"""
Split File Editor  (PySide6 / Qt)
---------------------------------
Left pane  : original file (read-only). Changed/removed lines are highlighted;
             click one to get "Undo change on line N" and restore just that line.
Right pane : editable copy, added/changed parts highlighted live.
Paging     : the file is shown X lines per page (X selectable in the toolbar).

Supports: .txt, .csv, .json, .xml  (add more in FORMATS below)
Unicode  : Bengali / Arabic / English / digits. Qt shapes complex scripts with
           HarfBuzz (correct Bengali conjuncts, Arabic joining and RTL order).
           Encoding picker, CRLF-preserving save.

Install  : pip install PySide6
           (Ubuntu, if Qt can't load the "xcb" plugin: sudo apt install libxcb-cursor0)
Run      : python split_editor.py [file]

Data model
----------
orig_lines     : original file as a list of lines (never changes)
edited_chunks  : one list of lines per page, in original-page coordinates.
                 Editing page k only touches edited_chunks[k], so a page's
                 left/right panes always line up regardless of other pages.
"""

import bisect
import codecs
import csv
import faulthandler
import io
import json
import re
import sys
import unicodedata
import xml.etree.ElementTree as ET
from difflib import SequenceMatcher

from PySide6.QtCore import QPoint, Qt, QTimer, Signal
from PySide6.QtGui import (QColor, QFont, QFontDatabase, QKeySequence, QShortcut,
                           QTextCharFormat, QTextCursor, QTextFormat)
from PySide6.QtWidgets import (QApplication, QCheckBox, QComboBox, QFileDialog, QFrame,
                               QHBoxLayout, QLabel, QLineEdit, QMainWindow, QMenu, QMessageBox,
                               QPlainTextEdit, QProgressDialog, QPushButton, QSizePolicy,
                               QSpinBox, QTextEdit, QVBoxLayout, QWidget)

# ----------------------------------------------------------------------------
# Format registry  (extension point #1: add a new file type here)
# Each validator takes the full text and returns a short status string,
# or raises an exception if the content is invalid for that format.
# ----------------------------------------------------------------------------


def _validate_text(text):
    return f"{len(text.splitlines())} lines"


class ValidationError(Exception):
    """A format error; line/col are 1-based positions in the full edited text (if known)."""

    def __init__(self, msg, line=None, col=None):
        super().__init__(msg)
        self.msg, self.line, self.col = msg, line, col

    def where(self):
        if self.line is None:
            return self.msg
        return f"line {self.line}, column {self.col}: {self.msg}"


def _validate_csv(text):
    reader = csv.reader(io.StringIO(text))
    rows = cols = 0
    try:
        for row in reader:
            rows += 1
            cols = max(cols, len(row))
    except csv.Error as exc:
        raise ValidationError(str(exc), reader.line_num, 1) from exc
    return f"{rows} rows, up to {cols} columns"


def _validate_json(text):
    try:
        json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValidationError(exc.msg, exc.lineno, exc.colno) from exc
    return "valid JSON"


def _validate_xml(text):
    try:
        ET.fromstring(text)
    except ET.ParseError as exc:
        line, col = getattr(exc, "position", (None, 0))
        msg = re.sub(r":? line \d+, column \d+$", "", str(exc))
        raise ValidationError(msg, line, col + 1) from exc
    return "valid XML"


FORMATS = {
    ".txt": ("Text", _validate_text),
    ".csv": ("CSV", _validate_csv),
    ".json": ("JSON", _validate_json),
    ".xml": ("XML", _validate_xml),
}

QT_FILTER = "Supported files (" + " ".join(f"*{e}" for e in FORMATS) + ");;All files (*)"

# First installed family wins (all cover Bengali; Qt falls back per-character
# for anything missing, e.g. Arabic). Changeable from the toolbar.
FONT_CANDIDATES = [
    "Hind Siliguri", "Noto Sans Bengali", "Nirmala UI", "Kalpurush", "SolaimanLipi",
    "Lohit Bengali", "Kohinoor Bangla", "Segoe UI", "Noto Sans", "DejaVu Sans",
]
# Appended after the chosen font so Arabic etc. fall back to a sensible font
# instead of whatever Qt happens to find first (only installed ones are used).
FALLBACK_FONTS = ["Noto Sans Bengali", "Noto Naskh Arabic", "Noto Sans Arabic", "Amiri",
                  "Segoe UI", "Nirmala UI", "DejaVu Sans", "Arial"]
PAGE_SIZES = ["25", "50", "100", "250", "500", "1000", "All"]
DEFAULT_PAGE_SIZE = 100

# ----------------------------------------------------------------------------
# Pure logic (no UI) -- easy to unit test and to extend
# ----------------------------------------------------------------------------


def split_lines(text):
    """Split on '\\n' only (keeps line endings), so it matches the editor's line numbering."""
    if not text:
        return []
    parts = text.split("\n")
    lines = [p + "\n" for p in parts[:-1]]
    if parts[-1]:
        lines.append(parts[-1])
    return lines


def _joins(prev, ch):
    """Does `ch` continue the letter (grapheme cluster) that ends with `prev`?"""
    return (
        unicodedata.category(ch) in ("Mn", "Mc", "Me")
        or ch in "\u200c\u200d"
        or prev == "\u200d"
        or unicodedata.combining(prev) == 9  # virama: joins the next consonant
    )


def _clusters(text):
    """
    Split text into user-perceived characters (simplified grapheme clusters), so
    highlights never cut inside a letter: Bengali conjuncts (ক্ষ), vowel signs
    (কি), anusvara/chandrabindu, Arabic harakat, ZWJ/ZWNJ sequences, etc.
    """
    out = []
    for ch in text:
        if out and _joins(out[-1][-1], ch):
            out[-1] += ch
        else:
            out.append(ch)
    return out


ENCODINGS = ["utf-8", "utf-8-sig", "utf-16", "utf-32", "cp1256", "cp1252", "latin-1"]


def detect_encoding(data):
    """BOM first, then strict UTF-8, else latin-1 (lossless fallback; user can pick another)."""
    if data.startswith((codecs.BOM_UTF32_LE, codecs.BOM_UTF32_BE)):
        return "utf-32"
    if data.startswith((codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)):
        return "utf-16"
    if data.startswith(codecs.BOM_UTF8):
        return "utf-8-sig"
    try:
        data.decode("utf-8")
        return "utf-8"
    except UnicodeDecodeError:
        return "latin-1"


def normalize_newlines(text):
    """Edit with '\\n' internally; remember the file's dominant line ending for saving."""
    crlf = text.count("\r\n")
    nl = "\r\n" if crlf and crlf >= text.count("\n") - crlf else "\n"
    return text.replace("\r\n", "\n").replace("\r", "\n"), nl


def _offsets(lines):
    out, pos = [], 0
    for ln in lines:
        out.append(pos)
        pos += len(ln)
    out.append(pos)
    return out


MAX_CHAR_DIFF = 20000  # blocks larger than this are highlighted whole


def compute_diff(a_lines, b_lines):
    """
    Diff two lists of lines (extension point #2: swap the algorithm here).
    Returns (line_opcodes, left_char_ranges, right_char_ranges).
    Char ranges are (start, end) offsets into "".join(a_lines) / "".join(b_lines).
    """
    ops = SequenceMatcher(None, a_lines, b_lines, autojunk=False).get_opcodes()
    a_off, b_off = _offsets(a_lines), _offsets(b_lines)
    left, right = [], []

    for tag, i1, i2, j1, j2 in ops:
        if tag == "equal":
            continue
        a0, a1 = a_off[i1], a_off[i2]
        b0, b1 = b_off[j1], b_off[j2]

        if tag == "delete":
            left.append((a0, a1))
        elif tag == "insert":
            right.append((b0, b1))
        else:  # replace -> refine at character level
            a_blk = "".join(a_lines[i1:i2])
            b_blk = "".join(b_lines[j1:j2])
            if len(a_blk) > MAX_CHAR_DIFF or len(b_blk) > MAX_CHAR_DIFF:
                left.append((a0, a1))
                right.append((b0, b1))
                continue
            a_cl, b_cl = _clusters(a_blk), _clusters(b_blk)
            ao, bo = _offsets(a_cl), _offsets(b_cl)
            for t, x1, x2, y1, y2 in SequenceMatcher(None, a_cl, b_cl, autojunk=False).get_opcodes():
                if t == "equal":
                    continue
                if x2 > x1:
                    left.append((a0 + ao[x1], a0 + ao[x2]))
                if y2 > y1:
                    right.append((b0 + bo[y1], b0 + bo[y2]))
    return ops, left, right


def restore_line(a, b, L):
    """
    Restore original line a[L] inside edited lines b.
    Returns the new list of edited lines, or None if line L is not changed.
      - deleted line  -> re-inserted where it was removed
      - modified line -> replaced by the original text
      - if L is the last original line of a modified block, any extra lines the
        edit added to that block are dropped (they replaced the original lines).
    """
    ops = SequenceMatcher(None, a, b, autojunk=False).get_opcodes()
    for tag, i1, i2, j1, j2 in ops:
        if tag == "equal" or not (i1 <= L < i2):
            continue
        b = list(b)
        if tag == "delete":
            b.insert(j1, a[L])
        else:  # replace
            k = L - i1
            if k < j2 - j1:
                b[j1 + k] = a[L]
            else:
                b.insert(j2, a[L])
            if L == i2 - 1:
                extra = (j2 - j1) - (i2 - i1)
                if extra > 0:
                    start = j1 + (i2 - i1)
                    del b[start:start + extra]
        return b
    return None


def _map_boundary(ops, p, n_b):
    """Map a boundary index p in list A to the matching boundary in list B."""
    for _tag, i1, _i2, j1, _j2 in ops:
        if i1 == p:
            return j1
    for _tag, i1, i2, j1, j2 in ops:
        if i1 < p < i2:
            return j1 + min(p - i1, j2 - j1)
    return n_b


def rechunk(orig_lines, edited_chunks, old_size, new_size):
    """
    Re-split the edited text for a new page size, keeping page boundaries
    anchored to original line numbers. Only chunks that contain a new boundary
    are diffed (cheap).
    """
    n = len(orig_lines)
    flat = [ln for c in edited_chunks for ln in c]
    total = len(flat)

    starts, pos = [], 0
    for c in edited_chunks:
        starts.append(pos)
        pos += len(c)

    ops_cache = {}

    def edited_boundary(p):
        if p <= 0:
            return 0
        if p >= n:
            return total
        k, q = divmod(p, old_size)
        if q == 0:
            return starts[k]
        if k not in ops_cache:
            a = orig_lines[k * old_size:(k + 1) * old_size]
            ops_cache[k] = SequenceMatcher(None, a, edited_chunks[k], autojunk=False).get_opcodes()
        return starts[k] + _map_boundary(ops_cache[k], q, len(edited_chunks[k]))

    bounds = [0]
    for p in range(new_size, n, new_size):
        bounds.append(max(bounds[-1], edited_boundary(p)))
    bounds.append(total)
    return [flat[bounds[i]:bounds[i + 1]] for i in range(len(bounds) - 1)]



# ----------------------------------------------------------------------------
# Find / replace engine (pure logic, no UI)
# ----------------------------------------------------------------------------

_WORD_CLASS = None


def _word_class():
    """
    Regex class for "word" characters: letters, digits, underscore AND all combining
    marks. Python's own word class leaves out marks such as Bengali vowel signs
    (া ি ু) and Arabic harakat, which would break "whole word" matching.
    """
    global _WORD_CLASS
    if _WORD_CLASS is None:
        spans, start = [], None
        for cp in range(0x10000):
            is_mark = unicodedata.category(chr(cp)) in ("Mn", "Mc", "Me")
            if is_mark and start is None:
                start = cp
            elif not is_mark and start is not None:
                spans.append((start, cp - 1))
                start = None
        if start is not None:
            spans.append((start, 0xFFFF))
        marks = "".join(f"\\u{a:04x}-\\u{b:04x}" for a, b in spans)
        _WORD_CLASS = "[\\w" + marks + "\\u200c\\u200d]"
    return _WORD_CLASS


def build_pattern(find, match_case=False, whole_word=False, use_regex=False):
    """Compile the user's token. Plain tokens are escaped; regex is used as typed."""
    if not find:
        raise ValueError("nothing to find")
    pat = find if use_regex else re.escape(find)
    if whole_word:
        w = _word_class()
        pat = f"(?<!{w})(?:{pat})(?!{w})"
    flags = (0 if match_case else re.IGNORECASE) | (re.MULTILINE if use_regex else 0)
    return re.compile(pat, flags)


def cluster_safe(text, s, e):
    """True if text[s:e] starts and ends on letter boundaries (cuts no Bengali/Arabic cluster)."""
    if s > 0 and _joins(text[s - 1], text[s]):
        return False
    if e < len(text) and _joins(text[e - 1], text[e]):
        return False
    return True


def scan(text, pat, safe=True):
    """-> ([(start, end), ...], skipped). `skipped` counts matches that would cut a letter."""
    out, skipped = [], 0
    for m in pat.finditer(text):
        s, e = m.span()
        if e == s:
            continue
        if safe and not cluster_safe(text, s, e):
            skipped += 1
            continue
        out.append((s, e))
    return out, skipped


def apply_replace(text, pat, repl, use_regex=False, safe=True):
    """Replace every (safe) match. Empty `repl` deletes. -> (new_text, replaced, skipped)"""
    done = skipped = 0

    def fn(m):
        nonlocal done, skipped
        if m.end() == m.start():
            return ""
        if safe and not cluster_safe(text, m.start(), m.end()):
            skipped += 1
            return m.group(0)
        done += 1
        return m.expand(repl) if use_regex else repl

    return pat.sub(fn, text), done, skipped


# ----------------------------------------------------------------------------
# UI
# ----------------------------------------------------------------------------

LEFT_CHAR_COLOR = "#ffb3b3"   # exact changed characters (original side)
LEFT_LINE_COLOR = "#ffe9e9"   # whole changed line (original side)
RIGHT_CHAR_COLOR = "#c8f0c8"  # added / changed characters (editable side)
FIND_COLOR = "#fff2a8"        # find matches on the current page
ERROR_LINE_COLOR = "#ffc9c9"  # line with a validation error (editable side)
ASTRAL_RE = re.compile("[\U00010000-\U0010ffff]")  # Qt positions count UTF-16 units


class PaneEdit(QPlainTextEdit):
    """Plain-text pane that reports which line the mouse is over / clicked."""

    lineClicked = Signal(int, QPoint)  # local 0-based line, global position
    lineHovered = Signal(int)          # -1 when not over a line

    def __init__(self, read_only):
        super().__init__()
        self.setLineWrapMode(QPlainTextEdit.NoWrap)
        self.setReadOnly(read_only)
        self.viewport().setMouseTracking(True)

    def line_at(self, pos):
        cur = self.cursorForPosition(pos)
        rect = self.cursorRect(cur)
        return cur.blockNumber() if rect.top() <= pos.y() <= rect.bottom() else -1

    def mousePressEvent(self, event):
        super().mousePressEvent(event)
        if event.button() == Qt.LeftButton:
            line = self.line_at(event.position().toPoint())
            if line >= 0:
                self.lineClicked.emit(line, event.globalPosition().toPoint())

    def mouseMoveEvent(self, event):
        super().mouseMoveEvent(event)
        self.lineHovered.emit(self.line_at(event.position().toPoint()))


class SplitEditor(QMainWindow):
    DEBOUNCE_MS = 150
    VALIDATE_AUTO_BYTES = 2_000_000  # larger files: validate on demand (Validate button)

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Split File Editor")
        self.resize(1400, 820)

        self.path = None
        self.loaded = False
        self.raw = b""
        self.encoding = "utf-8"
        self.newline = "\n"
        self.orig_lines = []
        self.edited_chunks = [[]]
        self.page = 0
        self.page_size = DEFAULT_PAGE_SIZE  # int, or None for "All"

        self._dirty = set()         # page numbers whose edited text differs from the original
        self._left_changed = set()  # local 0-based line numbers highlighted on the left
        self._syncing = False
        self._error_line = None     # (page, 1-based local line) of the last validation error
        self._bulk_history = []     # last few replace-all operations, for "Undo last bulk"

        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(self.DEBOUNCE_MS)
        self._timer.timeout.connect(self._refresh_diff)

        self._build_ui()
        QShortcut(QKeySequence("Ctrl+O"), self).activated.connect(self.open_file)
        QShortcut(QKeySequence("Ctrl+S"), self).activated.connect(self.save_file)
        for key in ("Ctrl+F", "Ctrl+H"):
            QShortcut(QKeySequence(key), self).activated.connect(self.show_find)
        QShortcut(QKeySequence("F3"), self).activated.connect(lambda: self._find_step())
        QShortcut(QKeySequence("Shift+F3"), self).activated.connect(lambda: self._find_step(backward=True))

    # ---- layout -----------------------------------------------------------

    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        root = QVBoxLayout(central)
        root.setContentsMargins(6, 4, 6, 2)

        def button(text, slot):
            b = QPushButton(text)
            b.clicked.connect(lambda _=False: slot())
            return b

        # row 1: file + paging
        row1 = QHBoxLayout()
        row1.addWidget(button("Open…", self.open_file))
        row1.addWidget(button("Save As…", self.save_file))
        row1.addWidget(button("Revert all", self.revert))
        row1.addWidget(button("Validate", self.validate))
        row1.addSpacing(14)
        row1.addWidget(QLabel("Lines per page:"))
        self.size_box = QComboBox()
        self.size_box.setEditable(True)
        self.size_box.addItems(PAGE_SIZES)
        self.size_box.setCurrentText(str(DEFAULT_PAGE_SIZE))
        self.size_box.setFixedWidth(80)
        self.size_box.activated.connect(self._on_size_change)
        self.size_box.lineEdit().returnPressed.connect(self._on_size_change)
        row1.addWidget(self.size_box)
        self.prev_btn = button("◀ Prev", lambda: self._goto(self.page - 1))
        self.next_btn = button("Next ▶", lambda: self._goto(self.page + 1))
        row1.addWidget(self.prev_btn)
        row1.addWidget(self.next_btn)
        self.page_label = QLabel("")
        row1.addWidget(self.page_label)
        self.file_label = QLabel("No file loaded")
        self.file_label.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        row1.addWidget(self.file_label, 1)
        root.addLayout(row1)

        # row 2: encoding + font
        row2 = QHBoxLayout()
        row2.addWidget(QLabel("Encoding:"))
        self.enc_box = QComboBox()
        self.enc_box.setEditable(True)
        self.enc_box.addItems(ENCODINGS)
        self.enc_box.setCurrentText(self.encoding)
        self.enc_box.setFixedWidth(110)
        self.enc_box.activated.connect(self._on_encoding_change)
        self.enc_box.lineEdit().returnPressed.connect(self._on_encoding_change)
        row2.addWidget(self.enc_box)
        row2.addSpacing(14)
        row2.addWidget(QLabel("Font:"))
        # Plain list of Bengali-capable families (a QFontComboBox would load a
        # preview of EVERY installed font, which can crash on broken fonts).
        self.font_box = QComboBox()
        bn = sorted(set(QFontDatabase.families(QFontDatabase.WritingSystem.Bengali)))
        self.font_box.addItems(bn or sorted(set(QFontDatabase.families())))
        self.font_box.setFixedWidth(240)
        row2.addWidget(self.font_box)
        self.fsize = QSpinBox()
        self.fsize.setRange(6, 48)
        self.fsize.setValue(13)
        row2.addWidget(self.fsize)
        row2.addSpacing(14)
        row2.addWidget(button("Find / Replace (Ctrl+F)", self.toggle_find))
        row2.addStretch(1)
        root.addLayout(row2)
        self._build_find_panel(root)

        # panes: two equal columns -> window is always split exactly in half
        self.left = PaneEdit(read_only=True)
        self.right = PaneEdit(read_only=False)
        self.left.setStyleSheet("QPlainTextEdit { background: #f6f6f6; }")
        self.right.setUndoRedoEnabled(True)
        panes = QHBoxLayout()
        for title, edit in (("ORIGINAL (read-only) — click a highlighted line to undo it", self.left),
                            ("EDITABLE", self.right)):
            col = QVBoxLayout()
            lbl = QLabel(title)
            lbl.setAlignment(Qt.AlignCenter)
            col.addWidget(lbl)
            col.addWidget(edit)
            panes.addLayout(col, 1)
        root.addLayout(panes, 1)

        self.status = QLabel("Open a file to begin.")
        self.statusBar().addWidget(self.status, 1)

        # fonts
        fams = set(QFontDatabase.families())
        fam = next((f for f in FONT_CANDIDATES if f in fams), None)
        if fam:
            if self.font_box.findText(fam) < 0:
                self.font_box.addItem(fam)
            self.font_box.setCurrentText(fam)
        self._apply_font()
        self.font_box.currentTextChanged.connect(self._apply_font)
        self.fsize.valueChanged.connect(self._apply_font)

        # behaviour
        self.right.document().contentsChanged.connect(self._on_modified)
        self.left.lineClicked.connect(self._on_left_click)
        self.left.lineHovered.connect(self._on_left_hover)
        for a, b in ((self.left, self.right), (self.right, self.left)):
            a.verticalScrollBar().valueChanged.connect(self._make_scroll_sync(b))

    def _make_scroll_sync(self, dst):
        """Both panes show the same top line (scrollbar units are lines)."""
        def sync(value):
            if self._syncing:
                return
            self._syncing = True
            dst.verticalScrollBar().setValue(value)
            self._syncing = False
        return sync

    def _apply_font(self, *_):
        primary = self.font_box.currentText()
        installed = set(QFontDatabase.families())
        font = QFont()
        if primary:
            font.setFamilies([primary] + [f for f in FALLBACK_FONTS if f in installed and f != primary])
        font.setPointSize(self.fsize.value())
        self.left.setFont(font)
        self.right.setFont(font)

    # ---- paging helpers ---------------------------------------------------

    def _eff(self, size="current"):
        """Effective lines-per-page (a number even when 'All' = None)."""
        size = self.page_size if size == "current" else size
        return size or max(len(self.orig_lines), 1)

    def _n_pages(self, size="current"):
        return max(1, -(-len(self.orig_lines) // self._eff(size)))

    def _orig_chunk(self, k):
        eff = self._eff()
        return self.orig_lines[k * eff:(k + 1) * eff]

    def _page_start(self):
        return self.page * self._eff()

    def _goto(self, page):
        if not self.loaded:
            return
        self._sync_model()
        page = max(0, min(page, self._n_pages() - 1))
        if page != self.page:
            self.page = page
            self._render_page()

    def _on_size_change(self, *_):
        txt = self.size_box.currentText().strip()
        try:
            new = None if txt.lower() == "all" else int(txt)
            if new is not None and new < 1:
                raise ValueError
        except ValueError:
            QMessageBox.warning(self, "Lines per page", "Enter a positive number or 'All'.")
            self.size_box.setCurrentText("All" if self.page_size is None else str(self.page_size))
            return

        if new == self.page_size:
            return
        if not self.loaded:
            self.page_size = new
            return

        self._sync_model()
        old_eff = self._eff()
        first_line = self.page * old_eff
        new_eff = self._eff(new)

        self.edited_chunks = rechunk(self.orig_lines, self.edited_chunks, old_eff, new_eff)
        self.page_size = new
        self.page = min(first_line // new_eff, self._n_pages() - 1)
        self._dirty = {k for k, c in enumerate(self.edited_chunks) if c != self._orig_chunk(k)}
        self._bulk_history = []
        self._render_page()

    # ---- encoding ---------------------------------------------------------

    def _on_encoding_change(self, *_):
        enc = self.enc_box.currentText().strip()
        try:
            codecs.lookup(enc)
        except LookupError:
            QMessageBox.warning(self, "Encoding", f"Unknown encoding: {enc}")
            self.enc_box.setCurrentText(self.encoding)
            return
        if enc == self.encoding:
            return
        if not self.loaded:
            self.encoding = enc
            return
        self._sync_model()
        if self._dirty and QMessageBox.question(
            self, "Change encoding",
            "Re-reading the file with another encoding discards your edits. Continue?",
        ) != QMessageBox.Yes:
            self.enc_box.setCurrentText(self.encoding)
            return
        self._decode_and_load(enc)

    # ---- file handling ----------------------------------------------------

    def open_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open file", "", QT_FILTER)
        if path:
            self.load_path(path)

    def load_path(self, path):
        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as exc:
            QMessageBox.critical(self, "Open failed", str(exc))
            return
        self.path, self.raw = path, data
        self.file_label.setText(path)
        self._decode_and_load(detect_encoding(data))

    def _decode_and_load(self, enc):
        try:
            text = self.raw.decode(enc)
        except (UnicodeError, LookupError) as exc:
            QMessageBox.critical(self, "Decode failed", f"Cannot read this file as {enc}:\n{exc}")
            self.enc_box.setCurrentText(self.encoding)
            return
        text, self.newline = normalize_newlines(text)
        if "\u2028" in text or "\u2029" in text:
            QMessageBox.warning(
                self, "Special line separators",
                "This file contains Unicode line/paragraph separators (U+2028/U+2029).\n"
                "The editor shows them as normal line breaks, so edited pages will save them as '\\n'.",
            )
        self.encoding = enc
        self.enc_box.setCurrentText(enc)
        self.orig_lines = split_lines(text)
        self.loaded = True
        self.page = 0
        self.edited_chunks = [list(self._orig_chunk(k)) for k in range(self._n_pages())]
        self._dirty = set()
        self._bulk_history = []
        self._render_page()

    def revert(self):
        if not self.loaded:
            return
        self._sync_model()
        if self._dirty and QMessageBox.question(
            self, "Revert all", "Discard all edits on every page and restore the original?"
        ) != QMessageBox.Yes:
            return
        self.edited_chunks = [list(self._orig_chunk(k)) for k in range(self._n_pages())]
        self._dirty = set()
        self._bulk_history = []
        self._render_page()

    def save_file(self):
        if not self.loaded:
            return
        fmt, _info, err = self._run_validation()  # also syncs the right pane into the model
        if err is not None:
            box = QMessageBox(self)
            box.setIcon(QMessageBox.Warning)
            box.setWindowTitle("Validation failed")
            box.setText(f"The edited {fmt} is not valid:\n{err.where()}")
            go = box.addButton("Go to error", QMessageBox.AcceptRole)
            anyway = box.addButton("Save anyway", QMessageBox.DestructiveRole)
            box.addButton(QMessageBox.Cancel)
            box.setDefaultButton(go)
            box.exec()
            if box.clickedButton() is go:
                self._goto_error(err)
                return
            if box.clickedButton() is not anyway:
                return
        name = self.path.replace("\\", "/").rsplit("/", 1)[-1]
        out, _ = QFileDialog.getSaveFileName(self, "Save As", name, QT_FILTER)
        if not out:
            return
        text = self._full_edited_text().replace("\n", self.newline)
        enc = self.encoding
        try:
            data = text.encode(enc)
        except UnicodeEncodeError:
            if QMessageBox.question(
                self, "Encoding", f"Some characters can't be stored as {enc}.\nSave as UTF-8 instead?"
            ) != QMessageBox.Yes:
                return
            enc, data = "utf-8", text.encode("utf-8")
        try:
            with open(out, "wb") as f:
                f.write(data)
        except Exception as exc:
            QMessageBox.critical(self, "Save failed", str(exc))
            return
        self._set_status(f"Saved to {out} ({enc})")

    def _format_info(self):
        ext = "." + self.path.rsplit(".", 1)[-1].lower() if "." in self.path else ""
        return FORMATS.get(ext, ("Text", _validate_text))

    def _set_status(self, text, error=False):
        self.status.setStyleSheet("color: #b00020;" if error else "")
        self.status.setText(text)

    def _run_validation(self):
        """Validate the WHOLE edited file. -> (format name, info, error or None)."""
        self._sync_model()
        name, validator = self._format_info()
        text = self._full_edited_text()
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            return name, validator(text), None
        except ValidationError as exc:
            return name, None, exc
        except Exception as exc:  # e.g. RecursionError on absurdly nested JSON
            return name, None, ValidationError(str(exc) or type(exc).__name__)
        finally:
            QApplication.restoreOverrideCursor()

    def _goto_error(self, err):
        """Show the error: right page, cursor on the line/column, tinted line, focus."""
        self._sync_model()
        if err.line is None:
            self._set_status(f"✖ {err.msg}", error=True)
            return
        acc, past_end = 0, True
        for k, c in enumerate(self.edited_chunks):
            if err.line <= acc + len(c):
                past_end = False
                break
            acc += len(c)
        if k != self.page:
            self.page = k
            self._render_page()
        doc = self.right.document()
        blk = doc.lastBlock() if past_end else doc.findBlockByNumber(err.line - acc - 1)
        if not blk.isValid():
            blk = doc.lastBlock()
        text = blk.text()
        col = len(text) if past_end else max(0, min((err.col or 1) - 1, len(text)))
        pos = blk.position() + col + sum(1 for _ in ASTRAL_RE.finditer(text, 0, col))
        cur = QTextCursor(doc)
        cur.setPosition(pos)
        self.right.setTextCursor(cur)
        self._error_line = (self.page, blk.blockNumber() + 1)
        self._refresh_diff()
        self.right.centerCursor()
        self.right.setFocus()
        self._set_status(f"✖ {err.where()}", error=True)

    def validate(self):
        if not self.loaded:
            return
        name, info, err = self._run_validation()
        if err is None:
            self._set_status(f"✔ {name}: {info}")
            QMessageBox.information(self, "Validate", f"{name}: {info}")
        else:
            self._goto_error(err)

    # ---- text helpers -----------------------------------------------------

    def _full_edited_text(self):
        return "".join(ln for c in self.edited_chunks for ln in c)

    def _sync_model(self):
        """Pull what is currently in the right pane into the model."""
        self._timer.stop()
        if not self.loaded:
            return
        chunk = split_lines(self.right.toPlainText())
        self.edited_chunks[self.page] = chunk
        if chunk == self._orig_chunk(self.page):
            self._dirty.discard(self.page)
        else:
            self._dirty.add(self.page)

    def _render_page(self):
        """Load the current page into both panes (resets typing-undo history)."""
        self._error_line = None
        a = self._orig_chunk(self.page)
        b = self.edited_chunks[self.page]

        self.right.document().contentsChanged.disconnect(self._on_modified)
        self.left.setPlainText("".join(a))
        self.right.setPlainText("".join(b))
        self.right.document().clearUndoRedoStacks()
        self.right.document().contentsChanged.connect(self._on_modified)
        self.left.verticalScrollBar().setValue(0)
        self.right.verticalScrollBar().setValue(0)

        n, eff = len(self.orig_lines), self._eff()
        pages = self._n_pages()
        if n:
            lo, hi = self.page * eff + 1, min((self.page + 1) * eff, n)
            self.page_label.setText(f"Page {self.page + 1}/{pages}  (lines {lo}–{hi} of {n})")
        else:
            self.page_label.setText("Page 1/1  (empty file)")
        self.prev_btn.setEnabled(self.page > 0)
        self.next_btn.setEnabled(self.page < pages - 1)

        self._update_scope_label()
        self._update_bulk_ui()
        self._refresh_diff()

    def _replace_right(self, text):
        """Swap the right pane's content as ONE undoable step (Ctrl+Z works)."""
        scroll = self.right.verticalScrollBar().value()
        cur = QTextCursor(self.right.document())
        cur.beginEditBlock()
        cur.select(QTextCursor.Document)
        cur.insertText(text)
        cur.endEditBlock()
        self.right.verticalScrollBar().setValue(scroll)

    # ---- live diff --------------------------------------------------------

    def _on_modified(self):
        self._timer.start()

    @staticmethod
    def _selection(doc, start, end, color, full_width=False):
        cur = QTextCursor(doc)
        cur.setPosition(start)
        if end > start:
            cur.setPosition(end, QTextCursor.KeepAnchor)
        fmt = QTextCharFormat()
        fmt.setBackground(QColor(color))
        if full_width:
            fmt.setProperty(QTextFormat.FullWidthSelection, True)
        sel = QTextEdit.ExtraSelection()
        sel.cursor = cur
        sel.format = fmt
        return sel

    def _range_selections(self, edit, text, ranges, color):
        """Char ranges (code points) -> selections (Qt counts UTF-16 units)."""
        astral = [m.start() for m in ASTRAL_RE.finditer(text)]

        def pos(off):
            return off + bisect.bisect_left(astral, off)

        doc = edit.document()
        return [self._selection(doc, pos(s), pos(e), color) for s, e in ranges]

    def _refresh_diff(self):
        if not self.loaded:
            return
        self._sync_model()
        a = self._orig_chunk(self.page)
        b = self.edited_chunks[self.page]
        ops, left_r, right_r = compute_diff(a, b)

        ldoc = self.left.document()
        left_sel = []
        self._left_changed = set()
        for tag, i1, i2, _j1, _j2 in ops:
            if tag != "equal" and i2 > i1:
                for ln in range(i1, i2):
                    blk = ldoc.findBlockByNumber(ln)
                    if blk.isValid():
                        left_sel.append(self._selection(ldoc, blk.position(), blk.position(),
                                                        LEFT_LINE_COLOR, full_width=True))
                    self._left_changed.add(ln)
        left_sel += self._range_selections(self.left, "".join(a), left_r, LEFT_CHAR_COLOR)
        b_text = "".join(b)
        right_sel = []
        if self._error_line and self._error_line[0] == self.page:
            rdoc = self.right.document()
            blk = rdoc.findBlockByNumber(self._error_line[1] - 1)
            if blk.isValid():
                right_sel.append(self._selection(rdoc, blk.position(), blk.position(),
                                                 ERROR_LINE_COLOR, full_width=True))
        right_sel += self._range_selections(self.right, b_text, right_r, RIGHT_CHAR_COLOR)
        right_sel += self._find_selections(b_text)

        self.left.setExtraSelections(left_sel)
        self.right.setExtraSelections(right_sel)
        self._update_status(len(left_r) + len(right_r))

    def _update_status(self, page_regions):
        name, validator = self._format_info()
        bad = False
        if len(self.raw) <= self.VALIDATE_AUTO_BYTES:
            try:
                info = validator(self._full_edited_text())
            except ValidationError as exc:
                info, bad = f"INVALID — {exc.where()}", True
            except Exception as exc:
                info, bad = f"INVALID — {exc}", True
        else:
            info = "not validated (large file — click Validate)"
        hint = "  [not UTF-8: if text looks garbled, pick another Encoding]" if self.encoding in (
            "latin-1", "cp1252") else ""
        self._set_status(
            f"{name} ({self.encoding}) | {info} | this page: {page_regions} changed region(s) | "
            f"pages modified: {len(self._dirty)}/{self._n_pages()}{hint}",
            error=bad,
        )

    # ---- find / replace / bulk delete -------------------------------------

    def _build_find_panel(self, root):
        self.find_panel = QFrame()
        self.find_panel.setFrameShape(QFrame.StyledPanel)
        lay = QVBoxLayout(self.find_panel)
        lay.setContentsMargins(6, 4, 6, 4)

        def mk(text, slot, tip=""):
            b = QPushButton(text)
            b.clicked.connect(lambda _=False: slot())
            if tip:
                b.setToolTip(tip)
            return b

        r1 = QHBoxLayout()
        r1.addWidget(QLabel("Find:"))
        self.find_edit = QLineEdit()
        self.find_edit.setPlaceholderText("token to find / remove")
        r1.addWidget(self.find_edit, 2)
        r1.addWidget(QLabel("Replace with:"))
        self.repl_edit = QLineEdit()
        self.repl_edit.setPlaceholderText("(empty = delete)")
        r1.addWidget(self.repl_edit, 2)
        self.opt_case = QCheckBox("Match case")
        self.opt_word = QCheckBox("Whole word")
        self.opt_regex = QCheckBox("Regex")
        self.opt_safe = QCheckBox("Keep letters intact")
        self.opt_safe.setChecked(True)
        self.opt_safe.setToolTip(
            "Skip matches that would cut a Bengali/Arabic letter in half,\n"
            "e.g. removing 'ব' from 'বা', or 'ক' from 'কি' / 'ক্ষ'.\n"
            "Untick to remove such matches too (e.g. to strip ZWJ/ZWNJ).")
        for cb in (self.opt_case, self.opt_word, self.opt_regex, self.opt_safe):
            r1.addWidget(cb)
            cb.toggled.connect(self._on_find_changed)
        lay.addLayout(r1)

        r2 = QHBoxLayout()
        r2.addWidget(QLabel("Scope:"))
        self.scope_box = QComboBox()
        self.scope_box.addItems(["This page", "Group of pages", "Whole file"])
        r2.addWidget(self.scope_box)
        self.group_spin = QSpinBox()
        self.group_spin.setRange(2, 1_000_000)
        self.group_spin.setValue(10)
        self.group_spin.setPrefix("pages per group: ")
        self.group_spin.setToolTip("Pages are grouped 1–N, N+1–2N, … ; the scope is the group containing the current page.")
        r2.addWidget(self.group_spin)
        self.scope_label = QLabel("")
        r2.addWidget(self.scope_label)
        r2.addSpacing(12)
        r2.addWidget(mk("◀ Find", lambda: self._find_step(backward=True), "Previous match (Shift+F3)"))
        r2.addWidget(mk("Find ▶", self._find_step, "Next match (F3 / Enter)"))
        r2.addWidget(mk("Replace", self._replace_one, "Replace the selected match, then find the next"))
        r2.addWidget(mk("Replace All", self.replace_all, "Replace every match in the scope (empty 'Replace with' deletes)"))
        r2.addWidget(mk("Delete All", self.delete_all, "Delete every match in the scope (ignores 'Replace with')"))
        r2.addWidget(mk("Count", self.count_matches, "Count matches in the scope"))
        self.undo_bulk_btn = mk("Undo last bulk", self.undo_bulk, "Undo the last Replace All / Delete All")
        r2.addWidget(self.undo_bulk_btn)
        r2.addStretch(1)
        lay.addLayout(r2)

        r3 = QHBoxLayout()
        self.find_count = QLabel("")
        self.find_msg = QLabel("")
        r3.addWidget(self.find_count)
        r3.addWidget(self.find_msg, 1)
        lay.addLayout(r3)
        root.addWidget(self.find_panel)

        self.find_edit.textChanged.connect(self._on_find_changed)
        self.find_edit.returnPressed.connect(lambda: self._find_step())
        self.repl_edit.returnPressed.connect(self._replace_one)
        self.scope_box.currentIndexChanged.connect(self._update_scope_label)
        self.group_spin.valueChanged.connect(self._update_scope_label)
        self._update_bulk_ui()

    def toggle_find(self):
        if self.find_panel.isHidden():
            self.show_find()
        else:
            self.find_panel.hide()
            self._timer.start()

    def show_find(self):
        self.find_panel.show()
        self.find_edit.setFocus()
        self.find_edit.selectAll()
        self._timer.start()

    def _on_find_changed(self, *_):
        self.find_msg.setText("")
        self._timer.start()  # re-highlights matches on this page

    def _note(self, text, error=False):
        self.find_msg.setStyleSheet("color: #b00020;" if error else "color: #1b5e20;")
        self.find_msg.setText(text)

    def _update_bulk_ui(self):
        self.undo_bulk_btn.setEnabled(bool(self._bulk_history))

    def _scope_pages(self):
        i = self.scope_box.currentIndex()
        n = self._n_pages()
        if i == 0:
            return range(self.page, self.page + 1)
        if i == 1:
            size = self.group_spin.value()
            lo = (self.page // size) * size
            return range(lo, min(lo + size, n))
        return range(n)

    def _update_scope_label(self, *_):
        i = self.scope_box.currentIndex()
        self.group_spin.setEnabled(i == 1)
        if not self.loaded:
            self.scope_label.setText("")
            return
        pages = self._scope_pages()
        n = self._n_pages()
        if i == 0:
            text = f"page {self.page + 1}"
        elif i == 1:
            text = f"pages {pages.start + 1}–{pages.stop} of {n}"
        else:
            text = f"all {n} pages"
        self.scope_label.setText(f"({text})")

    def _pattern(self, quiet=False):
        find = self.find_edit.text()
        if not find:
            if not quiet:
                self._note("Type a token to find.", error=True)
            return None
        try:
            pat = build_pattern(find, self.opt_case.isChecked(), self.opt_word.isChecked(),
                                self.opt_regex.isChecked())
            if self.opt_regex.isChecked() and pat.search(""):
                raise re.error("pattern matches empty text")
        except re.error as exc:
            if not quiet:
                self._note(f"Invalid regex: {exc}", error=True)
            return None
        return pat

    def _check_repl(self, pat, repl):
        if not self.opt_regex.isChecked():
            return True
        try:
            pat.sub(repl, "")  # validates group references like \1
        except (re.error, IndexError) as exc:
            self._note(f"Bad replacement: {exc}", error=True)
            return False
        return True

    def _find_selections(self, text):
        """Yellow highlights for matches on the current page (+ live count)."""
        pat = None if self.find_panel.isHidden() else self._pattern(quiet=True)
        if pat is None:
            self.find_count.setText("")
            return []
        matches, skipped = scan(text, pat, self.opt_safe.isChecked())
        extra = f", {skipped} skipped inside letters" if skipped else ""
        self.find_count.setText(f"{len(matches)} match(es) on this page{extra}")
        return self._range_selections(self.right, text, matches[:2000], FIND_COLOR)

    def _run_pages(self, pages, work, label):
        """Call work(k) per page; progress + Cancel when there are many pages."""
        n = len(pages)
        dlg = None
        if n > 300:
            dlg = QProgressDialog(label, "Cancel", 0, n, self)
            dlg.setWindowModality(Qt.WindowModal)
            dlg.setMinimumDuration(300)
        for i, k in enumerate(pages):
            if dlg is not None and i % 200 == 0:
                dlg.setValue(i)
                QApplication.processEvents()
                if dlg.wasCanceled():
                    return False
            work(k)
        if dlg is not None:
            dlg.setValue(n)
        return True

    # -- single match navigation / replace

    def _cp_to_pos(self, text, off):
        return off + sum(1 for _ in ASTRAL_RE.finditer(text, 0, off))

    def _pos_to_cp(self, text, pos16):
        k = 0
        for m in ASTRAL_RE.finditer(text):
            if m.start() + k + 2 <= pos16:
                k += 1
            else:
                break
        return pos16 - k

    def _select_range(self, s, e):
        text = self.right.toPlainText()
        cur = self.right.textCursor()
        cur.setPosition(self._cp_to_pos(text, s))
        cur.setPosition(self._cp_to_pos(text, e), QTextCursor.KeepAnchor)
        self.right.setTextCursor(cur)
        self.right.ensureCursorVisible()

    def _find_step(self, backward=False, keep_note=False):
        if not self.loaded:
            return False
        pat = self._pattern()
        if pat is None:
            return False
        if not keep_note:
            self._note("")
        safe = self.opt_safe.isChecked()
        self._sync_model()
        text = self.right.toPlainText()
        cur = self.right.textCursor()
        cp = self._pos_to_cp(text, cur.selectionStart() if backward else cur.selectionEnd())
        here, _ = scan(text, pat, safe)
        if backward:
            cand = [m for m in here if m[1] <= cp]
            hit = cand[-1] if cand else None
        else:
            cand = [m for m in here if m[0] >= cp]
            hit = cand[0] if cand else None
        if hit:
            self._select_range(*hit)
            return True

        pages = list(self._scope_pages())
        if backward:
            order = [k for k in reversed(pages) if k < self.page] + [k for k in reversed(pages) if k > self.page]
        else:
            order = [k for k in pages if k > self.page] + [k for k in pages if k < self.page]
        found = {}

        def work(k):
            if not found:
                ms, _ = scan("".join(self.edited_chunks[k]), pat, safe)
                if ms:
                    found["k"], found["m"] = k, (ms[-1] if backward else ms[0])

        # stop at the first page with a match; the progress dialog only matters on huge scopes
        for k in order:
            work(k)
            if found:
                break
        if found:
            self._goto(found["k"])
            self._select_range(*found["m"])
            return True
        if here:
            self._select_range(*(here[-1] if backward else here[0]))
            self._note("Wrapped around.")
            return True
        if keep_note:  # e.g. right after "Replaced 1 match."
            self.find_msg.setText(self.find_msg.text() + " No more matches in scope.")
        else:
            self._note("No matches in scope.", error=True)
        return False

    def _replace_one(self):
        if not self.loaded:
            return
        pat = self._pattern()
        if pat is None:
            return
        repl = self.repl_edit.text()
        if not self._check_repl(pat, repl):
            return
        cur = self.right.textCursor()
        if cur.hasSelection():
            m = pat.fullmatch(cur.selectedText().replace("\u2029", "\n"))
            if m:
                cur.insertText(m.expand(repl) if self.opt_regex.isChecked() else repl)
                self.right.setTextCursor(cur)
                self._note("Replaced 1 match.")
                self._find_step(keep_note=True)
                return
        self._find_step()

    # -- bulk operations

    def count_matches(self):
        if not self.loaded:
            return
        pat = self._pattern()
        if pat is None:
            return
        self._sync_model()
        safe = self.opt_safe.isChecked()
        tot = [0, 0, 0]  # matches, pages with matches, skipped

        def work(k):
            ms, sk = scan("".join(self.edited_chunks[k]), pat, safe)
            tot[0] += len(ms)
            tot[1] += 1 if ms else 0
            tot[2] += sk

        pages = self._scope_pages()
        if not self._run_pages(pages, work, "Counting matches…"):
            self._note("Cancelled.", error=True)
            return
        extra = f"; {tot[2]} skipped inside letters" if tot[2] else ""
        self._note(f"{tot[0]} match(es) in {tot[1]} of {len(pages)} page(s){extra}.")

    def replace_all(self):
        self._bulk_replace(self.repl_edit.text(), "Replaced")

    def delete_all(self):
        self._bulk_replace("", "Deleted")

    def _bulk_replace(self, repl, verb):
        if not self.loaded:
            return
        pat = self._pattern()
        if pat is None or not self._check_repl(pat, repl):
            return
        regex, safe = self.opt_regex.isChecked(), self.opt_safe.isChecked()
        self._sync_model()
        changes, stats = {}, [0, 0]  # page -> new chunk; [replaced, skipped]

        def work(k):
            new, n, sk = apply_replace("".join(self.edited_chunks[k]), pat, repl, regex, safe)
            stats[1] += sk
            if n:
                changes[k] = split_lines(new)
                stats[0] += n

        pages = self._scope_pages()
        if not self._run_pages(pages, work, f"{verb}…"):
            self._note("Cancelled — nothing was changed.", error=True)
            return
        hint = (f" ({stats[1]} skipped inside letters — untick 'Keep letters intact' to include them)"
                if stats[1] else "")
        if not changes:
            self._note("No matches to change." + hint, error=bool(stats[1]))
            return
        self._apply_bulk(changes)
        self._note(f"{verb} {stats[0]} match(es) in {len(changes)} page(s).{hint}")

    def _apply_bulk(self, changes):
        undo = {}
        for k, new in changes.items():
            undo[k] = (self.edited_chunks[k], new)
            self.edited_chunks[k] = new
            if new == self._orig_chunk(k):
                self._dirty.discard(k)
            else:
                self._dirty.add(k)
        self._bulk_history.append(undo)
        del self._bulk_history[:-5]  # keep the last 5 operations
        if self.page in changes:
            self._replace_right("".join(changes[self.page]))  # also one Ctrl+Z step
        self._refresh_diff()
        self._update_bulk_ui()

    def undo_bulk(self):
        if not self._bulk_history:
            return
        self._sync_model()
        op = self._bulk_history.pop()
        restored = skipped = 0
        for k, (old, new) in op.items():
            if self.edited_chunks[k] == new:  # untouched since the bulk op
                self.edited_chunks[k] = old
                if old == self._orig_chunk(k):
                    self._dirty.discard(k)
                else:
                    self._dirty.add(k)
                restored += 1
            else:
                skipped += 1
        if self.page in op and self.edited_chunks[self.page] == op[self.page][0]:
            self._replace_right("".join(self.edited_chunks[self.page]))
        self._refresh_diff()
        self._update_bulk_ui()
        extra = f" ({skipped} page(s) skipped: edited since)" if skipped else ""
        self._note(f"Undid last bulk operation on {restored} page(s).{extra}", error=bool(skipped))

    # ---- click-to-undo on the left pane ----------------------------------

    def _on_left_hover(self, line):
        cursor = Qt.PointingHandCursor if line in self._left_changed else Qt.IBeamCursor
        self.left.viewport().setCursor(cursor)

    def _on_left_click(self, line, global_pos):
        if line in self._left_changed:
            QTimer.singleShot(0, lambda: self._popup(line, global_pos))

    def _popup(self, line, global_pos):
        menu = QMenu(self)
        act = menu.addAction(f"Undo change on line {self._page_start() + line + 1}")
        if menu.exec(global_pos) is act:
            self._undo_line(line)

    def _undo_line(self, line):
        self._sync_model()
        new_b = restore_line(self._orig_chunk(self.page), self.edited_chunks[self.page], line)
        if new_b is None:
            return
        self.edited_chunks[self.page] = new_b
        self._replace_right("".join(new_b))
        self._refresh_diff()


def main():
    faulthandler.enable()  # a native crash now prints the Python stack
    app = QApplication(sys.argv)
    win = SplitEditor()
    win.show()
    args = app.arguments()[1:]
    if args:
        win.load_path(args[0])
    sys.exit(app.exec())


if __name__ == "__main__":
    main()