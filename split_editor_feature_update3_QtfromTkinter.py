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
from PySide6.QtWidgets import (QApplication, QComboBox, QFileDialog, QFontComboBox, QHBoxLayout,
                               QLabel, QMainWindow, QMenu, QMessageBox, QPlainTextEdit,
                               QPushButton, QSizePolicy, QSpinBox, QTextEdit, QVBoxLayout, QWidget)

# ----------------------------------------------------------------------------
# Format registry  (extension point #1: add a new file type here)
# Each validator takes the full text and returns a short status string,
# or raises an exception if the content is invalid for that format.
# ----------------------------------------------------------------------------


def _validate_text(text):
    return f"{len(text.splitlines())} lines"


def _validate_csv(text):
    rows = list(csv.reader(io.StringIO(text)))
    cols = max((len(r) for r in rows), default=0)
    return f"{len(rows)} rows, up to {cols} columns"


def _validate_json(text):
    json.loads(text)
    return "valid JSON"


def _validate_xml(text):
    ET.fromstring(text)
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


def _clusters(text):
    """
    Split text into user-perceived characters (simplified grapheme clusters), so
    highlights never cut inside a letter: Bengali conjuncts (ক্ষ), vowel signs
    (কি), anusvara/chandrabindu, Arabic harakat, ZWJ/ZWNJ sequences, etc.
    """
    out = []
    for ch in text:
        if out:
            prev = out[-1][-1]
            if (
                unicodedata.category(ch) in ("Mn", "Mc", "Me")
                or ch in "\u200c\u200d"
                or prev == "\u200d"
                or unicodedata.combining(prev) == 9  # virama: joins the next consonant
            ):
                out[-1] += ch
                continue
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
# UI
# ----------------------------------------------------------------------------

LEFT_CHAR_COLOR = "#ffb3b3"   # exact changed characters (original side)
LEFT_LINE_COLOR = "#ffe9e9"   # whole changed line (original side)
RIGHT_CHAR_COLOR = "#c8f0c8"  # added / changed characters (editable side)
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

        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(self.DEBOUNCE_MS)
        self._timer.timeout.connect(self._refresh_diff)

        self._build_ui()
        QShortcut(QKeySequence("Ctrl+O"), self).activated.connect(self.open_file)
        QShortcut(QKeySequence("Ctrl+S"), self).activated.connect(self.save_file)

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
        self.font_box = QFontComboBox()
        self.font_box.setFixedWidth(240)
        row2.addWidget(self.font_box)
        self.fsize = QSpinBox()
        self.fsize.setRange(6, 48)
        self.fsize.setValue(13)
        row2.addWidget(self.fsize)
        row2.addStretch(1)
        root.addLayout(row2)

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
            self.font_box.setCurrentFont(QFont(fam))
        self._apply_font()
        self.font_box.currentFontChanged.connect(self._apply_font)
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
        font = QFont(self.font_box.currentFont())
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
        self._render_page()

    def save_file(self):
        if not self.loaded:
            return
        self._sync_model()
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
        self.status.setText(f"Saved to {out} ({enc})")

    def _format_info(self):
        ext = "." + self.path.rsplit(".", 1)[-1].lower() if "." in self.path else ""
        return FORMATS.get(ext, ("Text", _validate_text))

    def validate(self):
        if not self.loaded:
            return
        self._sync_model()
        name, validator = self._format_info()
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            info = validator(self._full_edited_text())
        except Exception as exc:
            info = f"INVALID: {exc}"
        finally:
            QApplication.restoreOverrideCursor()
        QMessageBox.information(self, "Validate", f"{name}: {info}")

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
        right_sel = self._range_selections(self.right, "".join(b), right_r, RIGHT_CHAR_COLOR)

        self.left.setExtraSelections(left_sel)
        self.right.setExtraSelections(right_sel)
        self._update_status(len(left_r) + len(right_r))

    def _update_status(self, page_regions):
        name, validator = self._format_info()
        if len(self.raw) <= self.VALIDATE_AUTO_BYTES:
            try:
                info = validator(self._full_edited_text())
            except Exception as exc:
                info = f"INVALID: {exc}"
        else:
            info = "not validated (large file — click Validate)"
        hint = "  [not UTF-8: if text looks garbled, pick another Encoding]" if self.encoding in (
            "latin-1", "cp1252") else ""
        self.status.setText(
            f"{name} ({self.encoding}) | {info} | this page: {page_regions} changed region(s) | "
            f"pages modified: {len(self._dirty)}/{self._n_pages()}{hint}"
        )

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
    app = QApplication(sys.argv)
    win = SplitEditor()
    win.show()
    args = app.arguments()[1:]
    if args:
        win.load_path(args[0])
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
