"""
Split File Editor
-----------------
Left pane  : original file (read-only). Changed/removed lines are highlighted;
             click one to get "Undo change on line N" and restore just that line.
Right pane : editable copy, added/changed parts highlighted live.
Paging     : the file is shown X lines per page (X selectable in the toolbar).

Supports: .txt, .csv, .json, .xml  (add more in FORMATS below)
Requires: Python 3.8+ (tkinter only, no third-party packages)
Unicode: Bengali / Arabic / English / digits; encoding picker, CRLF-preserving save.

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
import sys
import tkinter as tk
import tkinter.font as tkfont
import unicodedata
import xml.etree.ElementTree as ET
from difflib import SequenceMatcher
from tkinter import filedialog, messagebox, ttk

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

FILETYPES = [
    ("Supported files", " ".join(f"*{e}" for e in FORMATS)),
    ("All files", "*.*"),
]

_CURRENT = object()  # sentinel: "use the current page size" (None means All)
# First installed family wins. Pick fonts that cover Bengali + Arabic + Latin;
# anything missing falls back per-character. Changeable from the toolbar.
FONT_CANDIDATES = [
    "Nirmala UI", "Segoe UI", "Kohinoor Bangla", "Noto Sans Bengali", "Noto Sans",
    "Lohit Bengali", "Kalpurush", "SolaimanLipi", "Arial Unicode MS", "DejaVu Sans",
]
PAGE_SIZES = ["25", "50", "100", "250", "500", "1000", "All"]
DEFAULT_PAGE_SIZE = 100

# ----------------------------------------------------------------------------
# Pure logic (no UI) -- easy to unit test and to extend
# ----------------------------------------------------------------------------


def split_lines(text):
    """Split on '\\n' only (keeps line endings), so it matches Tk's line numbering."""
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


class SplitEditor(tk.Tk):
    DEBOUNCE_MS = 150

    def __init__(self):
        super().__init__()
        self.title("Split File Editor")
        self.geometry("1200x700")

        self.path = None
        self.loaded = False
        self.raw = b""
        self.encoding = "utf-8"
        self.newline = "\n"

        avail = set(tkfont.families(self))
        family = next((f for f in FONT_CANDIDATES if f in avail),
                      tkfont.nametofont("TkDefaultFont").actual("family"))
        self.text_font = tkfont.Font(self, family=family, size=12)
        self.orig_lines = []
        self.edited_chunks = [[]]
        self.page = 0
        self.page_size = DEFAULT_PAGE_SIZE  # int, or None for "All"

        self._diff_job = None
        self._syncing = False
        self._left_changed = set()  # local 0-based line numbers highlighted on the left

        self._build_toolbar()
        self._build_panes()
        self._build_statusbar()
        self._bind_keys()
        self._astral_units = self._probe_astral_units()

    # ---- layout -----------------------------------------------------------

    def _build_toolbar(self):
        bar = ttk.Frame(self, padding=(6, 4))
        bar.pack(side="top", fill="x")

        ttk.Button(bar, text="Open…", command=self.open_file).pack(side="left")
        ttk.Button(bar, text="Save As…", command=self.save_file).pack(side="left", padx=4)
        ttk.Button(bar, text="Revert all", command=self.revert).pack(side="left")

        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=10)

        ttk.Label(bar, text="Lines per page:").pack(side="left")
        self.size_var = tk.StringVar(value=str(DEFAULT_PAGE_SIZE))
        self.size_box = ttk.Combobox(bar, textvariable=self.size_var, values=PAGE_SIZES, width=6)
        self.size_box.pack(side="left", padx=4)
        self.size_box.bind("<<ComboboxSelected>>", self._on_size_change)
        self.size_box.bind("<Return>", self._on_size_change)

        self.prev_btn = ttk.Button(bar, text="◀ Prev", command=lambda: self._goto(self.page - 1))
        self.prev_btn.pack(side="left", padx=(10, 2))
        self.next_btn = ttk.Button(bar, text="Next ▶", command=lambda: self._goto(self.page + 1))
        self.next_btn.pack(side="left")
        self.page_label = ttk.Label(bar, text="")
        self.page_label.pack(side="left", padx=8)

        self.file_label = ttk.Label(bar, text="No file loaded")
        self.file_label.pack(side="left", padx=12)

        bar2 = ttk.Frame(self, padding=(6, 0, 6, 4))
        bar2.pack(side="top", fill="x")

        ttk.Label(bar2, text="Encoding:").pack(side="left")
        self.enc_var = tk.StringVar(value=self.encoding)
        enc_box = ttk.Combobox(bar2, textvariable=self.enc_var, values=ENCODINGS, width=10)
        enc_box.pack(side="left", padx=4)
        enc_box.bind("<<ComboboxSelected>>", self._on_encoding_change)
        enc_box.bind("<Return>", self._on_encoding_change)

        ttk.Separator(bar2, orient="vertical").pack(side="left", fill="y", padx=10)

        ttk.Label(bar2, text="Font:").pack(side="left")
        self.font_var = tk.StringVar(value=self.text_font.actual("family"))
        font_box = ttk.Combobox(bar2, textvariable=self.font_var, width=24,
                                values=sorted(set(tkfont.families(self))))
        font_box.pack(side="left", padx=4)
        font_box.bind("<<ComboboxSelected>>", self._on_font_change)
        font_box.bind("<Return>", self._on_font_change)

        self.fsize_var = tk.StringVar(value=str(self.text_font.actual("size")))
        fsize = ttk.Spinbox(bar2, from_=6, to=48, width=4, textvariable=self.fsize_var,
                            command=self._on_font_change)
        fsize.pack(side="left")
        fsize.bind("<Return>", self._on_font_change)

    def _build_panes(self):
        body = ttk.Frame(self)
        body.pack(side="top", fill="both", expand=True)
        # Two equal columns -> window is always split exactly in half.
        body.columnconfigure(0, weight=1, uniform="half")
        body.columnconfigure(1, weight=1, uniform="half")
        body.rowconfigure(1, weight=1)

        ttk.Label(body, text="ORIGINAL (read-only) — click a highlighted line to undo it",
                  anchor="center").grid(row=0, column=0, sticky="ew")
        ttk.Label(body, text="EDITABLE", anchor="center").grid(row=0, column=1, sticky="ew")

        self.left = self._make_text(body, 0, editable=False)
        self.right = self._make_text(body, 1, editable=True)

        # Highlight styles (later-defined tags have higher priority)
        self.left.tag_configure("linechg", background="#fff0f0")
        self.left.tag_configure("changed", background="#ffb3b3")
        self.right.tag_configure("changed", background="#c8f0c8")

        self._link_scroll(self.left, self.right)

        self.right.bind("<<Modified>>", self._on_modified)
        self.left.bind("<Button-1>", self._on_left_click)
        self.left.bind("<Motion>", self._on_left_motion)

    def _make_text(self, parent, col, editable):
        frame = ttk.Frame(parent)
        frame.grid(row=1, column=col, sticky="nsew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)

        text = tk.Text(frame, wrap="none", undo=editable, font=self.text_font)
        ysb = ttk.Scrollbar(frame, orient="vertical", command=text.yview)
        xsb = ttk.Scrollbar(frame, orient="horizontal", command=text.xview)
        text.configure(xscrollcommand=xsb.set)
        text._ysb = ysb
        text.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")

        if not editable:
            text.configure(state="disabled", cursor="arrow")
        return text

    def _link_scroll(self, a, b):
        """Keep both panes scrolled to the same top line."""
        def make(src, dst):
            def handler(first, last):
                src._ysb.set(first, last)
                if not self._syncing:
                    self._syncing = True
                    try:
                        line = src.index("@0,0").split(".")[0]
                        dst.yview(f"{line}.0")
                    finally:
                        self._syncing = False
            return handler

        a.configure(yscrollcommand=make(a, b))
        b.configure(yscrollcommand=make(b, a))

    def _build_statusbar(self):
        self.status = tk.StringVar(value="Open a file to begin.")
        ttk.Label(self, textvariable=self.status, relief="sunken", anchor="w", padding=(6, 2)).pack(
            side="bottom", fill="x"
        )

    def _bind_keys(self):
        self.bind("<Control-o>", lambda e: self.open_file())
        self.bind("<Control-s>", lambda e: self.save_file())

    # ---- paging helpers ---------------------------------------------------

    def _eff(self, size=_CURRENT):
        """Effective lines-per-page (a number even when 'All' = None)."""
        size = self.page_size if size is _CURRENT else size
        return size or max(len(self.orig_lines), 1)

    def _n_pages(self, size=_CURRENT):
        n, eff = len(self.orig_lines), self._eff(size)
        return max(1, -(-n // eff))

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

    def _on_size_change(self, _event=None):
        txt = self.size_var.get().strip()
        try:
            new = None if txt.lower() == "all" else int(txt)
            if new is not None and new < 1:
                raise ValueError
        except ValueError:
            messagebox.showwarning("Lines per page", "Enter a positive number or 'All'.")
            self.size_var.set("All" if self.page_size is None else str(self.page_size))
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
        self._render_page()

    # ---- file handling ----------------------------------------------------

    def _probe_astral_units(self):
        """How many '+Nc' index steps does Tk take for a non-BMP char (emoji): 1 or 2?"""
        try:
            t = tk.Text(self)
            t.insert("1.0", "\U0001F600x")
            units = 1 if t.get("1.0+1c", "1.0+2c") == "x" else 2
            t.destroy()
            return units
        except Exception:
            return 1

    def _on_font_change(self, _event=None):
        fam = self.font_var.get().strip()
        if fam in set(tkfont.families(self)):
            self.text_font.configure(family=fam)
        try:
            self.text_font.configure(size=max(6, min(48, int(self.fsize_var.get()))))
        except ValueError:
            self.fsize_var.set(str(self.text_font.actual("size")))

    def _on_encoding_change(self, _event=None):
        enc = self.enc_var.get().strip()
        try:
            codecs.lookup(enc)
        except LookupError:
            messagebox.showwarning("Encoding", f"Unknown encoding: {enc}")
            self.enc_var.set(self.encoding)
            return
        if enc == self.encoding:
            return
        if not self.loaded:
            self.encoding = enc
            return
        self._sync_model()
        if self._is_modified() and not messagebox.askyesno(
            "Change encoding", "Re-reading the file with another encoding discards your edits. Continue?"
        ):
            self.enc_var.set(self.encoding)
            return
        self._decode_and_load(enc)

    def open_file(self):
        path = filedialog.askopenfilename(filetypes=FILETYPES)
        if path:
            self.load_path(path)

    def load_path(self, path):
        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))
            return
        self.path, self.raw = path, data
        self.file_label.config(text=path)
        self._decode_and_load(detect_encoding(data))

    def _decode_and_load(self, enc):
        try:
            text = self.raw.decode(enc)
        except (UnicodeError, LookupError) as exc:
            messagebox.showerror("Decode failed", f"Cannot read this file as {enc}:\n{exc}")
            self.enc_var.set(self.encoding)
            return
        text, self.newline = normalize_newlines(text)
        self.encoding = enc
        self.enc_var.set(enc)
        self.orig_lines = split_lines(text)
        self.loaded = True
        self.page = 0
        self.edited_chunks = [list(self._orig_chunk(k)) for k in range(self._n_pages())]
        self._render_page()

    def _is_modified(self):
        return any(c != self._orig_chunk(k) for k, c in enumerate(self.edited_chunks))

    def revert(self):
        if not self.loaded:
            return
        self._sync_model()
        if self._is_modified() and not messagebox.askyesno(
            "Revert all", "Discard all edits on every page and restore the original?"
        ):
            return
        self.edited_chunks = [list(self._orig_chunk(k)) for k in range(self._n_pages())]
        self._render_page()

    def save_file(self):
        if not self.loaded:
            return
        self._sync_model()
        ext = "." + self.path.rsplit(".", 1)[-1].lower() if "." in self.path else ""
        out = filedialog.asksaveasfilename(
            initialfile=self.path.replace("\\", "/").rsplit("/", 1)[-1],
            defaultextension=ext,
            filetypes=FILETYPES,
        )
        if not out:
            return
        text = self._full_edited_text().replace("\n", self.newline)
        enc = self.encoding
        try:
            data = text.encode(enc)
        except UnicodeEncodeError:
            if not messagebox.askyesno(
                "Encoding", f"Some characters can't be stored as {enc}.\nSave as UTF-8 instead?"
            ):
                return
            enc, data = "utf-8", text.encode("utf-8")
        try:
            with open(out, "wb") as f:
                f.write(data)
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))
            return
        self.status.set(f"Saved to {out} ({enc})")

    # ---- text helpers -----------------------------------------------------

    def _full_edited_text(self):
        return "".join(ln for c in self.edited_chunks for ln in c)

    def _right_text(self):
        return self.right.get("1.0", "end-1c")

    def _sync_model(self):
        """Pull what is currently in the right pane into the model."""
        if self._diff_job:
            self.after_cancel(self._diff_job)
            self._diff_job = None
        if self.loaded:
            self.edited_chunks[self.page] = split_lines(self._right_text())

    def _render_page(self):
        """Load the current page into both panes (resets typing-undo history)."""
        a = self._orig_chunk(self.page)
        b = self.edited_chunks[self.page]

        self.left.configure(state="normal")
        self.left.delete("1.0", "end")
        self.left.insert("1.0", "".join(a))
        self.left.configure(state="disabled")

        self.right.delete("1.0", "end")
        self.right.insert("1.0", "".join(b))
        self.right.edit_reset()
        self.right.edit_modified(False)
        self.left.yview_moveto(0)
        self.right.yview_moveto(0)

        n, eff = len(self.orig_lines), self._eff()
        pages = self._n_pages()
        if n:
            lo, hi = self.page * eff + 1, min((self.page + 1) * eff, n)
            self.page_label.config(text=f"Page {self.page + 1}/{pages}  (lines {lo}–{hi} of {n})")
        else:
            self.page_label.config(text="Page 1/1  (empty file)")
        self.prev_btn.state(["!disabled"] if self.page > 0 else ["disabled"])
        self.next_btn.state(["!disabled"] if self.page < pages - 1 else ["disabled"])

        self._refresh_diff()

    def _replace_right(self, text):
        """Swap the right pane's content as ONE undoable step (Ctrl+Z works)."""
        yv = self.right.yview()[0]
        self.right.configure(autoseparators=False)  # keep delete+insert in one group
        self.right.edit_separator()
        self.right.delete("1.0", "end")
        self.right.insert("1.0", text)
        self.right.edit_separator()
        self.right.configure(autoseparators=True)
        self.right.yview_moveto(yv)

    # ---- live diff --------------------------------------------------------

    def _on_modified(self, _event):
        if not self.right.edit_modified():
            return
        self.right.edit_modified(False)  # re-arm the event
        if self._diff_job:
            self.after_cancel(self._diff_job)
        self._diff_job = self.after(self.DEBOUNCE_MS, self._refresh_diff)

    def _refresh_diff(self):
        if not self.loaded:
            return
        self._sync_model()
        a = self._orig_chunk(self.page)
        b = self.edited_chunks[self.page]
        ops, left_r, right_r = compute_diff(a, b)

        for widget in (self.left, self.right):
            widget.tag_remove("changed", "1.0", "end")
        self.left.tag_remove("linechg", "1.0", "end")
        self._left_changed = set()

        def astral(lines):  # positions of non-BMP chars, only needed if Tk counts them as 2
            if self._astral_units == 1:
                return []
            return [i for i, c in enumerate("".join(lines)) if ord(c) > 0xFFFF]

        def idx(pos, off):
            return f"1.0+{off + bisect.bisect_left(pos, off) * (self._astral_units - 1)}c"

        pa, pb = astral(a), astral(b)
        for s, e in left_r:
            self.left.tag_add("changed", idx(pa, s), idx(pa, e))
        for s, e in right_r:
            self.right.tag_add("changed", idx(pb, s), idx(pb, e))
        for tag, i1, i2, _j1, _j2 in ops:
            if tag != "equal" and i2 > i1:
                self.left.tag_add("linechg", f"{i1 + 1}.0", f"{i2 + 1}.0")
                self._left_changed.update(range(i1, i2))

        self._update_status(len(left_r) + len(right_r))

    def _update_status(self, page_regions):
        ext = "." + self.path.rsplit(".", 1)[-1].lower() if "." in self.path else ""
        name, validator = FORMATS.get(ext, ("Text", _validate_text))
        try:
            info = validator(self._full_edited_text())
        except Exception as exc:
            info = f"INVALID: {exc}"
        pages_mod = sum(c != self._orig_chunk(k) for k, c in enumerate(self.edited_chunks))
        hint = "  [not UTF-8: if text looks garbled, pick another Encoding]" if self.encoding in (
            "latin-1", "cp1252") else ""
        self.status.set(
            f"{name} ({self.encoding}) | {info} | this page: {page_regions} changed region(s) | "
            f"pages modified: {pages_mod}/{self._n_pages()}{hint}"
        )

    # ---- click-to-undo on the left pane ----------------------------------

    def _left_line_at(self, event):
        idx = self.left.index(f"@{event.x},{event.y}")
        bb = self.left.bbox(idx)
        if not bb or not (bb[1] <= event.y < bb[1] + bb[3]):
            return None
        return int(idx.split(".")[0]) - 1

    def _on_left_motion(self, event):
        line = self._left_line_at(event)
        self.left.configure(cursor="hand2" if line in self._left_changed else "arrow")

    def _on_left_click(self, event):
        line = self._left_line_at(event)
        if line is None or line not in self._left_changed:
            return
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(
            label=f"Undo change on line {self._page_start() + line + 1}",
            command=lambda: self._undo_line(line),
        )
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _undo_line(self, line):
        self._sync_model()
        new_b = restore_line(self._orig_chunk(self.page), self.edited_chunks[self.page], line)
        if new_b is None:
            return
        self.edited_chunks[self.page] = new_b
        self._replace_right("".join(new_b))
        self._refresh_diff()


if __name__ == "__main__":
    app = SplitEditor()
    if len(sys.argv) > 1:  # optional: python split_editor.py somefile.json
        app.load_path(sys.argv[1])
    app.mainloop()