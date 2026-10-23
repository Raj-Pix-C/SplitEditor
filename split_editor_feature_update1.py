"""
Split File Editor
-----------------
Left pane  : original file (read-only). Changed/removed lines are highlighted;
             click one to get "Undo change on line N" and restore just that line.
Right pane : editable copy, added/changed parts highlighted live.
Paging     : the file is shown X lines per page (X selectable in the toolbar).

Supports: .txt, .csv, .json, .xml  (add more in FORMATS below)
Requires: Python 3.8+ (tkinter only, no third-party packages)

Data model
----------
orig_lines     : original file as a list of lines (never changes)
edited_chunks  : one list of lines per page, in original-page coordinates.
                 Editing page k only touches edited_chunks[k], so a page's
                 left/right panes always line up regardless of other pages.
"""

import csv
import io
import json
import sys
import tkinter as tk
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
            for t, x1, x2, y1, y2 in SequenceMatcher(None, a_blk, b_blk, autojunk=False).get_opcodes():
                if t == "equal":
                    continue
                if x2 > x1:
                    left.append((a0 + x1, a0 + x2))
                if y2 > y1:
                    right.append((b0 + y1, b0 + y2))
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

        text = tk.Text(frame, wrap="none", undo=editable, font=("Courier New", 11))
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

    @staticmethod
    def _read(path):
        for enc in ("utf-8-sig", "utf-16", "latin-1"):
            try:
                with open(path, "r", encoding=enc) as f:
                    return f.read()
            except (UnicodeError, UnicodeDecodeError):
                continue
        raise ValueError("Could not decode file")

    def open_file(self):
        path = filedialog.askopenfilename(filetypes=FILETYPES)
        if path:
            self.load_path(path)

    def load_path(self, path):
        try:
            text = self._read(path)
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))
            return
        self.path = path
        self.orig_lines = split_lines(text)
        self.loaded = True
        self.page = 0
        self.edited_chunks = [list(self._orig_chunk(k)) for k in range(self._n_pages())]
        self.file_label.config(text=path)
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
        try:
            with open(out, "w", encoding="utf-8", newline="") as f:
                f.write(self._full_edited_text())
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))
            return
        self.status.set(f"Saved to {out}")

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

        for s, e in left_r:
            self.left.tag_add("changed", f"1.0+{s}c", f"1.0+{e}c")
        for s, e in right_r:
            self.right.tag_add("changed", f"1.0+{s}c", f"1.0+{e}c")
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
        self.status.set(
            f"{name} | {info} | this page: {page_regions} changed region(s) | "
            f"pages modified: {pages_mod}/{self._n_pages()}"
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
