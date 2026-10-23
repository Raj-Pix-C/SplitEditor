"""
Split File Editor
-----------------
Left pane  : original file (read-only), changed/removed parts highlighted live.
Right pane : editable copy, added/changed parts highlighted live.

Supports: .txt, .csv, .json, .xml  (add more in FORMATS below)
Requires: Python 3.8+ (tkinter only, no third-party packages)
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
# Each validator takes the text and returns a short status string,
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

# ----------------------------------------------------------------------------
# Diff engine  (extension point #2: swap this out for a different algorithm)
# Returns (left_ranges, right_ranges) as lists of (start, end) char offsets.
# Line-level diff first, then char-level inside changed blocks (fast on big files).
# ----------------------------------------------------------------------------

MAX_CHAR_DIFF = 20000  # blocks larger than this are highlighted whole


def compute_diff(original, edited):
    a_lines = original.splitlines(keepends=True)
    b_lines = edited.splitlines(keepends=True)

    def offsets(lines):
        out, pos = [], 0
        for ln in lines:
            out.append(pos)
            pos += len(ln)
        out.append(pos)
        return out

    a_off, b_off = offsets(a_lines), offsets(b_lines)
    left, right = [], []

    for tag, i1, i2, j1, j2 in SequenceMatcher(None, a_lines, b_lines, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        a0, a1 = a_off[i1], a_off[i2]
        b0, b1 = b_off[j1], b_off[j2]

        if tag == "delete":
            left.append((a0, a1))
        elif tag == "insert":
            right.append((b0, b1))
        else:  # replace -> refine at character level
            a_blk, b_blk = original[a0:a1], edited[b0:b1]
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
    return left, right


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
        self.original = ""
        self._diff_job = None
        self._syncing = False

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
        ttk.Button(bar, text="Revert", command=self.revert).pack(side="left")
        self.file_label = ttk.Label(bar, text="No file loaded")
        self.file_label.pack(side="left", padx=12)

    def _build_panes(self):
        body = ttk.Frame(self)
        body.pack(side="top", fill="both", expand=True)
        # Two equal columns -> window is always split exactly in half.
        body.columnconfigure(0, weight=1, uniform="half")
        body.columnconfigure(1, weight=1, uniform="half")
        body.rowconfigure(1, weight=1)

        ttk.Label(body, text="ORIGINAL (read-only)", anchor="center").grid(row=0, column=0, sticky="ew")
        ttk.Label(body, text="EDITABLE", anchor="center").grid(row=0, column=1, sticky="ew")

        self.left = self._make_text(body, 0, editable=False)
        self.right = self._make_text(body, 1, editable=True)

        # Highlight styles
        self.left.tag_configure("changed", background="#ffd0d0")
        self.right.tag_configure("changed", background="#c8f0c8")

        # Keep both panes scrolled together
        self._link_scroll(self.left, self.right)

        self.right.bind("<<Modified>>", self._on_modified)

    def _make_text(self, parent, col, editable):
        frame = ttk.Frame(parent)
        frame.grid(row=1, column=col, sticky="nsew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)

        text = tk.Text(frame, wrap="none", undo=editable, font=("Courier New", 11))
        ysb = ttk.Scrollbar(frame, orient="vertical", command=text.yview)
        xsb = ttk.Scrollbar(frame, orient="horizontal", command=text.xview)
        text.configure(xscrollcommand=xsb.set)
        text._ysb = ysb  # used by scroll linking
        text.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")

        if not editable:
            text.configure(state="disabled", cursor="arrow")
        return text

    def _link_scroll(self, a, b):
        def make(src, dst):
            def handler(first, last):
                src._ysb.set(first, last)
                if not self._syncing:
                    self._syncing = True
                    dst.yview_moveto(first)
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
        if not path:
            return
        try:
            text = self._read(path)
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))
            return

        self.path = path
        self.original = text
        self.file_label.config(text=path)

        self._set_left(text)
        self._set_right(text)
        self._refresh_diff()

    def revert(self):
        if self.path:
            self._set_right(self.original)
            self._refresh_diff()

    def save_file(self):
        if not self.path:
            return
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
                f.write(self._right_text())
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))
            return
        self.status.set(f"Saved to {out}")

    # ---- text helpers -----------------------------------------------------

    def _set_left(self, text):
        self.left.configure(state="normal")
        self.left.delete("1.0", "end")
        self.left.insert("1.0", text)
        self.left.configure(state="disabled")

    def _set_right(self, text):
        self.right.delete("1.0", "end")
        self.right.insert("1.0", text)
        self.right.edit_reset()
        self.right.edit_modified(False)

    def _right_text(self):
        return self.right.get("1.0", "end-1c")

    # ---- live diff --------------------------------------------------------

    def _on_modified(self, _event):
        if not self.right.edit_modified():
            return
        self.right.edit_modified(False)  # re-arm the event
        if self._diff_job:
            self.after_cancel(self._diff_job)
        self._diff_job = self.after(self.DEBOUNCE_MS, self._refresh_diff)

    def _refresh_diff(self):
        self._diff_job = None
        if not self.path:
            return
        edited = self._right_text()
        left_r, right_r = compute_diff(self.original, edited)

        for widget, ranges in ((self.left, left_r), (self.right, right_r)):
            widget.tag_remove("changed", "1.0", "end")
            for s, e in ranges:
                widget.tag_add("changed", f"1.0+{s}c", f"1.0+{e}c")

        self._update_status(edited, len(left_r) + len(right_r))

    def _update_status(self, edited, n_changes):
        ext = "." + self.path.rsplit(".", 1)[-1].lower() if "." in self.path else ""
        name, validator = FORMATS.get(ext, ("Text", _validate_text))
        try:
            info = validator(edited)
        except Exception as exc:
            info = f"INVALID: {exc}"
        state = "unchanged" if edited == self.original else f"{n_changes} changed region(s)"
        self.status.set(f"{name} | {info} | {state}")


if __name__ == "__main__":
    app = SplitEditor()
    if len(sys.argv) > 1:  # optional: python split_editor.py somefile.json
        try:
            app.path = sys.argv[1]
            app.original = app._read(app.path)
            app.file_label.config(text=app.path)
            app._set_left(app.original)
            app._set_right(app.original)
            app._refresh_diff()
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))
    app.mainloop()
