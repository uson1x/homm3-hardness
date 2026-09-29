#!/usr/bin/env python3
"""Parse the four adapter pictures of Appendix C (homm3/paper/main.md) into Lean literals.

Session 4, target 3.  Reads main.md and `verify_x3c.ADAPTERS` read-only.  For each of the
four patterns (in the order printed: missing LEFT, RIGHT, BOTTOM, TOP) it prints

* the 9 x 9 picture as a Lean `List (List ℕ)` literal, row by row (`#` -> 0, `.` -> 1,
  `Z` -> 2, `U`/`R`/`D` -> 3), and
* the three arms of `verify_x3c.ADAPTERS` as `(port, [cells])`,

and asserts on the Python side that the picture's free cells are exactly the arms plus `Z`
(so the printed patterns are the machine-checked ones).  Lean re-checks all of it.

Run from formal/lean:  PYTHONDONTWRITEBYTECODE=1 python3 tools/appendix_c.py
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))  # the artifact root (homm3/)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
sys.dont_write_bytecode = True

import verify_x3c as V  # noqa: E402

CODE = {"#": 0, ".": 1, "Z": 2, "U": 3, "R": 3, "D": 3}
ORDER = [("LEFT", "TRB"), ("RIGHT", "TBL"), ("BOTTOM", "TRL"), ("TOP", "RBL")]
PORT = {"top": 0, "right": 1, "bottom": 2, "left": 3}


def main():
    text = open(os.path.join(ROOT, "paper", "main.md")).read()
    start = text.index("## Appendix C.")
    end = text.index("## Appendix D.")
    sec = text[start:end]
    blocks = re.findall(r"Missing `(\w+)`[^\n]*\n(?:[^\n]*\n)*?\n```\n(.*?)```", sec, re.S)
    assert [b[0] for b in blocks] == [o[0] for o in ORDER], [b[0] for b in blocks]
    out = []
    for (missing, pic), (_, key) in zip(blocks, ORDER):
        rows = [r for r in pic.split("\n") if r.strip()]
        assert len(rows) == 9
        grid = []
        for y, r in enumerate(rows):
            assert r.startswith(" ") == (y % 2 == 0), (missing, y, r)
            toks = r.split()
            assert len(toks) == 9
            grid.append([CODE[t] for t in toks])
        arms = V.ADAPTERS[key]
        free = {(x, y) for y in range(9) for x in range(9) if grid[y][x] != 0}
        cells = {c for arm in arms.values() for c in arm} | {(4, 4)}
        assert free == cells, (missing, sorted(free ^ cells))
        armlits = ", ".join(
            f"({PORT[side]}, [" + ", ".join(f"({x}, {y})" for x, y in cells_) + "])"
            for side, cells_ in arms.items())
        out.append(f"-- missing {missing} ({key})\n"
                   f"def grid{missing.capitalize()} : List (List ℕ) :=\n  "
                   + ",\n   ".join(str(r) for r in grid).join(["[", "]"]) + "\n"
                   f"def arms{missing.capitalize()} : List (ℕ × List (ℕ × ℕ)) := [{armlits}]\n")
    print("\n".join(out))


if __name__ == "__main__":
    main()
