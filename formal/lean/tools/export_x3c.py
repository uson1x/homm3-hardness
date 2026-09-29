#!/usr/bin/env python3
"""Export the boards of `homm3/scripts/verify_x3c.py` (default tier) as Lean literals.

Session 4, target 4.  The script imports `verify_x3c` read-only and replays its default
suite exactly: `run_suite` seeds one `random.Random(seed)` per suite and only
`build_instance` draws from it, so calling `build_instance` on the same families in the same
order with the same seed rebuilds the same boards bit for bit ([4]: seed 101, the q = 1
family; [5]: seed 202, planted(2, 2, 10, seed 3) + random(2, 3, 10, seed 5) +
random(2, 4, 10, seed 41)).  The negative-control board is rebuilt the way
`check_negative_control` builds it (`random.Random(99)`, fixture [(0,1,2), (0,1,3)]).

For every board it also records Python's verdicts: `x3c_is_yes` and the game search
(`winning_allocations`, historical constants def 41 / hp 5, the script's default `hold`
policy), with the number of winning allocations.

Output: `CrossCheckX3CData.lean` (the literals) and a JSON summary on stdout.
Board format (`Homm3.BoardData`): byte i = x + W*y of `lab` is 0 (impassable), e + 1
(region of element e) or 128 + g (enemy hex of member g); 16-bit field i of `dist` is the
BFS distance of a region hex from its deployment hex inside the region; sigma = W * H.

Run from formal/lean:  PYTHONDONTWRITEBYTECODE=1 python3 tools/export_x3c.py
"""

from __future__ import annotations

import json
import os
import random
import sys
import time
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_ROOT = os.path.dirname(HERE)
SCRIPTS = os.path.normpath(os.path.join(LEAN_ROOT, "..", "..", "scripts"))  # artifact root/scripts
sys.path.insert(0, SCRIPTS)
sys.dont_write_bytecode = True

import verify_x3c as V  # noqa: E402


def neighbours(W, H, h):
    return list(V._neighbours(W, H, h))


def encode(inst):
    W, H = inst["width"], inst["height"]
    owner = inst["owner"]
    lab = 0
    for h, (kind, idx) in owner.items():
        code = idx + 1 if kind == "e" else 128 + idx
        assert 0 < code < 256
        lab |= code << (8 * h)
    # BFS distances inside each region, from the deployment hex
    dist = {}
    for e, p in inst["deploy"].items():
        dist[p] = 0
        dq = deque([p])
        while dq:
            cur = dq.popleft()
            for n in neighbours(W, H, cur):
                if owner.get(n) == ("e", e) and n not in dist:
                    dist[n] = dist[cur] + 1
                    dq.append(n)
    region_hexes = [h for h, o in owner.items() if o[0] == "e"]
    missing = [h for h in region_hexes if h not in dist]
    assert not missing, f"region hexes unreachable from p_e: {missing[:5]}"
    dnum = 0
    for h, d in dist.items():
        assert d < 65536
        dnum |= d << (16 * h)
    n_el = inst["n_elements"]
    p = [(inst["deploy"][e] % W, inst["deploy"][e] // W) for e in range(n_el)]
    z = [(inst["enemy_hex"][s] % W, inst["enemy_hex"][s] // W) for s in range(len(inst["sets"]))]
    return {"W": W, "H": H, "lab": lab, "dist": dnum, "p": p, "z": z, "sigma": W * H,
            "q": n_el // 3, "CL": [list(s) for s in inst["sets"]],
            "free": len(owner), "regions": {e: sum(1 for o in owner.values() if o == ("e", e))
                                            for e in range(n_el)}}


def lean_board(name, b):
    pairs = lambda xs: "[" + ", ".join(f"({x}, {y})" for x, y in xs) + "]"
    return (f"def {name} : BoardData where\n"
            f"  W := {b['W']}\n  H := {b['H']}\n"
            f"  lab := 0x{b['lab']:x}\n"
            f"  dist := 0x{b['dist']:x}\n"
            f"  p := {pairs(b['p'])}\n  z := {pairs(b['z'])}\n  σ := {b['sigma']}\n")


def main():
    t0 = time.time()
    tiers = [
        ("q1", [(3, [(0, 1, 2)])], 101),
        ("q2", V.planted_instances(2, 2, 10, seed=3) + V.random_instances(2, 3, 10, seed=5)
         + V.random_instances(2, 4, 10, seed=41), 202),
    ]
    boards = []
    for tag, fams, seed in tiers:
        rng = random.Random(seed)
        for n, sets in fams:
            inst = V.build_instance(n, sets, rng)
            assert inst is not None, "router skipped a board (the default tier builds all 31)"
            geo = V.check_geometry(inst)
            assert not geo, geo
            b = encode(inst)
            b["x3c"] = V.x3c_is_yes(n, sets)
            wins = V.winning_allocations(inst)
            b["game"] = bool(wins)
            b["winners"] = [list(w) for w in wins]
            boards.append(b)
    # the negative control's board (resource lemma disabled; the board does not depend on def)
    # built as `check_negative_control` builds it: with def(Q) = att(P) in force (the creature
    # types are fixed at build time); a second build at def 41 must give the same board
    fixture = [(0, 1, 2), (0, 1, 3)]
    original = V.ENEMY_DEF
    V.ENEMY_DEF = V.PLAYER_ATT
    try:
        neg1 = V.build_instance(6, fixture, random.Random(99))
        assert neg1 is not None and not V.check_geometry(neg1)
        game_def1 = V.winning_allocations(neg1)
    finally:
        V.ENEMY_DEF = original
    neg = V.build_instance(6, fixture, random.Random(99))
    assert neg["owner"] == neg1["owner"] and neg["deploy"] == neg1["deploy"]
    nb = encode(neg)
    nb["x3c"] = V.x3c_is_yes(6, fixture)
    nb["game_def1"] = [list(w) for w in game_def1]
    nb["game"] = bool(V.winning_allocations(neg, stop_at_first=True))

    out = ["import Homm3.BoardCheck", "",
           "/-!", "# Session 4, target 4. The boards of `verify_x3c.py` (default tier), as data",
           "",
           "Generated by `tools/export_x3c.py` from `homm3/scripts/verify_x3c.py` (read-only",
           "import, the script's own seeds).  `bNN` is the `NN`-th board of the default suite",
           "(`b00`: the q = 1 smoke test; `b01`–`b30`: the q = 2 families in suite order); `bNeg` is",
           "the negative control's board.  Do not edit by hand.",
           "-/", "", "namespace Homm3.X3CData", "", "open Homm3", ""]
    for i, b in enumerate(boards):
        out.append(lean_board(f"b{i:02d}", b))
        out.append(f"def q{i:02d} : ℕ := {b['q']}")
        out.append(f"def C{i:02d} : List (List ℕ) := {b['CL']}")
        out.append("")
    out.append(lean_board("bNeg", nb))
    out.append(f"def qNeg : ℕ := {nb['q']}")
    out.append(f"def CNeg : List (List ℕ) := {nb['CL']}")
    out.append("")
    out.append("end Homm3.X3CData")
    out.append("")
    with open(os.path.join(LEAN_ROOT, "CrossCheckX3CData.lean"), "w") as f:
        f.write("\n".join(out))
    summary = [{"i": i, "q": b["q"], "C": b["CL"], "W": b["W"], "H": b["H"], "free": b["free"],
                "maxR": max(b["regions"].values()), "x3c": b["x3c"], "game": b["game"],
                "winners": b["winners"]} for i, b in enumerate(boards)]
    summary.append({"i": "neg", "q": nb["q"], "C": nb["CL"], "W": nb["W"], "H": nb["H"],
                    "free": nb["free"], "x3c": nb["x3c"], "game": nb["game"],
                    "game_def1": nb["game_def1"]})
    print(json.dumps({"boards": summary, "secs": round(time.time() - t0, 1)}))


if __name__ == "__main__":
    main()
