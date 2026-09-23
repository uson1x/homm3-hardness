"""Exhaustive check of the deployment-stub clause of Lemma D.4, step 5.

The clause: in an element-vertex box (radius RHO, centre on an even row) whose free
hexes are the centre, the axis segments to the used ports, and a two-hex stub along an
unused axis direction u, the outer stub hex p_e has EXACTLY ONE free neighbour (the
inner stub hex).  The paper once justified the LEFT/UP cases from RIGHT/DOWN "by the
reflections that preserve row parity"; reflecting in a column does not preserve hex
adjacency in offset coordinates, so the cases are checked directly here instead: every
used-port set (at most three ports, so the stub direction exists), every stub direction
u outside it, both row parities of the centre (the algorithm only ever uses even rows,
but the clause holds for odd ones too).  Adjacency comes from Battlefield.neighbours
(BattleHex.h:147-178), not from a private copy of the rule.

Run:  python3 scripts/check_stub.py      # expected: "... 0 failures"
"""
from __future__ import annotations

import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from embed_lemma import RHO  # noqa: E402
from homm3_model import Battlefield  # noqa: E402

DIRS = {"R": (1, 0), "L": (-1, 0), "T": (0, -1), "B": (0, 1)}


def check() -> tuple[int, int]:
    size = 2 * RHO + 5
    bf = Battlefield(size, size)
    cases = failures = 0
    for parity in (0, 1):
        cx, cy = RHO + 2, RHO + 2 + parity
        assert cy % 2 == parity
        for k in range(0, 4):
            for used in itertools.combinations("RLTB", k):
                for u in "RLTB":
                    if u in used:
                        continue
                    free = {(cx, cy)}
                    for d in used:
                        dx, dy = DIRS[d]
                        free.update((cx + dx * t, cy + dy * t) for t in range(1, RHO + 1))
                    ux, uy = DIRS[u]
                    inner, outer = (cx + ux, cy + uy), (cx + 2 * ux, cy + 2 * uy)
                    free.update((inner, outer))
                    nbrs = {bf.xy(h) for h in bf.neighbours(bf.index(*outer))}
                    cases += 1
                    if nbrs & free != {inner}:
                        failures += 1
                        print(f"FAIL parity={parity} used={''.join(used) or '-'} u={u}: "
                              f"free neighbours of p_e = {sorted(nbrs & free)}")
    return cases, failures


if __name__ == "__main__":
    cases, failures = check()
    print(f"deployment-stub clause: {cases} (port set, u, parity) cases, "
          f"{failures} failures")
    sys.exit(1 if failures else 0)
