"""Seeded fuzz of the Lemma D.4 pipeline and an independent planarity oracle.

Round 13. Both panel reviewers ran a version of these two checks on their
own (codex Checks 14-15, fable backlog item (г)) and found them cheap and
clean; the project's standing decision "no DMP cross-check, no pipeline
fuzz" (2026-08-23) rested on the implementation not being the proof
(Appendix D.6 says so), which is true but does not make the coverage
worthless.  So the two checks live here, OUTSIDE the battery -- same policy
as `audit_ability_projection.py` and `check_artifact_repo.py`: run them when
the router, the drawing or the planarity test changes, and after every
constant change.

  [1] pipeline fuzz -- seeded random 3-uniform families at |X| in
      {3, 6, 9, 12}, up to ten sets each, through `build_board_lemma`:
      every board must pass I1-I4 (`verify_x3c.check_geometry`) and the real
      (SEP') check (`verify_embedding.check_separation`); every G_no must
      carry a true certificate (a non-planar family, or a degenerate one
      that X3C itself answers no); nothing may raise.

  [2] planarity oracle -- EVERY labelled simple graph on six vertices
      (2^15 = 32768 of them) is classified by DMP (`planar_embed.planarity`)
      and by an independent forbidden-subgraph oracle: a graph on at most
      six vertices is non-planar iff it contains K5, K3,3 or K5 with one
      edge subdivided (the only Kuratowski subdivisions that fit in six
      vertices).  The two verdicts must agree on all 32768 graphs.  This
      tests the DMP verdict without asking DMP which graphs are planar; it
      says nothing about larger incidence graphs.

Run:  python3 scripts/fuzz_pipeline.py            # 300 families, ~5 s
      python3 scripts/fuzz_pipeline.py --families 1000
"""

from __future__ import annotations

import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import planar_embed as P
import verify_embedding as E
import verify_x3c as V
from embed_lemma import build_board_lemma


def fuzz_pipeline(n_families: int, seed: int = 13092026) -> tuple[dict, list]:
    rng = random.Random(seed)
    counts = {"board": 0, "G_no": 0, "nonplanar": 0, "degenerate": 0}
    fails = []
    for _ in range(n_families):
        n = rng.choice([3, 6, 9, 12])
        triples = list(itertools.combinations(range(n), 3))
        sets = rng.sample(triples, rng.randint(1, min(10, len(triples))))
        try:
            kind, payload = build_board_lemma(n, sets)
        except Exception as exc:  # noqa: BLE001 -- a raise IS the finding
            fails.append((n, sets, f"raised {exc!r}"))
            continue
        counts[kind] += 1
        if kind == "board":
            bad = V.check_geometry(payload) + E.check_separation(payload)[0]
            if bad:
                fails.append((n, sets, bad))
        else:
            reason = payload["reason"]
            if "planar" in reason:
                counts["nonplanar"] += 1
                if E.incidence_planar(n, sets):
                    fails.append((n, sets, "certified non-planar but the "
                                            "incidence graph is planar"))
            else:
                counts["degenerate"] += 1
                if V.x3c_is_yes(n, sets):
                    fails.append((n, sets, f"G_no ({reason}) for an X3C "
                                            f"yes-instance"))
    return counts, fails


def six_vertex_oracle() -> tuple[int, int, list]:
    n = 6
    edges = list(itertools.combinations(range(n), 2))
    index = {e: i for i, e in enumerate(edges)}

    def bits(es):
        return sum(1 << index[tuple(sorted(e))] for e in set(es))

    forbidden = set()
    for branch in itertools.combinations(range(n), 5):
        complete = set(itertools.combinations(branch, 2))
        forbidden.add(bits(complete))                       # K5
        extra = next(v for v in range(n) if v not in branch)
        for u, v in complete:                                # K5, one edge
            forbidden.add(bits((complete - {(u, v)})         # subdivided
                               | {tuple(sorted((u, extra))),
                                  tuple(sorted((v, extra)))}))
    for side in itertools.combinations(range(n), 3):         # K3,3
        other = set(range(n)) - set(side)
        forbidden.add(bits((u, v) for u in side for v in other))

    planar = 0
    mismatches = []
    for mask in range(1 << len(edges)):
        expected = not any(mask & f == f for f in forbidden)
        got = P.planarity(n, [e for i, e in enumerate(edges)
                              if mask >> i & 1]) is not None
        planar += got
        if got != expected:
            mismatches.append((mask, expected, got))
    return 1 << len(edges), planar, mismatches


def main() -> int:
    n_families = 300
    if "--families" in sys.argv:
        n_families = int(sys.argv[sys.argv.index("--families") + 1])
    t0 = time.time()
    counts, fails = fuzz_pipeline(n_families)
    print(f"[1] pipeline fuzz: {n_families} seeded families -> "
          f"{counts['board']} boards, {counts['G_no']} G_no "
          f"({counts['nonplanar']} non-planar, {counts['degenerate']} "
          f"degenerate), {len(fails)} failures ({time.time() - t0:.1f}s)")
    for f in fails[:10]:
        print("   FAIL", f)
    t1 = time.time()
    total, planar, mism = six_vertex_oracle()
    print(f"[2] planarity oracle: {total} labelled graphs on six vertices, "
          f"{planar} planar, {len(mism)} DMP/oracle mismatches "
          f"({time.time() - t1:.1f}s)")
    for m in mism[:10]:
        print("   MISMATCH", m)
    if fails or mism:
        print("\nFAILED")
        return 1
    print(f"\nALL PASS  (fuzz: {n_families} families, {counts['board']} boards "
          f"I1-I4 + (SEP'), {counts['G_no']} true certificates; oracle: "
          f"{total} graphs, 0 mismatches)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
