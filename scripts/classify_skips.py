#!/usr/bin/env python3
"""Classify every router skip in the two --full Theorem-3 corpora, by hand.

Supports the §4.4 remark about the built/skipped split: replays the exact
family lists and seeds that `verify_x3c.py --full --vacate` and
`crosscheck_sol.py --full` feed to `run_suite`, and for every family the
board router gives up on prints WHY it is a no-instance (its uncovered
elements) and what X3C says. Round 9 introduced this as a throwaway; round
10 promoted it into the repository because the classification is quoted in
the paper: 7 skip events across the two corpora, 5 distinct families (two
are skipped in both), every one a degenerate no-instance with an uncovered
element.

SLOW and BY-HAND: this drives the same randomized hill-climb router as the
suites themselves (minutes), so it is not part of test_regressions.py. Run
it when the corpus definitions or seeds change, and reconcile the printout
with §4.4 and the embedding verifier's per-family classification.
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_x3c as V            # noqa: E402
import crosscheck_sol as C        # noqa: E402


def classify(tag, families, seed, skipped):
    rng = random.Random(seed)
    for n, sets in families:
        inst = V.build_instance(n, sets, rng)
        if inst is None:
            uncovered = sorted(set(range(n)) - {e for s in sets for e in s})
            skipped.append((n, tuple(map(tuple, sets))))
            print(f"{tag}: SKIP n={n} sets={sets} "
                  f"uncovered={uncovered or 'NONE (planar? check!)'} "
                  f"x3c_yes={V.x3c_is_yes(n, sets)}")


def main() -> int:
    skips_x3c, skips_cross = [], []

    # verify_x3c --full corpus, exactly as its main() feeds run_suite
    classify("x3c[4]", [(3, [(0, 1, 2)])], 101, skips_x3c)
    classify("x3c[5]", (V.planted_instances(2, 2, 10, seed=3)
                        + V.random_instances(2, 3, 10, seed=5)
                        + V.random_instances(2, 4, 10, seed=41)), 202,
             skips_x3c)
    classify("x3c[6]", (V.planted_instances(3, 2, 8, seed=13)
                        + V.random_instances(3, 6, 10, seed=17)
                        + V.planted_instances(4, 2, 5, seed=23)
                        + V.random_instances(4, 7, 5, seed=29)), 303,
             skips_x3c)

    # crosscheck_sol --full corpus (cross_instances), seed 777, sol stats
    saved = C.with_sol_stats()
    try:
        classify("cross", ([(3, [(0, 1, 2)])]
                           + V.planted_instances(2, 2, 8, seed=3)
                           + V.random_instances(2, 3, 8, seed=5)
                           + V.random_instances(2, 4, 8, seed=41)
                           + V.planted_instances(3, 2, 6, seed=13)
                           + V.random_instances(3, 6, 6, seed=17)
                           + V.planted_instances(4, 2, 3, seed=23)), 777,
                 skips_cross)
    finally:
        C.restore(saved)

    distinct = set(skips_x3c) | set(skips_cross)
    both = set(skips_x3c) & set(skips_cross)
    print(f"skip events: {len(skips_x3c)} (x3c --full --vacate) + "
          f"{len(skips_cross)} (crosscheck --full) = "
          f"{len(skips_x3c) + len(skips_cross)}; "
          f"{len(distinct)} distinct families, {len(both)} skipped in both")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
