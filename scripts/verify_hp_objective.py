#!/usr/bin/env python3
"""The hit-point-objective corollary of Theorem 4 (review round 4, finding 1.1).

Claim checked. Take the Theorem 4 instances of candidate-C-featureless.md
unchanged, but replace the objective by TOTAL HIT POINTS REMOVED - absorbed
damage, with overkill discarded (CUnitState.cpp:202-203) - and the threshold by
W_hp = m*T. The resulting decision problem still decides 3-PARTITION, so
maximising hit points removed is strongly NP-hard as well: the earlier drafts'
claim that an HP objective "would make the problem trivial" is true only on the
matching-reach family of Theorem 1 and false in general.

Why the arithmetic relaxation is a sound upper bound for the FULL action model
(WAIT and MOVE-only included): at R = 1 every legal play induces a map
f : [3m] -> [m] u {skip} (a stack strikes at most one enemy); the blow of C_i
delivers at most its nominal a_i (a stack that WAITs and meets a DEFEND bonus
delivers at most nominal, never more -- not strictly less, since the formula
clamps at 1 and a_i = 1 is legal; only the inequality is needed here); enemy g absorbs min(T, sum of incoming) regardless
of order; and no other damage reaches an enemy (the defence holds, so no player
stack ever retaliates). Hence

    HP removed <= max_f sum_g min(T, sum_{i in f^-1(g)} a_i) =: hp_relaxation.

Checks, per instance (same families and smallest legal cases as
verify_featureless.py):
  1. hp_relaxation(a, T, m) == m*T  <=>  3-PARTITION(a, T), decided
     independently by exhaustive search. This is the no-direction.
  2. On every yes-instance the 3-partition witness assignment is played in the
     reference simulator (branching over approach hexes) and the enemies'
     absorbed hit points are read off the final state: exactly m*T. This is the
     yes-direction, constructively.
  3. Negative control: on the fixed no-instance [4,4,4,4,4,6], T = 13 the
     relaxation must stay strictly below m*T (a pass carries evidence, not
     silence).
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from verify_featureless import (  # noqa: E402
    SMALL_CASES, _solution_assignment, assemble, balance, build, gen_instances,
    initial_enemy_counts, run_defence, three_partition_answer,
)


def hp_relaxation(a: list[int], T: int, m: int) -> int:
    """max over f : [3m] -> [m] u {skip} of sum_g min(T, sum_{f(i)=g} a_i)."""
    states = {(0,) * m}
    for x in a:
        nxt = set()
        for st in states:
            nxt.add(st)
            for g in range(m):
                nxt.add(st[:g] + (min(st[g] + x, T),) + st[g + 1:])
        states = nxt
    return max(sum(st) for st in states)


def absorbed_hp_of_witness(inst: dict, target_of: list[int]) -> int | None:
    """Play the witness assignment in the simulator; return total absorbed HP."""
    k = len(inst["slots"])
    battle = assemble(inst, list(range(k)))
    initial = initial_enemy_counts(battle)
    assert initial  # enemies present
    pools = {i: s.available() for i, s in enumerate(battle.stacks) if s.side == 1}

    def rec(b, j: int) -> int | None:
        if j == k:
            run_defence(b, inst["variant"])
            return sum(pool - b.stacks[i].available()
                       for i, pool in pools.items())
        atk = b.stacks[j]
        tgt_idx = k + target_of[j]
        tgt = b.stacks[tgt_idx]
        if not tgt.alive():
            return None
        for dest in b.attack_spots(atk, tgt):
            nxt = b.clone()
            nxt.resolve_attack(nxt.stacks[j], nxt.stacks[tgt_idx], dest=dest)
            out = rec(nxt, j + 1)
            if out is not None:
                return out
        return None

    return rec(battle, 0)


def main() -> int:
    rng = random.Random(20260802)
    cases = list(SMALL_CASES)
    cases += balance(gen_instances(rng, 2, 24, ts=[13, 16, 17, 20]), want_no=8)
    cases += balance(gen_instances(rng, 3, 10, ts=[13, 16]), want_no=4)

    seen = set()
    n_yes = n_no = 0
    for a, T in cases:
        key = (tuple(sorted(a)), T)
        if key in seen:
            continue
        seen.add(key)
        m = len(a) // 3
        truth = three_partition_answer(a, T)
        relax = hp_relaxation(a, T, m)
        if (relax == m * T) != truth:
            print(f"FAIL {a} T={T}: hp relaxation {relax}, mT={m*T}, "
                  f"3-PARTITION={truth}")
            return 1
        if truth:
            n_yes += 1
            inst = build(a, T, variant="hold")
            target_of = _solution_assignment(a, T, m)
            absorbed = absorbed_hp_of_witness(inst, target_of)
            if absorbed != m * T:
                print(f"FAIL {a} T={T}: witness absorbed {absorbed} != {m*T}")
                return 1
        else:
            n_no += 1

    # negative control: the relaxation is strictly below m*T on a no-instance,
    # so the equivalence above is not passing vacuously
    a, T = [4, 4, 4, 4, 4, 6], 13
    assert not three_partition_answer(a, T)
    ctrl = hp_relaxation(a, T, 2)
    if ctrl >= 2 * T:
        print(f"FAIL negative control: relaxation {ctrl} >= {2*T}")
        return 1

    print(f"ALL PASS: {n_yes + n_no} instances ({n_yes} yes / {n_no} no); "
          f"hp_relaxation == mT iff 3-PARTITION on every one; witness play "
          f"absorbed exactly mT on every yes-instance; negative control "
          f"{ctrl} < {2*T}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
