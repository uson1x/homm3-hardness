#!/usr/bin/env python3
"""Certify the recorded optima as (‡)-numbers, (‡) = WAIT-then-DEFEND.

History. Review round 5 found that the corpus was generated under
`enemy_policy: "hold"` (the solver skips the enemy's turn entirely) while the
paper's policy (‡) was then "every enemy issues DEFEND at its turn" — and six
recorded optima were unattainable under that policy, because a fast enemy's
DEFEND raised its defence before the player's blow. Review round 6 verified the
repair adopted since: (‡) is now the legal policy

    if the stack has not waited this round, issue WAIT;
    on its postponed activation, issue DEFEND

(candidate-A.md §2.1, paper §2.4). Under it, every enemy's terminal DEFEND
lands in the WAIT phase, after every NORMAL-phase player action, regardless of
relative speed — so an attack-only play delivers exactly what it delivers under
`hold`, while any play's blow is still at most nominal.

This script certifies the WITNESS half of that argument mechanically, instance
by instance: it replays the recorded optimal allocation through the attack-only
play search of solve.py, but in a phase-aware simulation in which every enemy
literally executes (‡) — WAIT at its NORMAL-phase activation, DEFEND (with the
+20 %, floor +1 bonus live in the damage formula) at its postponed WAIT-phase
activation. The best value found must equal the recorded optimum exactly:

  * equality from below is the witness — the recorded optimum is attainable
    under (‡);
  * equality from above must also hold, since a (‡)-play's blows are at most
    nominal and the recorded value is the `hold` optimum of this allocation.

The UPPER half of the sandwich — no play under (‡) beats the recorded optimum
over *all* allocations — is verify_full_model_optima.py's ghost-reach bound,
which dominates every legal play and prices every blow at nominal damage,
hence dominates (‡)-damage too. Together: recorded optimum = (‡)-optimum.

Negative control (--legacy-defend): the same machinery with the OLD policy —
DEFEND at the NORMAL-phase activation, no waiting. This must FAIL, reproducing
the six round-5 violations; a run that passed under both policies would mean
the phase machinery is not actually live. Run from homm3/empirics/:

    python3 scripts/check_defend_policy.py
    python3 scripts/check_defend_policy.py --legacy-defend
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "scripts"))

import instance as inst_mod  # noqa: E402

from homm3_model import Battle  # noqa: E402

ROOT = HERE.parent

# The six instances review round 5 proved unattainable under the old
# immediate-DEFEND policy (each reproduced independently at the time).
# The exact-replay negative control finds these six plus eight sharper ones;
# the total is pinned so the paper's "plus eight more" is generated, not asserted.
LEGACY_TOTAL_EXPECTED = 14

ROUND5_VIOLATIONS = {
    "naturalM-k3-04", "naturalS-k2-05", "naturalS-k5-05",
    "naturalS-k6-01", "naturalS-k7-01", "naturalS-k7-03",
}


def phased_schedule(battle: Battle, legacy: bool) -> list[tuple[int, str]]:
    """Activation order for one round under the scripted defence.

    NORMAL phase: initiative descending (side-then-slot tie rule of the model).
    Under (‡) every enemy waits there, so the schedule appends the WAIT phase:
    enemies in *increasing* speed order (CBattleInfoCallback.cpp:495-519).
    Under --legacy-defend the enemy defends at its NORMAL activation and the
    WAIT phase is empty. Searched player actions never wait in either mode:
    the search covers the attack-only fragment, as solve.py's does.
    """
    entries = [(battle.stacks.index(s), "N") for s in battle.turn_order()]
    if not legacy:
        waiting = sorted((s for s in battle.living() if s.side == 1),
                         key=lambda s: (s.ctype.speed, s.side, s.slot))
        entries += [(battle.stacks.index(s), "W") for s in waiting]
    return entries


def best_under_policy(inst: dict, alloc, legacy: bool) -> int:
    """Max destroyed value over attack-only player plays, defence plays (‡)
    (or the legacy immediate DEFEND). Phase-aware analogue of solve._play."""
    battle, initial = inst_mod.build_battle(inst, alloc)
    entries = phased_schedule(battle, legacy)

    def rec(b: Battle, i: int) -> int:
        if i == len(entries):
            return inst_mod.destroyed_value(b, initial)
        idx, phase = entries[i]
        stack = b.stacks[idx]
        if not stack.alive():
            return rec(b, i + 1)

        if stack.side == 1:
            # Clone before the enemy acts: flag changes must not leak into
            # sibling search branches (cf. test_regressions.py, enemy leak).
            nxt = b.clone()
            st = nxt.stacks[idx]
            nxt.activate(st)
            if legacy:
                nxt.act_defend(st)          # old (‡): DEFEND at the NORMAL turn
            elif phase == "N":
                nxt.act_wait(st)            # (‡): WAIT now ...
            else:
                nxt.act_defend(st)          # ... DEFEND at the postponed turn
            return rec(nxt, i + 1)

        best = rec(b, i + 1)                # pass
        for target in b.attackable(stack):
            t_idx = b.stacks.index(target)
            for dest in b.attack_spots(stack, target):
                nxt = b.clone()
                nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[t_idx], dest=dest)
                best = max(best, rec(nxt, i + 1))
        return best

    return rec(battle, 0)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--legacy-defend", action="store_true",
                    help="negative control: run the OLD policy (DEFEND at the "
                         "NORMAL activation); must reproduce the six round-5 "
                         "violations")
    args = ap.parse_args()

    optima = json.load(open(ROOT / "instances" / "optima.json"))
    files = sorted(p for p in (ROOT / "instances").glob("*.json")
                   if p.name not in ("optima.json", "index.json"))

    mismatches = []
    checked = 0
    t0 = time.time()
    for path in files:
        inst = inst_mod.load(path)
        iid = inst["id"]
        if iid not in optima:
            continue
        if inst["rounds"] != 1:
            print(f"FAIL {iid}: R != 1; the one-round lemma does not apply")
            return 1
        checked += 1
        rec = optima[iid]
        alloc = inst_mod.normalise_allocation(inst, rec["allocation"])
        best = best_under_policy(inst, alloc, legacy=args.legacy_defend)
        if best != rec["optimum"]:
            mismatches.append((iid, rec["optimum"], best))

    dt = time.time() - t0
    label = "legacy DEFEND-at-turn" if args.legacy_defend else "(‡) WAIT-then-DEFEND"
    print(f"instances replayed under {label}: {checked} ({dt:.0f}s)")
    print(f"recorded optimum not reproduced:  {len(mismatches)}")
    for iid, want, got in mismatches:
        print(f"    {iid:18s} recorded {want:6d}  replayed {got:6d}")

    if args.legacy_defend:
        found = {iid for iid, _w, _g in mismatches}
        missing = ROUND5_VIOLATIONS - found
        if missing:
            print(f"\nFAILED negative control: round-5 violations NOT reproduced: "
                  f"{sorted(missing)} — the phase machinery is not biting.")
            return 1
        extra = found - ROUND5_VIOLATIONS
        if extra:
            print(f"  (exact replay also drops below the recorded optimum on "
                  f"{len(extra)} further instance(s): {sorted(extra)} — round 5's "
                  f"bound was generous, so a superset is expected behaviour)")
        # Round 8: the paper's "plus eight more" was prose next to the artifact.
        # Pin the full set, so the sentence is generated by this script and any
        # drift (scorer change, corpus change) fails here instead of in review.
        if len(found) != LEGACY_TOTAL_EXPECTED:
            print(f"\nFAILED negative control: expected exactly "
                  f"{LEGACY_TOTAL_EXPECTED} legacy mismatches "
                  f"({len(ROUND5_VIOLATIONS)} round-5 + "
                  f"{LEGACY_TOTAL_EXPECTED - len(ROUND5_VIOLATIONS)} sharper), "
                  f"got {len(found)}: {sorted(found)}")
            return 1
        print(f"\nNEGATIVE CONTROL OK: the old policy fails exactly where round 5 "
              f"said it must ({len(ROUND5_VIOLATIONS)} violations), plus exactly "
              f"{LEGACY_TOTAL_EXPECTED - len(ROUND5_VIOLATIONS)} more from the "
              f"sharper exact replay; the phase-aware machinery is live.")
        return 0

    if mismatches:
        print("\nFAILED: the recorded optima are not (‡)-numbers.")
        return 1
    if checked != len(optima):
        print(f"\nINCONCLUSIVE: {checked} of {len(optima)} instances replayed.")
        return 1
    print("\nOK: every recorded optimum is attained, and not exceeded, by the "
          "attack-only replay under (‡) = WAIT-then-DEFEND; together with the "
          "ghost upper bound (verify_full_model_optima.py) the recorded optima "
          "ARE the (‡) optima. Coverage complete, 0 skipped.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
