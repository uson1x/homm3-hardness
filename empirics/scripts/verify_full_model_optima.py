#!/usr/bin/env python3
"""Certify the recorded optima for the FULL H3-det action model, WAIT included.

Why this exists (review round 4, finding 4.6). The exact solver's play search
omits WAIT and MOVE-only actions, so `simulated_value` in optima.json is, on its
face, the optimum of a *reduced* action model. The recorded numbers are saved by
a sandwich, which this script closes mechanically:

  lower bound   `simulated_value` is achieved by an explicit allocation in the
                reference simulator; every action it uses is legal in the full
                model, so it is a lower bound on the full-model optimum.

  upper bound   `upper_bound_dp` is sound for the full model *if* its reach
                table dominates every reach any legal play can create. The
                stored table is computed with all other player slots empty but
                every enemy alive, so it misses one full-model effect: a dead
                enemy stops blocking its hex (CBattleInfoCallback.cpp:1355-1360),
                and a stack that acts late (e.g. after WAIT) may walk through.
                This script recomputes the table under the strictly more
                permissive GHOST-ENEMY relaxation: target g is reachable from
                slot j if it can be struck on a board containing nothing but the
                probe and g itself. Whatever a real play does - allies moving or
                vacating, WAITs reordering, enemies dying and opening hexes -
                the blockers at strike time are a superset of {target}, and
                reach is anti-monotone in the blocked set (pinned by
                scripts/test_obstacles.py), so ghost reach dominates. Damage is
                position-independent and at most nominal (a stack that WAITs and
                meets a DEFEND bonus delivers at most nominal, MODEL.md sec. 4/6);
                damage accumulates order-independently in a single pool with
                overkill discarded; the defence never initiates, under the corpus
                policy `hold` and under the paper's (‡) = WAIT-then-DEFEND alike.
                Hence upper_bound_dp over ghost reach >= full-model optimum, under
                either defence; the (‡) witness half lives in
                check_defend_policy.py.

If for every instance the ghost-reach bound equals the recorded optimum, then

  optimum = simulated_value <= full-model optimum <= ghost bound = optimum,

and the recorded optimum is exact for the full action model, WAIT and MOVE-only
included. Run from homm3/empirics/: python3 scripts/verify_full_model_optima.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import instance as inst_mod  # noqa: E402
import solve  # noqa: E402
from homm3_model import Battle, Stack  # noqa: E402

INSTANCE_DIR = Path(__file__).resolve().parent.parent / "instances"


def ghost_reach_table(inst: dict) -> dict[tuple[int, str], tuple[int, ...]]:
    """(slot, type) -> enemies attackable with every OTHER enemy deleted."""
    types = inst_mod.creature_types(inst)
    field = inst_mod.battlefield(inst)
    enemies = inst["enemies"]
    out: dict[tuple[int, str], tuple[int, ...]] = {}
    for j, hex_ in enumerate(inst["slots"]):
        for name, ct in types.items():
            hit = []
            for g, e in enumerate(enemies):
                probe = Stack(ct, 1, side=0, slot=j, hex_=hex_)
                target = Stack(types[e["type"]], e["count"], side=1, slot=g,
                               hex_=e["hex"])
                battle = Battle(field, [probe, target])
                if any(t.slot == g for t in battle.attackable(probe)):
                    hit.append(g)
            out[(j, name)] = tuple(hit)
    return out


def main() -> int:
    optima = json.loads((INSTANCE_DIR / "optima.json").read_text())
    files = sorted(p for p in INSTANCE_DIR.glob("*.json")
                   if p.stem not in ("optima", "index"))
    if len(files) != len(optima):
        print(f"FAIL: {len(files)} instance files vs {len(optima)} optima entries")
        return 1

    unchanged = widened = 0
    failures = []
    for path in files:
        inst = json.loads(path.read_text())
        rec = optima[inst["id"]]
        if not (rec.get("certified")
                and rec["optimum"] == rec["relaxation_bound"] == rec["simulated_value"]):
            failures.append((inst["id"], "recorded optimum is not sandwiched"))
            continue
        if inst.get("enemy_policy") != "hold":
            failures.append((inst["id"], f"policy {inst.get('enemy_policy')!r}"))
            continue

        stored = solve.reach_table(inst)
        ghost = ghost_reach_table(inst)
        for key in stored:
            if not set(stored[key]) <= set(ghost[key]):
                failures.append((inst["id"], f"ghost reach lost targets at {key}"))
        if ghost == stored:
            unchanged += 1
        else:
            widened += 1
        # Round 9 (fable S7): the DP bound is recomputed for EVERY instance.
        # The old shortcut inferred "identical reach table -> identical DP ->
        # the recorded bound already is the ghost bound" and skipped the DP —
        # sound, but it meant `upper_bound_dp` never actually ran here, and
        # 60 of the 145 recorded bounds were produced by a different method
        # ("knapsack") in the first place. The full re-derivation costs ~24 s.
        fresh = json.loads(path.read_text())
        fresh[inst_mod.CACHE_KEY] = {"reach": ghost}
        try:
            bound, _alloc = solve.upper_bound_dp(fresh)
        except solve.SearchTooLarge:
            bound, _alloc = solve.upper_bound_dp(fresh, state_cap=8_000_000)
        if bound != rec["optimum"]:
            failures.append(
                (inst["id"],
                 f"ghost bound {bound} != recorded optimum {rec['optimum']}"))

    print(f"instances: {len(files)}; ghost reach identical: {unchanged}; "
          f"widened: {widened}; ghost bound recomputed by upper_bound_dp "
          f"for every instance; failures: {len(failures)}")
    for iid, why in failures:
        print(f"  FAIL {iid}: {why}")
    if failures:
        print("NOT CERTIFIED for the full action model")
        return 1
    print("ALL PASS: every recorded optimum is exact over the full H3-det action "
          "model (WAIT and MOVE-only included), by the sandwich above, under the\n"
          "corpus's scripted defence `hold`. The paper's policy (‡) is now\n"
          "WAIT-then-DEFEND, whose blows are at most nominal and whose reach this\n"
          "ghost bound dominates, so the bound is an upper bound under (‡) as well;\n"
          "run check_defend_policy.py for the witness half — the phase-aware replay\n"
          "that certifies every recorded optimum as attainable, and not exceedable,\n"
          "under (‡).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
