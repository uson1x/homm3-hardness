#!/usr/bin/env python3
"""Checks on the instance set and on the optima we recorded.

This is a second opinion on every number the paper will quote, but it shares the
reference battle/search implementation in `solve.py` for exhaustive simulation;
it is not an independent reimplementation of that search path.

  1. Brute force. On every instance whose allocation space is small enough,
     enumerate *all* feasible allocations, simulate each with the reference
     mechanics, and compare the maximum against the recorded optimum.
  2. Knapsack cross-check. On corridor instances, rebuild the 0-1 knapsack of
     candidate-A.md sec. 5.5 and solve it with the pre-existing
     ../../scripts/dp_single_type.py, which was written and self-checked
     independently of anything here.
  3. Reduction fidelity. The recorded optimum must answer the source problem:
     corridor optimum >= W iff the PARTITION instance is a yes-instance, and
     flower optimum >= m iff the 3-PARTITION instance is.
  3b. The fast evaluator. `solve.play_fast` is measured against the exhaustive
     search but is NOT relied on: it misses the movement interaction in both
     directions (an ally can block an approach hex, and a stack that has moved
     frees the hex it left), so it is a bound in neither direction. The
     disagreement rate is reported as a statistic; scoring uses the exhaustive
     search everywhere.
  4. Schema sanity. Slots and enemy hexes are on the board and distinct, every
     referenced creature type exists, damage is flat, R = 1.

Run:  python3 scripts/verify_instances.py [--brute-cap N]
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "scripts"))

import instance as inst_mod  # noqa: E402
import solve  # noqa: E402
from dp_single_type import dp as knapsack_dp  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
INST_DIR = ROOT / "instances"


def count_allocations(inst: dict, cap: int) -> int | None:
    n = 0
    for _ in solve.enumerate_allocations(inst):
        n += 1
        if n > cap:
            return None
    return n


def play_tree_size(inst: dict) -> int:
    """Leaves of the action search for one allocation, in the worst case.

    Each occupied slot chooses a reachable (enemy, approach-hex) pair or passes,
    so the tree is at most prod_j (actions_j + 1). The brute-force check costs
    allocations * this, and it is the second factor that hurts: without counting
    approach destinations a seven-slot instance can look cheap and then run for
    hours. The action widths are measured with all other player slots empty, so
    this remains a deliberately conservative work estimate.
    """

    def action_counts():
        types = inst_mod.creature_types(inst)
        field = inst_mod.battlefield(inst)
        enemies = inst["enemies"]
        out = {}
        for j, hex_ in enumerate(inst["slots"]):
            for name, ct in types.items():
                probe = inst_mod.Stack(ct, 1, side=0, slot=j, hex_=hex_)
                es = [inst_mod.Stack(types[e["type"]], e["count"], side=1,
                                     slot=g, hex_=e["hex"])
                      for g, e in enumerate(enemies)]
                battle = inst_mod.Battle(field, [probe] + es)
                out[(j, name)] = sum(
                    len(battle.attack_spots(probe, target))
                    for target in battle.attackable(probe))
        return out

    actions = inst_mod._cached(inst, "action_counts", action_counts)
    total = 1
    for j in range(inst["size"]):
        widest = max((actions[(j, a["type"])] for a in inst["army"]), default=0)
        total *= widest + 1
    return total


def check_schema(inst: dict) -> list[str]:
    bad = []
    w, h = inst["field"]["width"], inst["field"]["height"]
    size = w * h
    if inst["rounds"] != 1:
        bad.append("rounds != 1")
    if inst["enemy_policy"] != "hold":
        bad.append("unexpected enemy policy")
    if len(inst["slots"]) != inst["size"]:
        bad.append("slot count != size")
    if len(set(inst["slots"])) != len(inst["slots"]):
        bad.append("duplicate slot hexes")
    occupied = list(inst["slots"]) + [e["hex"] for e in inst["enemies"]]
    if len(set(occupied)) != len(occupied):
        bad.append("a slot and an enemy share a hex")
    for x in occupied:
        if not (0 <= x < size):
            bad.append(f"hex {x} off the {w}x{h} board")
    for name, t in inst["types"].items():
        if t["dmg_min"] != t["dmg_max"]:
            bad.append(f"{name}: damage is not flat")
        if t["hp"] <= 0 or t["speed"] < 0:
            bad.append(f"{name}: impossible statistics")
    for a in inst["army"]:
        if a["type"] not in inst["types"]:
            bad.append(f"army references unknown type {a['type']}")
        if a["stock"] <= 0:
            bad.append(f"{a['type']}: non-positive stock")
    for e in inst["enemies"]:
        if e["type"] not in inst["types"]:
            bad.append(f"defence references unknown type {e['type']}")
        if e["count"] <= 0:
            bad.append(f"{e['type']}: non-positive count")
    return bad


def knapsack_crosscheck(inst: dict) -> tuple[int, int] | None:
    """(our optimum via sec. 5.5 items, dp_single_type's answer), or None."""
    if inst["family"] != "corridor-partition":
        return None
    name = inst["army"][0]["type"]
    budget = inst["army"][0]["stock"]
    reach = solve.reach_table(inst)
    targets = [reach[(j, name)] for j in range(inst["size"])]
    if any(len(t) != 1 for t in targets):
        return None
    values, needs = [], []
    for (g,) in targets:
        e = inst["enemies"][g]
        pool = e["count"] * inst["types"][e["type"]]["hp"]
        need = next((c for c in range(1, budget + 1)
                     if solve.damage_of(inst, name, c, g) >= pool), None)
        if need is None:
            continue
        values.append(e["count"] * inst["types"][e["type"]]["value"])
        needs.append(need)
    return knapsack_dp(values, needs, budget), budget


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--brute-cap", type=int, default=60_000,
                    help="max allocations to enumerate per instance")
    ap.add_argument("--work-cap", type=int, default=200_000,
                    help="max allocations * play-tree leaves per instance")
    ap.add_argument("--scan-cap", type=int, default=8_000,
                    help="allocations to scan when reservoir-sampling")
    ap.add_argument("--fast-sample", type=int, default=150,
                    help="allocations per instance to check play_fast against "
                         "the exhaustive search")
    args = ap.parse_args()

    optima = json.loads((INST_DIR / "optima.json").read_text())
    paths = sorted(p for p in INST_DIR.glob("*.json")
                   if p.name not in ("optima.json", "index.json"))

    failures: list[str] = []
    stats = {"schema_ok": 0, "brute_checked": 0, "brute_skipped": 0,
             "fast_checked": 0, "fast_disagreements": 0,
             "instances_with_fast_gap": 0,
             "knapsack_checked": 0, "reduction_checked": 0}
    t0 = time.time()

    for path in paths:
        inst = inst_mod.load(path)
        iid = inst["id"]
        rec = optima[iid]
        opt = rec["optimum"]

        problems = check_schema(inst)
        if problems:
            failures += [f"{iid}: schema: {p}" for p in problems]
        else:
            stats["schema_ok"] += 1

        # 1. brute force over allocations
        tree = play_tree_size(inst)
        n_alloc = count_allocations(inst, args.brute_cap)
        if n_alloc is None:
            # Deliberate cap: report allocation-space skips too, so every
            # omitted brute-force check has a named instance and a reason.
            print(f"  [skip] {iid}: allocation count exceeds cap "
                  f"{args.brute_cap}")
        else:
            estimated_work = n_alloc * tree
            if estimated_work > args.work_cap:
                # Deliberate cap: report the exact instance and estimate so a
                # skipped brute-force check is never mistaken for a silent pass.
                print(f"  [skip] {iid}: estimated {estimated_work} leaves "
                      f"exceeds work cap {args.work_cap}")
                n_alloc = None
        if n_alloc is None:
            stats["brute_skipped"] += 1
        else:
            best = -1
            for raw in solve.enumerate_allocations(inst):
                alloc = inst_mod.normalise_allocation(inst, raw)
                best = max(best, solve.play_optimally(inst, alloc))
            stats["brute_checked"] += 1
            if best != opt:
                failures.append(
                    f"{iid}: brute force {best} != recorded optimum {opt} "
                    f"({n_alloc} allocations)")

        # 1b. the fast evaluator must agree with the exhaustive one on the
        #     allocations the bulk runs will actually feed it
        # reservoir sample, so the check is not confined to the first few
        # allocations the enumerator happens to emit (which all leave slot 0
        # empty and would hide any blocking effect entirely)
        rng = random.Random(f"fast:{iid}")
        # each sampled allocation costs one exhaustive play search, so take
        # fewer of them where that search is wide
        want = max(5, min(args.fast_sample, args.work_cap // max(1, tree)))
        sample: list = []
        for n, raw in enumerate(solve.enumerate_allocations(inst)):
            if n >= args.scan_cap:
                break
            if len(sample) < want:
                sample.append(raw)
            else:
                j = rng.randint(0, n)
                if j < want:
                    sample[j] = raw
        if sample:
            disagreements = solve.verify_fast_evaluator(inst, sample)
            stats["fast_checked"] += len(sample)
            stats["fast_disagreements"] += len(disagreements)
            if disagreements:
                stats["instances_with_fast_gap"] += 1

        # 2. knapsack cross-check against dp_single_type.py
        kc = knapsack_crosscheck(inst)
        if kc is not None:
            stats["knapsack_checked"] += 1
            if kc[0] != opt:
                failures.append(f"{iid}: dp_single_type {kc[0]} != optimum {opt}")

        # 3. the reduction must decide its source problem
        prov = inst["provenance"]
        if inst["family"] == "corridor-partition":
            stats["reduction_checked"] += 1
            game_yes = opt >= prov["decision_target_W"]
            if game_yes != prov["partition_is_yes"]:
                failures.append(
                    f"{iid}: game says {game_yes}, PARTITION says "
                    f"{prov['partition_is_yes']}")
        elif inst["family"] == "flower-3partition":
            stats["reduction_checked"] += 1
            game_yes = opt >= prov["decision_target_W"]
            if game_yes != prov["three_partition_is_yes"]:
                failures.append(
                    f"{iid}: game says {game_yes}, 3-PARTITION says "
                    f"{prov['three_partition_is_yes']}")

    dt = time.time() - t0
    print(f"{len(paths)} instances checked in {dt:.1f}s")
    for k, v in stats.items():
        print(f"  {k:<20} {v}")
    if failures:
        print(f"\nFAILED: {len(failures)} problem(s)")
        for f in failures[:40]:
            print(f"  - {f}")
        return 1
    print("\nALL PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
