#!/usr/bin/env python3
"""Baseline allocation policies, and the harness that scores them.

What is being measured
----------------------
Only the *allocation* is the policy's decision. Once the allocation is fixed,
the battle itself is played optimally by exhaustive search (solve.play_optimally).
That split is deliberate: the paper's claim is about the pre-battle sizing
decision, so a baseline must not be penalised for tactical play it never made.
It also makes the comparison generous to the baselines and to the LLMs, which is
the right direction for a claim of the form "even so, they fall short".

The policies
------------
random          For each type, pick a random number of slots and split the stock
                into a random composition over them. Reported as the mean over
                `--samples` draws, so it estimates what a policy with no idea
                what it is doing achieves. This is the floor.

even-split      Spread each type's stock evenly over its slots. The natural
                "use all seven slots" instinct, and the thing the game's own UI
                nudges you towards when you split a stack.

one-big-stack   Each type goes into exactly one slot, undivided. This is what
                most HoMM3 players actually do most of the time, because merging
                is the default and splitting takes deliberate clicks.

greedy-density  Classic knapsack greedy: order the available kills by
                value-per-creature and take them while the stock lasts.

greedy-cheapest The folklore heuristic. A player scans the enemy line, works out
                "that one I can finish with five, that one would take twelve",
                and banks the cheap kills first. It is greedy by weight rather
                than by density. We single it out because it is what the game
                teaches: the value of a blow is the kill, not the damage
                (candidate-A.md sec. 5.1-5.2), so players learn to count
                "how many do I need to finish this stack" and to spend the
                smallest sufficient amount. It is also the heuristic most likely
                to look right and be wrong, which is exactly what we want to
                measure.

greedy-value    Kill the most valuable stack you can afford first. The other
                half of the folklore ("take out their best unit"), and a useful
                contrast with greedy-cheapest.

focus-fire      Concentrate several slots on one enemy until the kill threshold
                is crossed, then move on (best value per creature spent first).
                The strongest heuristic here and the fairest reference point
                for the LLM comparison; see policy_focus_fire below.

Run:  python3 scripts/baselines.py [--samples 100] [--seed N]
"""

from __future__ import annotations

import argparse
import json
import random
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import instance as inst_mod  # noqa: E402
import solve  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
INST_DIR = ROOT / "instances"
RESULTS = ROOT / "results"


# --- helpers ---------------------------------------------------------------


def kill_options(inst: dict) -> list[dict]:
    """Every (slot, type, enemy) triple with the stack size that wipes it.

    `need` is the smallest count of `type` that destroys enemy `enemy` in one
    blow from `slot`; None when no affordable count does.
    """
    reach = solve.reach_table(inst)
    stock = {a["type"]: a["stock"] for a in inst["army"]}
    out = []
    for j in range(inst["size"]):
        for name, cap in stock.items():
            for g in reach[(j, name)]:
                e = inst["enemies"][g]
                pool = e["count"] * inst["types"][e["type"]]["hp"]
                need = next((c for c in range(1, cap + 1)
                             if solve.damage_of(inst, name, c, g) >= pool), None)
                if need is None:
                    continue
                value = e["count"] * inst["types"][e["type"]]["value"]
                out.append({"slot": j, "type": name, "enemy": g,
                            "need": need, "value": value})
    return out


def empty_allocation(inst: dict) -> list:
    return [None] * inst["size"]


def random_composition(rng: random.Random, total: int, parts: int) -> list[int]:
    """Split `total` into `parts` non-negative integers, uniformly."""
    if parts <= 1:
        return [total]
    cuts = sorted(rng.randint(0, total) for _ in range(parts - 1))
    out, prev = [], 0
    for c in cuts:
        out.append(c - prev)
        prev = c
    out.append(total - prev)
    return out


# --- policies --------------------------------------------------------------


def policy_random(inst: dict, rng: random.Random) -> list:
    alloc = empty_allocation(inst)
    free = list(range(inst["size"]))
    rng.shuffle(free)
    for a in inst["army"]:
        if not free:
            break
        # never spread a type over more slots than it has creatures: with a
        # stock of one that would burn slots on empty stacks and make the floor
        # artificially low rather than merely uninformed
        n_slots = rng.randint(1, min(len(free), a["stock"]))
        chosen = [free.pop() for _ in range(n_slots)]
        for slot, c in zip(chosen, random_composition(rng, a["stock"], n_slots)):
            if c > 0:
                alloc[slot] = [a["type"], c]
    return alloc


def policy_even_split(inst: dict) -> list:
    alloc = empty_allocation(inst)
    k = inst["size"]
    army = inst["army"]
    # round-robin: type i owns slots i, i+T, i+2T, ...
    for i, a in enumerate(army):
        mine = list(range(i, k, len(army)))
        if not mine:
            continue
        base, extra = divmod(a["stock"], len(mine))
        for n, slot in enumerate(mine):
            c = base + (1 if n < extra else 0)
            if c > 0:
                alloc[slot] = [a["type"], c]
    return alloc


def policy_one_big_stack(inst: dict) -> list:
    alloc = empty_allocation(inst)
    for i, a in enumerate(inst["army"]):
        if i >= inst["size"]:
            break
        alloc[i] = [a["type"], a["stock"]]
    return alloc


def _greedy(inst: dict, key) -> list:
    """Take kills in the order `key` gives, while stock and slots last."""
    alloc = empty_allocation(inst)
    left = {a["type"]: a["stock"] for a in inst["army"]}
    used_slots: set[int] = set()
    dead: set[int] = set()

    for opt in sorted(kill_options(inst), key=key):
        if opt["slot"] in used_slots or opt["enemy"] in dead:
            continue
        if left[opt["type"]] < opt["need"]:
            continue
        alloc[opt["slot"]] = [opt["type"], opt["need"]]
        left[opt["type"]] -= opt["need"]
        used_slots.add(opt["slot"])
        dead.add(opt["enemy"])

    # Leftovers go where they can still do damage, rather than staying home:
    # the best remaining (slot, type, enemy) by raw damage.
    reach = solve.reach_table(inst)
    for name, remaining in left.items():
        if remaining <= 0:
            continue
        best = None
        for j in range(inst["size"]):
            if j in used_slots:
                continue
            for g in reach[(j, name)]:
                if g in dead:
                    continue
                d = solve.damage_of(inst, name, remaining, g)
                score = (d, inst["types"][inst["enemies"][g]["type"]]["value"])
                if best is None or score > best[0]:
                    best = (score, j)
        if best is not None:
            alloc[best[1]] = [name, remaining]
            used_slots.add(best[1])
    return alloc


def policy_greedy_density(inst: dict) -> list:
    return _greedy(inst, key=lambda o: (-(o["value"] / o["need"]), o["need"]))


def policy_greedy_cheapest(inst: dict) -> list:
    return _greedy(inst, key=lambda o: (o["need"], -o["value"]))


def policy_greedy_value(inst: dict) -> list:
    return _greedy(inst, key=lambda o: (-o["value"], o["need"]))


def policy_focus_fire(inst: dict) -> list:
    """Concentrate whatever it takes on one enemy, finish it, move on.

    The single-slot greedies above cannot express "three stacks gang up on one
    target", which is the first thing a HoMM3 player learns and the exact
    structure Theorem 2 exploits. This policy can: it picks the enemy with the
    best value per creature spent, then pours slots into it until the kill
    threshold is crossed, and repeats on what is left.

    It is the strongest heuristic here and the fairest reference point for the
    LLM comparison, because it is the one that has the right *shape* and can
    still get the arithmetic wrong.
    """
    reach = solve.reach_table(inst)
    alloc = empty_allocation(inst)
    left = {a["type"]: a["stock"] for a in inst["army"]}
    free = set(range(inst["size"]))
    dead: set[int] = set()

    while True:
        best = None
        for g, e in enumerate(inst["enemies"]):
            if g in dead:
                continue
            pool = e["count"] * inst["types"][e["type"]]["hp"]
            value = e["count"] * inst["types"][e["type"]]["value"]
            if value <= 0:
                continue
            # Build the plan against a local copy of the stock: a type committed
            # to one slot of this plan is no longer available to the next, or the
            # plan would spend the same creatures twice and come out illegal.
            avail = dict(left)
            plan, spent, damage = [], 0, 0
            used_slots: set[int] = set()
            while damage < pool:
                # hardest-hitting (slot, type) still available for this target
                pick = None
                for j in sorted(free - used_slots):
                    for name, remaining in avail.items():
                        if remaining <= 0 or g not in reach[(j, name)]:
                            continue
                        per = solve.damage_of(inst, name, 1, g)
                        if pick is None or per > pick[0]:
                            pick = (per, j, name, remaining)
                if pick is None:
                    break
                _per, j, name, remaining = pick
                need = next((c for c in range(1, remaining + 1)
                             if damage + solve.damage_of(inst, name, c, g) >= pool),
                            None)
                take = need if need is not None else remaining
                damage += solve.damage_of(inst, name, take, g)
                avail[name] -= take
                plan.append((j, name, take))
                used_slots.add(j)
                spent += take
            if damage >= pool and spent > 0:
                score = value / spent
                if best is None or score > best[0]:
                    best = (score, g, plan)
        if best is None:
            break
        _score, g, plan = best
        for j, name, take in plan:
            alloc[j] = [name, take]
            left[name] -= take
            free.discard(j)
        dead.add(g)

    # anything still in reserve goes wherever it does the most damage
    for name, remaining in left.items():
        if remaining <= 0:
            continue
        best = None
        for j in sorted(free):
            for g in reach[(j, name)]:
                if g in dead:
                    continue
                d = solve.damage_of(inst, name, remaining, g)
                if best is None or d > best[0]:
                    best = (d, j)
        if best is not None:
            alloc[best[1]] = [name, remaining]
            free.discard(best[1])
    return alloc


DETERMINISTIC = {
    "even-split": policy_even_split,
    "one-big-stack": policy_one_big_stack,
    "greedy-density": policy_greedy_density,
    "greedy-cheapest": policy_greedy_cheapest,
    "greedy-value": policy_greedy_value,
    "focus-fire": policy_focus_fire,
}


# --- scoring ---------------------------------------------------------------


def score(inst: dict, alloc: list, who: str) -> tuple[int, bool]:
    """A baseline emitting an illegal allocation is a bug in the baseline.

    Scoring it as 0 like an LLM answer would quietly bury the mistake in the
    averages, so it is raised instead.
    """
    res = inst_mod.evaluate(inst, alloc)
    if not res["legal"]:
        raise AssertionError(
            f"policy {who} produced an illegal allocation on {inst['id']}: "
            f"{res['reason']}  ({alloc})")
    return res["value"], res["legal"]


def run(samples: int, seed: int) -> dict:
    optima = json.loads((INST_DIR / "optima.json").read_text())
    paths = sorted(p for p in INST_DIR.glob("*.json")
                   if p.name not in ("optima.json", "index.json"))

    per_instance: dict[str, dict] = {}
    for path in paths:
        inst = inst_mod.load(path)
        iid = inst["id"]
        opt = optima[iid]["optimum"]
        row = {"family": inst["family"], "size": inst["size"], "optimum": opt,
               "max_enemy_value": optima[iid]["max_enemy_value"], "policies": {}}

        for name, fn in DETERMINISTIC.items():
            value, legal = score(inst, fn(inst), name)
            row["policies"][name] = {"value": value, "ratio": value / opt,
                                     "exact": value == opt, "legal": legal}

        rng = random.Random(f"{seed}:{iid}")
        vals = [score(inst, policy_random(inst, rng), "random")[0]
                for _ in range(samples)]
        row["policies"]["random"] = {
            "value": statistics.mean(vals),
            "ratio": statistics.mean(vals) / opt,
            "exact": sum(v == opt for v in vals) / len(vals),
            "best_of_n": max(vals) / opt,
            "legal": True,
        }
        per_instance[iid] = row
    return per_instance


def aggregate(per_instance: dict) -> dict:
    names = list(DETERMINISTIC) + ["random"]

    def summarise(rows: list[dict]) -> dict:
        out = {}
        for name in names:
            ratios = [r["policies"][name]["ratio"] for r in rows]
            exacts = [r["policies"][name]["exact"] for r in rows]
            out[name] = {
                "n": len(rows),
                "mean_ratio": round(statistics.mean(ratios), 4),
                "median_ratio": round(statistics.median(ratios), 4),
                "min_ratio": round(min(ratios), 4),
                "exact_rate": round(statistics.mean(
                    [float(e) for e in exacts]), 4),
                # how often the policy leaves more than a tenth of the optimum
                # on the table: the mean ratio hides this, because partial
                # credit is easy to come by and total failure is rare
                "below_90_rate": round(
                    sum(r < 0.9 for r in ratios) / len(ratios), 4),
            }
        best = [r["policies"]["random"].get("best_of_n") for r in rows]
        if all(b is not None for b in best):
            out["random"]["best_of_n_mean"] = round(statistics.mean(best), 4)
        return out

    rows = list(per_instance.values())
    agg = {"overall": summarise(rows), "by_family": {}, "by_size": {},
           "by_family_size": {}}
    for fam in sorted({r["family"] for r in rows}):
        agg["by_family"][fam] = summarise([r for r in rows if r["family"] == fam])
    for size in sorted({r["size"] for r in rows}):
        agg["by_size"][str(size)] = summarise([r for r in rows if r["size"] == size])
    for fam in sorted({r["family"] for r in rows}):
        for size in sorted({r["size"] for r in rows if r["family"] == fam}):
            sub = [r for r in rows if r["family"] == fam and r["size"] == size]
            agg["by_family_size"][f"{fam}/k={size}"] = summarise(sub)
    return agg


def print_table(agg: dict) -> None:
    names = list(DETERMINISTIC) + ["random"]
    for title, block in (("OVERALL", {"all": agg["overall"]}),
                         ("BY FAMILY", agg["by_family"]),
                         ("BY SIZE (k)", agg["by_size"])):
        print(f"\n{title}")
        print(f"  {'group':<22} {'policy':<16} {'n':>4} {'mean':>7} "
              f"{'median':>7} {'min':>7} {'exact':>7}")
        for group, summary in block.items():
            for name in names:
                s = summary[name]
                print(f"  {group:<22} {name:<16} {s['n']:>4} "
                      f"{s['mean_ratio']:>7.3f} {s['median_ratio']:>7.3f} "
                      f"{s['min_ratio']:>7.3f} {s['exact_rate']:>7.3f}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=100)
    ap.add_argument("--seed", type=int, default=20260801)
    args = ap.parse_args()

    per_instance = run(args.samples, args.seed)
    agg = aggregate(per_instance)
    print_table(agg)

    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "baselines.json").write_text(json.dumps({
        "seed": args.seed,
        "random_samples": args.samples,
        "note": "ratio = value achieved / certified optimum; "
                "play is resolved optimally once the allocation is fixed",
        "aggregate": agg,
        "per_instance": per_instance,
    }, indent=1) + "\n")
    print(f"\n-> {RESULTS / 'baselines.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
