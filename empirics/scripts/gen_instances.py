#!/usr/bin/env python3
"""Generate the instance set for the ARMY-ALLOCATION empirics.

Four families, two purposes.

*Reduction* families are the constructions of proofs/candidate-A.md, at sizes
small enough to solve exactly. They are the instances the theorems are about, so
an agent that does badly on them is doing badly on the thing we proved hard.

    corridor-partition   Theorem 1: one creature type, one row, slot j reaches
                         exactly enemy j. Encodes PARTITION.
    flower-3partition    Theorem 2: 3m types of stock one, three rows, three
                         slots per enemy. Encodes 3-PARTITION.

*Natural* families exist to answer the obvious objection to the above — that the
instances were built backwards from a reduction and no one would ever meet them.
They use:

    - the shipped 11x17 battlefield (BattleHex.h:19-24),
    - shipped deployment hexes, taken verbatim from the `creatureBankNarrow`
      layout in config/gameConfig.json:672-679,
    - shipped creature statistics, read out of the original CRTRAITS.TXT by
      scripts/extract_creatures.py,
    - shipped AI values as the per-creature objective weights,
    - and the rules of MODEL.md unchanged.

Nothing about them is built backwards from PARTITION. The only modelling choice
is the one MODEL.md sec. 4 already requires: damage must be flat, so a creature's
roll is fixed at `dmg_min`. Two shipped creatures (Angel, Peasant) already
satisfy `dmg_min == dmg_max` and need no projection at all; instances built only
from those are marked `damage_projection: "native"` and act as a control.

Double-wide creatures and shooters are excluded because the reference simulator
implements neither (MODEL.md sec. 7); including them would mean reporting numbers
the model cannot stand behind.

Usage:  python3 scripts/gen_instances.py [--seed N] [--out instances/]
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import instance as inst_mod  # noqa: E402
import solve  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data" / "creatures_h3.json"

# candidate-A.md sec. 2 constants
ALPHA = 10
PLAYER_HP = 5
PLAYER_SPEED = 2
ENEMY_SPEED = 1

# config/gameConfig.json:672-679, layout "creatureBankNarrow"
BANK_ATTACKER_HEXES = [57, 61, 90, 93, 96, 125, 129]
BANK_DEFENDER_HEXES = [15, 185, 172, 2, 100, 87, 8]
# lib/battle/BattleHex.h:19-24
FIELD_W, FIELD_H = 17, 11


def ctype(name, *, attack, defense, dmg, hp, speed, value=0):
    return {"attack": attack, "defense": defense, "dmg_min": dmg, "dmg_max": dmg,
            "hp": hp, "speed": speed, "value": value, "shooter": False}


# =========================================================================
# Reduction family 1: PARTITION corridor  (candidate-A.md sec. 3.1)
# =========================================================================


def partition_answer(a: list[int]) -> bool:
    target = sum(a) // 2
    reachable = {0}
    for x in a:
        reachable |= {r + x for r in reachable}
    return target in reachable


def build_corridor(a: list[int], seed: int, idx: int) -> dict:
    n = len(a)
    B = sum(a) // 2
    types = {"C": ctype("C", attack=ALPHA, defense=ALPHA, dmg=1,
                        hp=PLAYER_HP, speed=PLAYER_SPEED)}
    enemies = []
    for j, aj in enumerate(a):
        types[f"E{j}"] = ctype(f"E{j}", attack=ALPHA, defense=ALPHA, dmg=1,
                               hp=aj, speed=ENEMY_SPEED, value=aj)
        enemies.append({"type": f"E{j}", "count": 1, "hex": 5 * j + 1})
    return {
        "id": f"corridor-k{n}-{idx:03d}",
        "family": "corridor-partition",
        "size": n,
        "seed": seed,
        "field": {"width": 5 * n, "height": 1, "obstacles": []},
        "rounds": 1,
        "enemy_policy": "hold",
        "types": types,
        "army": [{"type": "C", "stock": B}],
        "slots": [5 * j for j in range(n)],
        "enemies": enemies,
        "provenance": {
            "construction": "proofs/candidate-A.md sec. 3.1 (Theorem 1, PARTITION)",
            "partition_items": a,
            "partition_target": B,
            "partition_is_yes": partition_answer(a),
            "decision_target_W": B,
        },
    }


# =========================================================================
# Reduction family 2: 3-PARTITION flower  (candidate-A.md sec. 4.1)
# =========================================================================


def three_partition_answer(a: list[int], T: int) -> bool:
    import itertools

    def rec(remaining: tuple) -> bool:
        if not remaining:
            return True
        first, rest = remaining[0], remaining[1:]
        for pair in itertools.combinations(rest, 2):
            if a[first] + a[pair[0]] + a[pair[1]] != T:
                continue
            nxt = tuple(x for x in rest if x not in pair)
            if rec(nxt):
                return True
        return False

    return rec(tuple(range(len(a))))


def build_flower(a: list[int], T: int, seed: int, idx: int) -> dict:
    m = len(a) // 3
    width = 8 * m + 2

    def hexi(x, y):
        return x + y * width

    types = {}
    for i, ai in enumerate(a):
        types[f"C{i}"] = ctype(f"C{i}", attack=ALPHA, defense=ALPHA, dmg=ai,
                               hp=PLAYER_HP, speed=PLAYER_SPEED)
    slots, enemies = [], []
    for g in range(m):
        X = 8 * g + 1
        slots += [hexi(X - 1, 1), hexi(X, 0), hexi(X, 2)]
        types[f"E{g}"] = ctype(f"E{g}", attack=ALPHA, defense=ALPHA, dmg=1,
                               hp=T, speed=ENEMY_SPEED, value=1)
        enemies.append({"type": f"E{g}", "count": 1, "hex": hexi(X, 1)})
    return {
        "id": f"flower-k{3 * m}-{idx:03d}",
        "family": "flower-3partition",
        "size": 3 * m,
        "seed": seed,
        "field": {"width": width, "height": 3, "obstacles": []},
        "rounds": 1,
        "enemy_policy": "hold",
        "types": types,
        "army": [{"type": f"C{i}", "stock": 1} for i in range(len(a))],
        "slots": slots,
        "enemies": enemies,
        "provenance": {
            "construction": "proofs/candidate-A.md sec. 4.1 (Theorem 2, 3-PARTITION)",
            "items": a,
            "T": T,
            "three_partition_is_yes": three_partition_answer(a, T),
            "decision_target_W": m,
        },
    }


def gen_3partition_items(rng: random.Random, m: int, want: int):
    out, seen, tries = [], set(), 0
    while len(out) < want and tries < 50_000:
        tries += 1
        T = rng.choice([20, 24, 28])
        lo, hi = T // 4 + 1, (T - 1) // 2
        a = [rng.randint(lo, hi) for _ in range(3 * m)]
        diff = m * T - sum(a)
        if not (lo <= a[-1] + diff <= hi):
            continue
        a[-1] += diff
        key = (tuple(sorted(a)), T)
        if key in seen:
            continue
        seen.add(key)
        out.append((a, T))
    return out


# =========================================================================
# Natural families: shipped board, shipped hexes, shipped creatures
# =========================================================================


def load_roster() -> list[dict]:
    """Shipped creatures the reference simulator can represent faithfully."""
    data = json.loads(DATA.read_text())
    return [c for c in data["creatures"]
            if not c["shooter"] and not c["doubleWide"]
            and c["hp"] > 0 and c["speed"] > 0 and c["dmg_min"] > 0]


def as_type(c: dict) -> dict:
    """Shipped statistics, damage fixed at dmg_min (MODEL.md sec. 4)."""
    return {"attack": c["attack"], "defense": c["defense"],
            "dmg_min": c["dmg_min"], "dmg_max": c["dmg_min"],
            "hp": c["hp"], "speed": c["speed"], "value": c["aiValue"],
            "shooter": False}


def counts_to_kill(inst: dict, type_name: str, enemy_index: int, cap: int) -> int | None:
    """Smallest stack of `type_name` that wipes enemy `enemy_index` in one blow."""
    e = inst["enemies"][enemy_index]
    pool = e["count"] * inst["types"][e["type"]]["hp"]
    for c in range(1, cap + 1):
        if solve.damage_of(inst, type_name, c, enemy_index) >= pool:
            return c
    return None


def build_natural(rng: random.Random, k: int, n_types: int, roster: list[dict],
                  idx: int, seed: int) -> dict | None:
    """One natural instance, or None if it came out degenerate."""
    picks = rng.sample(roster, n_types)
    enemy_picks = rng.sample(roster, rng.randint(2, 4))

    types: dict[str, dict] = {}
    army = []
    for c in picks:
        types[c["singular"]] = as_type(c)
        army.append({"type": c["singular"], "stock": 1})   # stock fixed below

    enemies = []
    hexes = rng.sample(BANK_DEFENDER_HEXES, len(enemy_picks))
    for c, h in zip(enemy_picks, hexes):
        types.setdefault(c["singular"], as_type(c))
        enemies.append({"type": c["singular"], "count": rng.randint(1, 5), "hex": h})

    native = all(c["dmg_min"] == c["dmg_max"] for c in picks + enemy_picks)
    inst = {
        "id": f"natural{'M' if n_types > 1 else 'S'}-k{k}-{idx:03d}",
        "family": "natural-multi" if n_types > 1 else "natural-single",
        "size": k,
        "seed": seed,
        "field": {"width": FIELD_W, "height": FIELD_H, "obstacles": []},
        "rounds": 1,
        "enemy_policy": "hold",
        "types": types,
        "army": army,
        "slots": BANK_ATTACKER_HEXES[:k],
        "enemies": enemies,
        "provenance": {
            "layout": "config/gameConfig.json:672-679 creatureBankNarrow",
            "creature_source": "DATA/CRTRAITS.TXT via scripts/extract_creatures.py",
            "damage_projection": "native" if native else "min",
            "player_types": [c["singular"] for c in picks],
        },
    }

    # Budget: enough to wipe part of the defence but not all of it, so the
    # instance is a real trade-off rather than "kill everything" or "kill nothing".
    needs = []
    for g in range(len(enemies)):
        best = None
        for name in [c["singular"] for c in picks]:
            n = counts_to_kill(inst, name, g, 40)
            if n is not None and (best is None or n < best):
                best = n
        if best is not None:
            needs.append(best)
    if len(needs) < 2:
        return None
    total_need = sum(needs)
    budget = int(total_need * rng.uniform(0.35, 0.75))
    if budget < 2 or budget > 26:
        return None

    if n_types == 1:
        army[0]["stock"] = budget
    else:
        share = max(1, budget // n_types)
        for a in army:
            a["stock"] = share
    inst_mod.invalidate(inst)
    return inst


# =========================================================================
# Solving and filtering
# =========================================================================


def solve_corridor(inst: dict) -> dict:
    """Corridor instances go through the O(k*B) knapsack of sec. 5.5.

    The generic DP would have to carry one damage coordinate per enemy and blows
    up here; the knapsack is exact for this structure and is what the paper
    claims. We still verify the value is achievable in the simulator.
    """
    name = inst["army"][0]["type"]
    budget = inst["army"][0]["stock"]
    reach = solve.reach_table(inst)
    targets = [reach[(j, name)] for j in range(inst["size"])]
    assert all(len(t) == 1 for t in targets), "corridor geometry broken"
    assert len(set(t[0] for t in targets)) == len(targets), "slots share an enemy"

    items = []
    for j, (g,) in enumerate(targets):
        need = counts_to_kill(inst, name, g, budget)
        if need is None:
            continue
        e = inst["enemies"][g]
        items.append((j, need, e["count"] * inst["types"][e["type"]]["value"]))

    best = [0] * (budget + 1)
    take: list[list[int]] = [[] for _ in range(budget + 1)]
    for j, need, val in items:
        for cap in range(budget, need - 1, -1):
            cand = best[cap - need] + val
            if cand > best[cap]:
                best[cap] = cand
                take[cap] = take[cap - need] + [j]
    chosen = take[budget]

    alloc_raw: list = [None] * inst["size"]
    for j, need, _val in items:
        if j in chosen:
            alloc_raw[j] = [name, need]
    alloc = inst_mod.normalise_allocation(inst, alloc_raw)
    inst_mod.check_feasible(inst, alloc)
    achieved = solve.play_optimally(inst, alloc)
    return {
        "optimum": achieved if achieved == best[budget] else None,
        "relaxation_bound": best[budget],
        "simulated_value": achieved,
        "certified": achieved == best[budget],
        "allocation": alloc_raw,
        "max_enemy_value": inst_mod.max_enemy_value(inst),
        "blocking_free": True,
        "method": "knapsack (candidate-A.md sec. 5.5)",
    }


def is_interesting(inst: dict, res: dict) -> bool:
    """Reject natural instances whose answer is 'everything' or 'nothing'.

    Reduction instances are exempt: in a 3-PARTITION yes-instance the optimum
    *is* the whole defence, and dropping those would leave only no-instances.
    """
    if inst["family"] in ("corridor-partition", "flower-3partition"):
        return res["optimum"] > 0
    return 0 < res["optimum"] < res["max_enemy_value"]


# =========================================================================
# Driver
# =========================================================================


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260801)
    ap.add_argument("--out", default=str(ROOT / "instances"))
    args = ap.parse_args()

    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    roster = load_roster()

    instances: list[dict] = []
    optima: dict[str, dict] = {}
    drops = {"too_large": 0, "uncertified": 0, "degenerate": 0}

    def keep(inst: dict) -> bool:
        try:
            if inst["family"] == "corridor-partition":
                res = solve_corridor(inst)
            else:
                res = solve.exact_optimum(inst)
        except solve.SearchTooLarge:
            drops["too_large"] += 1
            return False
        if not res["certified"]:
            drops["uncertified"] += 1
            return False
        if not is_interesting(inst, res):
            drops["degenerate"] += 1
            return False
        instances.append(inst)
        optima[inst["id"]] = res
        return True

    # ---- corridor / PARTITION: k = 2..7, both answers -------------------
    print("corridor-partition ...", flush=True)
    for k in range(2, 8):
        made = {True: 0, False: 0}
        want = 5
        tries = 0
        while min(made.values()) < want and tries < 4000:
            tries += 1
            a = sorted(rng.randint(1, 9) for _ in range(k))
            if sum(a) % 2:
                continue
            ans = partition_answer(a)
            if made[ans] >= want:
                continue
            inst = build_corridor(a, args.seed, made[True] + made[False])
            inst["id"] = f"corridor-k{k}-{'y' if ans else 'n'}{made[ans]:02d}"
            if keep(inst):
                made[ans] += 1
        print(f"  k={k}: {made[True]} yes, {made[False]} no")

    # ---- flower / 3-PARTITION: m = 1, 2 ---------------------------------
    print("flower-3partition ...", flush=True)
    for m in (1, 2):
        made = {True: 0, False: 0}
        want = 5 if m == 2 else 3
        for a, T in gen_3partition_items(rng, m, 600):
            ans = three_partition_answer(a, T)
            if made[ans] >= want:
                continue
            inst = build_flower(a, T, args.seed, made[True] + made[False])
            inst["id"] = f"flower-k{3 * m}-{'y' if ans else 'n'}{made[ans]:02d}"
            if keep(inst):
                made[ans] += 1
            if min(made.values()) >= want:
                break
        print(f"  m={m}: {made[True]} yes, {made[False]} no")

    # ---- natural: single type, k = 2..7 ---------------------------------
    print("natural-single ...", flush=True)
    for k in range(2, 8):
        made, tries = 0, 0
        while made < 6 and tries < 400:
            tries += 1
            inst = build_natural(rng, k, 1, roster, made, args.seed)
            if inst is None:
                continue
            inst["id"] = f"naturalS-k{k}-{made:02d}"
            if keep(inst):
                made += 1
        print(f"  k={k}: {made}")

    # ---- natural: 2-4 types, k = 2..7 -----------------------------------
    print("natural-multi ...", flush=True)
    for k in range(2, 8):
        made, tries = 0, 0
        while made < 6 and tries < 400:
            tries += 1
            n_types = rng.randint(2, min(4, max(2, k)))
            inst = build_natural(rng, k, n_types, roster, made, args.seed)
            if inst is None:
                continue
            inst["id"] = f"naturalM-k{k}-{made:02d}"
            if keep(inst):
                made += 1
        print(f"  k={k}: {made}")

    # ---- write ----------------------------------------------------------
    for inst in instances:
        (out_dir / f"{inst['id']}.json").write_text(
            inst_mod.dumps(inst, indent=1, ensure_ascii=False) + "\n")
    (out_dir / "optima.json").write_text(
        json.dumps(optima, indent=1, ensure_ascii=False) + "\n")
    index = {
        "seed": args.seed,
        "count": len(instances),
        "by_family": {},
        "instances": [
            {"id": i["id"], "family": i["family"], "size": i["size"],
             "optimum": optima[i["id"]]["optimum"],
             "max_enemy_value": optima[i["id"]]["max_enemy_value"]}
            for i in instances
        ],
    }
    for i in instances:
        index["by_family"][i["family"]] = index["by_family"].get(i["family"], 0) + 1
    (out_dir / "index.json").write_text(
        json.dumps(index, indent=1, ensure_ascii=False) + "\n")

    print(f"\n{len(instances)} instances -> {out_dir}")
    for fam, n in index["by_family"].items():
        print(f"  {fam:<22} {n}")
    print(f"  rejected: {drops}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
