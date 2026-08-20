#!/usr/bin/env python3
"""Exact optimum for ARMY-ALLOCATION instances, with a certificate.

Two independent routines, and the point is that they meet:

`upper_bound_dp` is a relaxation. It ignores every geometric interaction between
player stacks (an ally standing in the way, or a stack that has moved into
contact and now blocks the only free approach hex), so it can only ever
*overstate* what the player can do. It is a dynamic program over
(slots processed, stock left, damage dealt to each enemy).

`play_optimally` hands a fixed allocation to the reference simulator in
../../scripts/homm3_model.py and searches every **attack-only** play: each stack
either passes or performs WALK_AND_ATTACK, branching over targets and over every
legal approach hex. It does *not* branch over pure movement, WAIT or DEFEND, so
it is not exhaustive over the full model. Do not describe it as searching every
legal action sequence; an earlier version of this docstring did, and it was wrong.

That restriction costs nothing for anything this project reports, but the reason
is an argument, and it is checked rather than asserted, in two places:
`verify_full_model_optima.py` certifies the 145 recorded optima against a
ghost-enemy relaxation that dominates every full-model play, and
`certify_scores.py` does the same with the allocation held fixed, certifying all
870 per-response scores. Rerun both after any change here.

If the allocation that attains the DP bound also attains that value in the
simulator, the bound is achieved, and since it is an upper bound over *all*
allocations, it is the exact optimum. That is the certificate we record. When
the two disagree the instance is flagged rather than silently reported.

Why the relaxation is sound at R = 1
------------------------------------
* A player stack's damage is `count * dmg * factors` (MODEL.md sec. 4); it does
  not depend on where anyone stands.
* The defence holds position (policy `hold`), so no player stack takes damage
  before it acts, and retaliation damage lands after the attacker's own blow.
  Player losses therefore cannot reduce player output within the round, and they
  do not enter the objective at all.
* Damage to one enemy accumulates in a single health pool, and
  `count = ceil(total / hp)` (CUnitState.cpp:262-273), so kills depend only on
  the *sum* of damage that enemy receives, not on the order or the split.
* Reach is computed with every other slot empty, which is the most permissive
  case, so no reachable target is ever missed.

All of this needs R = 1. Multi-round instances are out of scope here, and the
generator refuses to emit them.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "scripts"))

from homm3_model import Battle, Stack, compute_damage, kills_for_damage  # noqa: E402

import instance as inst_mod  # noqa: E402


class SearchTooLarge(RuntimeError):
    """The DP state space blew past the cap; the instance is too big."""


STATE_CAP = 400_000


# --- geometry --------------------------------------------------------------


def reach_table(inst: dict) -> dict[tuple[int, str], tuple[int, ...]]:
    """(slot, type) -> enemy indices this stack could strike in round 1.

    Computed with all other player slots empty: the most permissive case, which
    is what makes the DP an upper bound.
    """
    return inst_mod._cached(inst, "reach", lambda: _make_reach(inst))


def _make_reach(inst: dict) -> dict[tuple[int, str], tuple[int, ...]]:
    types = inst_mod.creature_types(inst)
    field = inst_mod.battlefield(inst)
    enemies = inst["enemies"]
    out = {}
    for j, hex_ in enumerate(inst["slots"]):
        for name, ct in types.items():
            probe = Stack(ct, 1, side=0, slot=j, hex_=hex_)
            es = [Stack(types[e["type"]], e["count"], side=1, slot=g, hex_=e["hex"])
                  for g, e in enumerate(enemies)]
            battle = Battle(field, [probe] + es)
            out[(j, name)] = tuple(sorted(s.slot for s in battle.attackable(probe)))
    return out


def blocking_free(inst: dict) -> bool:
    """True if occupying every slot never removes a target from anyone's reach.

    A cheap necessary condition for the relaxation to be tight. Not sufficient
    (a stack that has moved can still block), which is why we still verify the
    optimum by simulation.
    """
    types = inst_mod.creature_types(inst)
    field = inst_mod.battlefield(inst)
    enemies = inst["enemies"]
    loose = reach_table(inst)
    # Fill every slot with the fastest available type, so the board is as
    # crowded as any allocation could make it.
    fill = max(types.values(), key=lambda t: t.speed)
    for j in range(inst["size"]):
        players = [Stack(fill, 1, side=0, slot=i, hex_=h)
                   for i, h in enumerate(inst["slots"])]
        es = [Stack(types[e["type"]], e["count"], side=1, slot=g, hex_=e["hex"])
              for g, e in enumerate(enemies)]
        battle = Battle(field, players + es)
        crowded = tuple(sorted(s.slot for s in battle.attackable(battle.stacks[j])))
        if crowded != loose[(j, fill.name)]:
            return False
    return True


# --- damage and kills ------------------------------------------------------


def damage_of(inst: dict, type_name: str, count: int, enemy_index: int) -> int:
    """Damage one strike of `count` creatures of `type_name` deals to enemy g."""
    types = inst_mod.creature_types(inst)
    e = inst["enemies"][enemy_index]
    attacker = Stack(types[type_name], count, side=0, slot=0, hex_=0)
    defender = Stack(types[e["type"]], e["count"], side=1, slot=0, hex_=1)
    return compute_damage(attacker, defender)


def _fresh_defenders(inst: dict) -> list[Stack]:
    """One pristine Stack per enemy, reused as a read-only kill predictor."""
    def make():
        types = inst_mod.creature_types(inst)
        return [Stack(types[e["type"]], e["count"], side=1, slot=g, hex_=e["hex"])
                for g, e in enumerate(inst["enemies"])]
    return inst_mod._cached(inst, "defenders", make)


def kills_of(inst: dict, enemy_index: int, damage: int) -> int:
    return kills_for_damage(_fresh_defenders(inst)[enemy_index], damage)


def value_of_damage(inst: dict, dmg: tuple[int, ...]) -> int:
    defenders = _fresh_defenders(inst)
    total = 0
    for g, d in enumerate(dmg):
        value = inst["types"][inst["enemies"][g]["type"]].get("value", 0)
        if value:
            total += kills_for_damage(defenders[g], d) * value
    return total


# --- the relaxation --------------------------------------------------------


def upper_bound_dp(inst: dict, state_cap: int = STATE_CAP) -> tuple[int, list]:
    """Exact optimum of the relaxed problem. Returns (value, allocation)."""
    if inst["rounds"] != 1:
        raise ValueError("the relaxation is only valid for R = 1")

    k = inst["size"]
    army = inst["army"]
    type_names = [a["type"] for a in army]
    stocks = tuple(a["stock"] for a in army)
    n_enemies = len(inst["enemies"])
    pools = tuple(e["count"] * inst["types"][e["type"]]["hp"] for e in inst["enemies"])
    reach = reach_table(inst)

    # Precompute damage[(type, count, enemy)] once.
    dmg_tab: dict[tuple[str, int, int], int] = {}
    for ti, name in enumerate(type_names):
        for c in range(1, stocks[ti] + 1):
            for g in range(n_enemies):
                dmg_tab[(name, c, g)] = damage_of(inst, name, c, g)

    # state -> allocation achieving it
    start_state = (stocks, (0,) * n_enemies)
    states: dict[tuple, tuple] = {start_state: ()}

    for j in range(k):
        nxt: dict[tuple, tuple] = {}

        def offer(state, alloc):
            if state not in nxt:
                nxt[state] = alloc

        for (left, dmg), alloc in states.items():
            offer((left, dmg), alloc + (None,))          # leave slot j empty
            for ti, name in enumerate(type_names):
                targets = reach[(j, name)]
                if not targets:
                    continue
                for c in range(1, left[ti] + 1):
                    new_left = left[:ti] + (left[ti] - c,) + left[ti + 1:]
                    for g in targets:
                        acc = min(dmg[g] + dmg_tab[(name, c, g)], pools[g])
                        new_dmg = dmg[:g] + (acc,) + dmg[g + 1:]
                        offer((new_left, new_dmg), alloc + ((name, c, g),))
        if len(nxt) > state_cap:
            raise SearchTooLarge(f"{len(nxt)} states after slot {j + 1}/{k}")
        states = nxt

    best_value, best_alloc = -1, None
    for (_left, dmg), alloc in states.items():
        v = value_of_damage(inst, dmg)
        if v > best_value:
            best_value, best_alloc = v, alloc
    allocation = [None if a is None else [a[0], a[1]] for a in best_alloc]
    return best_value, allocation


def dp_state_estimate(inst: dict) -> int:
    """Rough size of the DP table, for the generator's tractability filter."""
    stock_space = 1
    for a in inst["army"]:
        stock_space *= a["stock"] + 1
    dmg_space = 1
    for e in inst["enemies"]:
        dmg_space *= min(e["count"] * inst["types"][e["type"]]["hp"], 4000) + 1
    return stock_space * min(dmg_space, 10**9)


# --- the real simulator ----------------------------------------------------


def play_optimally(inst: dict, alloc: list) -> int:
    """Max destroyed value over all player action sequences, defence holds.

    `alloc` is already normalised and feasible. This is the ground truth: it
    runs the reference mechanics, including movement, blocking and retaliation.
    Exponential in the number of slots (up to ~1.8 s at k = 7), but it is what
    every reported number goes through, because the cheap alternative below is
    not a bound in either direction.
    """
    battle, initial = inst_mod.build_battle(inst, alloc)
    return _play(battle, None, 0, initial, inst["rounds"])


def play_fast(inst: dict, alloc: list) -> int:
    """A cheap approximation of `play_optimally`. NOT used for reported numbers.

    Kept because it is instructive, and because `verify_fast_evaluator` measures
    how wrong it is. It reads reach off the *starting* position and so misses
    the movement interaction in both directions:

      * an ally can stand in the only free hex adjacent to a target, which this
        does not see, so it can overstate;
      * a stack that has already moved into contact *frees* the hex it left,
        opening a path for a later ally, which this also does not see, so it can
        understate.

    Measured by the seeded probe in verify_instances.py (a deterministic
    reservoir sample of allocations per instance, each replayed through the
    exhaustive search), it disagrees with the exhaustive search on a handful
    of sampled allocations on several natural instances — the probe prints
    the exact counts on every run (15 of 11713 samples across 4 instances at
    the time of writing). Being wrong in both directions it is a bound in
    neither, which is exactly why nothing is allowed to depend on it. (An
    earlier revision quoted one extreme pair of values here; no committed
    artifact reproduces that pair, so the probe's counters are the citable
    measurement.)

    Setting that aside, the round is separable: each stack strikes once for
    `count * dmg * factors`, damage to an enemy accumulates in one pool, and
    kills depend only on the total (see the module docstring). So the only
    decision left is which target each stack picks, and that is a small DP over
    the vector of damage dealt so far.
    """
    if inst["rounds"] != 1:
        return play_optimally(inst, alloc)

    battle, _initial = inst_mod.build_battle(inst, alloc)
    enemies = [s for s in battle.stacks if s.side == 1]
    index_of = {id(s): g for g, s in enumerate(enemies)}
    pools = tuple(s.available() for s in enemies)

    states = {(0,) * len(enemies)}
    for stack in battle.stacks:
        if stack.side != 0:
            continue
        options = []
        for target in battle.attackable(stack):
            g = index_of[id(target)]
            options.append((g, compute_damage(stack, target)))
        if not options:
            continue
        nxt = set()
        for dmg in states:
            nxt.add(dmg)                     # passing is always allowed
            for g, d in options:
                acc = min(dmg[g] + d, pools[g])
                nxt.add(dmg[:g] + (acc,) + dmg[g + 1:])
        states = nxt

    return max(value_of_damage(inst, dmg) for dmg in states)


def verify_fast_evaluator(inst: dict, allocations: list) -> list[tuple]:
    """Return the allocations where `play_fast` and `play_optimally` disagree."""
    bad = []
    for raw in allocations:
        alloc = inst_mod.normalise_allocation(inst, raw)
        fast = play_fast(inst, alloc)
        slow = play_optimally(inst, alloc)
        if fast != slow:
            bad.append((raw, fast, slow))
    return bad


def _play(battle: Battle, order, i: int, initial, rounds_left: int) -> int:
    if order is None:
        order = [battle.stacks.index(s) for s in battle.turn_order()]
        i = 0
    if i == len(order):
        if rounds_left > 1:
            nxt = battle.clone()
            nxt.end_round()
            return _play(nxt, None, 0, initial, rounds_left - 1)
        return inst_mod.destroyed_value(battle, initial)

    idx = order[i]
    stack = battle.stacks[idx]
    if not stack.alive():
        return _play(battle, order, i + 1, initial, rounds_left)
    if stack.side == 1:
        return _play(battle, order, i + 1, initial, rounds_left)   # policy: hold

    # Passing changes nothing, so it needs no copy of the battle; only the
    # attacking branches do. This is most of the cost at seven slots, where the
    # search visits tens of thousands of nodes.
    best = _play(battle, order, i + 1, initial, rounds_left)
    for target in battle.attackable(stack):
        t_idx = battle.stacks.index(target)
        # Branch over every legal approach hex, not just the canonical one:
        # the chosen hex changes blocking/reachability for later stacks, and
        # collapsing it understates the achievable value (second-opinion
        # finding 7, confirmed on naturalS-k7-01).
        for dest in battle.attack_spots(stack, target):
            nxt = battle.clone()
            nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[t_idx], dest=dest)
            best = max(best, _play(nxt, order, i + 1, initial, rounds_left))
    return best


# --- certified optimum -----------------------------------------------------


def exact_optimum(inst: dict) -> dict:
    """Optimum plus the evidence that it really is one."""
    bound, alloc_raw = upper_bound_dp(inst)
    alloc = inst_mod.normalise_allocation(inst, alloc_raw)
    inst_mod.check_feasible(inst, alloc)
    achieved = play_optimally(inst, alloc)
    return {
        "optimum": achieved if achieved == bound else None,
        "relaxation_bound": bound,
        "simulated_value": achieved,
        "certified": achieved == bound,
        "allocation": alloc_raw,
        "max_enemy_value": inst_mod.max_enemy_value(inst),
        "blocking_free": blocking_free(inst),
    }


# --- independent cross-checks ---------------------------------------------


def enumerate_allocations(inst: dict, limit: int | None = None):
    """Every feasible allocation, as raw [[type, count] | None] lists."""
    k = inst["size"]
    army = inst["army"]
    names = [a["type"] for a in army]
    n = 0

    def rec(j: int, left: tuple, acc: list):
        nonlocal n
        if limit is not None and n >= limit:
            return
        if j == k:
            n += 1
            yield list(acc)
            return
        yield from rec(j + 1, left, acc + [None])
        for ti, name in enumerate(names):
            for c in range(1, left[ti] + 1):
                new_left = left[:ti] + (left[ti] - c,) + left[ti + 1:]
                yield from rec(j + 1, new_left, acc + [[name, c]])

    yield from rec(0, tuple(a["stock"] for a in army), [])


def brute_force_optimum(inst: dict, cap: int = 200_000) -> int | None:
    """Optimum by enumerating allocations and simulating each. None if too big."""
    best = -1
    seen = 0
    for raw in enumerate_allocations(inst):
        seen += 1
        if seen > cap:
            return None
        alloc = inst_mod.normalise_allocation(inst, raw)
        best = max(best, play_optimally(inst, alloc))
    return best


def knapsack_optimum(inst: dict) -> int | None:
    """The O(k*B) DP of candidate-A.md sec. 5.5, for its exact hypotheses.

    Applies only when the army is a single type and every slot reaches exactly
    one enemy, all distinct. Returns None when the hypotheses do not hold.
    """
    if len(inst["army"]) != 1 or inst["rounds"] != 1:
        return None
    if any(e["count"] != 1 for e in inst["enemies"]):
        return None       # sec. 5.5 assumes one creature per enemy stack
    name = inst["army"][0]["type"]
    budget = inst["army"][0]["stock"]
    reach = reach_table(inst)
    hit = [reach[(j, name)] for j in range(inst["size"])]
    if any(len(r) != 1 for r in hit):
        return None
    targets = [r[0] for r in hit]
    if len(set(targets)) != len(targets):
        return None

    # b_j = smallest count that kills enemy target[j] outright; v_j its value.
    values, needs = [], []
    for j, g in enumerate(targets):
        e = inst["enemies"][g]
        pool = e["count"] * inst["types"][e["type"]]["hp"]
        need = None
        for c in range(1, budget + 1):
            if damage_of(inst, name, c, g) >= pool:
                need = c
                break
        if need is None:
            continue
        values.append(e["count"] * inst["types"][e["type"]]["value"])
        needs.append(need)

    best = [0] * (budget + 1)
    for v, b in zip(values, needs):
        if b > budget:
            continue
        for cap_ in range(budget, b - 1, -1):
            cand = best[cap_ - b] + v
            if cand > best[cap_]:
                best[cap_] = cand
    return best[budget]
