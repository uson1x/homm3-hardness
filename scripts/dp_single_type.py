#!/usr/bin/env python3
"""Upper bound check for candidate-A §5.4: single creature type, R = 1.

In the Theorem-1 family (corridor, hold policy, each slot reaches a unique
enemy, ONE CREATURE PER ENEMY STACK, damage under (★)) the game reduces to:
pick S ⊆ [k] maximising Σ v_j subject to Σ b_j ≤ B, where b_j = ceil(t_j / d)
is the count needed to finish enemy j. That is 0-1 knapsack; dp() solves it
in O(k·B).

Three checks, in order of strength:
  [1] dp() against exhaustive subset enumeration of the same knapsack
      abstraction on random instances — validates the program, not the
      abstraction (round 10 made this distinction load-bearing);
  [2] dp() against exhaustive play of BUILT corridor instances in
      homm3_model — validates the abstraction itself on the game;
  [3] a negative control: the round-10 counterexample (matching reach,
      multi-creature enemy stacks) where the threshold abstraction is
      provably wrong — the suite asserts dp and the game DISAGREE, so this
      file can never again green-light a family the proposition does not
      cover.
"""
import itertools
import random

from homm3_model import Battle, Battlefield, CreatureType, Stack
from brute_force import max_destroyed_value


def dp(values, needs, budget):
    """0-1 knapsack, O(k*B) time, O(B) space."""
    best = [0] * (budget + 1)
    for v, b in zip(values, needs):
        if b > budget:
            continue
        for cap in range(budget, b - 1, -1):
            cand = best[cap - b] + v
            if cand > best[cap]:
                best[cap] = cand
    return best[budget]


def brute(values, needs, budget):
    k = len(values)
    best = 0
    for r in range(k + 1):
        for s in itertools.combinations(range(k), r):
            if sum(needs[j] for j in s) <= budget:
                best = max(best, sum(values[j] for j in s))
    return best


N_TRIALS = 2000
N_GAME = 40


def build_corridor(enemies):
    """Theorem 1's corridor verbatim: one row of 5n hexes, p_j deployed at
    5(j-1), E_j at 5(j-1)+1, player speed 2 — slot j reaches E_j and nothing
    else (the next enemy is 6 hexes away, strike radius is 3). The player
    type has d = 1 and attack == defence, so (★) holds and nominal damage is
    dealt exactly. `enemies` is a list of (count, hp, value) triples; returns
    a function allocation -> Battle."""
    n = len(enemies)
    player = CreatureType("P", attack=5, defense=5, dmg_min=1, dmg_max=1,
                          hp=5, speed=2)
    etypes = [CreatureType(f"E{j}", attack=5, defense=5, dmg_min=1, dmg_max=1,
                           hp=hp, speed=0, value=val)
              for j, (_, hp, val) in enumerate(enemies)]

    def build(alloc):
        stacks = []
        for j, c in enumerate(alloc):
            if c:
                stacks.append(Stack(player, c, side=0, slot=j, hex_=5 * j))
        for j, (cnt, _, _) in enumerate(enemies):
            stacks.append(Stack(etypes[j], cnt, side=1, slot=j, hex_=5 * j + 1))
        return Battle(Battlefield(width=5 * n, height=1), stacks)

    return build


def game_optimum(enemies, budget):
    """Exhaustive: every allocation of `budget` creatures over len(enemies)
    slots, each played out by the exhaustive game search (R = 1)."""
    build = build_corridor(enemies)
    best = 0

    def rec(j, left, alloc):
        nonlocal best
        if j == len(enemies):
            if any(alloc):
                best = max(best, max_destroyed_value(build(alloc), 1))
            return
        for c in range(left + 1):
            rec(j + 1, left - c, alloc + [c])

    rec(0, budget, [])
    return best


def main():
    rng = random.Random(20260801)
    for trial in range(N_TRIALS):
        k = rng.randint(1, 12)
        budget = rng.randint(1, 60)
        values = [rng.randint(1, 50) for _ in range(k)]
        needs = [rng.randint(1, 70) for _ in range(k)]
        a, b = dp(values, needs, budget), brute(values, needs, budget)
        assert a == b, (trial, values, needs, budget, a, b)
    # the printed count is the loop bound itself, not a transcribed literal —
    # test_regressions.py parses this line to pin the manifest counter
    print(f"OK: dp == brute on {N_TRIALS} random instances")

    # [2] the abstraction against the game: single-creature corridors, where
    # the proposition applies — dp must equal exhaustive play exactly
    rng = random.Random(20261018)
    for trial in range(N_GAME):
        k = rng.randint(1, 3)
        budget = rng.randint(1, 6)
        enemies = [(1, rng.randint(1, 5), rng.randint(1, 9))
                   for _ in range(k)]
        values = [cnt * val for cnt, _, val in enemies]
        needs = [-(-hp // 1) for _, hp, _ in enemies]        # ceil(t_j / d), d = 1
        a = dp(values, needs, budget)
        g = game_optimum(enemies, budget)
        assert a == g, (trial, enemies, budget, a, g)
    print(f"OK: dp == game on {N_GAME} single-creature corridor instances")

    # [3] negative control: the round-10 counterexample — matching reach,
    # six-creature stacks. The threshold abstraction says 0 (b_j = 12 > B);
    # the game scores partial kills. If these ever AGREE, the guard rails
    # around Proposition 1.1's hypotheses have been silently removed.
    enemies = [(6, 2, 1), (6, 2, 1)]
    a = dp([6, 6], [12, 12], 6)
    g = game_optimum(enemies, 6)
    assert a == 0 and g == 3, (a, g)
    print(f"OK: negative control (multi-creature stacks): dp {a} != game {g}")


if __name__ == "__main__":
    main()
