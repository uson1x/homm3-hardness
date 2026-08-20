"""Regression tests for the obstacle and 2D-hex behaviour candidate D depends on.

`homm3_model.py` needed no change to support candidate D: `Battlefield.obstacles`
already existed and `Battle.reachable` already treated obstacles and occupied hexes
alike as blocked (`:278`).  `verify_mechanics.py` covers that with a single test
(C7).  Candidate D leans on obstacles much harder than candidate A ever did -- the
whole reduction is a statement about which hexes are connected to which -- so the
properties it relies on are pinned down here.

Each test names the fact from ../proofs/candidate-D-singletype.md that would break
if the simulator behaved differently.

Run:  python3 scripts/test_obstacles.py
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from homm3_model import Battle, Battlefield, CreatureType, Stack

FAILURES: list[str] = []
PASSED = 0


def check(name: str, got, want) -> None:
    global PASSED
    if got != want:
        FAILURES.append(f"{name}: got {got!r}, want {want!r}")
    else:
        PASSED += 1


def make(name, **kw):
    base = dict(attack=1, defense=1, dmg_min=1, dmg_max=1, hp=10, speed=3, value=0)
    base.update(kw)
    return CreatureType(name=name, **base)


# --- the alternating-triple fact (Lemma 4.2 of the writeup) ----------------


def test_alternating_neighbours_are_pairwise_nonadjacent():
    """The enemy gadget needs three free neighbours no two of which touch.

    The six neighbours of a hex form a cycle; the two alternating triples are the
    only 3-subsets that are pairwise non-adjacent.  If this failed, the element
    regions would not be separated and the reduction would leak.
    """
    f = Battlefield(width=11, height=11)
    for y in (4, 5):                       # both row parities
        z = f.index(5, y)
        nb = list(f.neighbours(z))
        check(f"row {y}: six neighbours", len(nb), 6)
        # ordering of Battlefield.neighbours: L, R, TL, TR, BL, BR
        left, right, tl, tr, bl, br = nb
        for triple, label in (((tl, right, bl), "TL/R/BL"),
                              ((tr, br, left), "TR/BR/L")):
            bad = [(a, b) for i, a in enumerate(triple)
                   for b in triple[i + 1:] if f.adjacent(a, b)]
            check(f"row {y}: {label} pairwise non-adjacent", bad, [])
        # the ring: consecutive neighbours always touch, so any 3-subset other
        # than the two alternating triples contains a touching pair
        ring = [tl, tr, right, br, bl, left]
        for i in range(6):
            check(f"row {y}: ring neighbours {i} and {(i+1) % 6} touch",
                  f.adjacent(ring[i], ring[(i + 1) % 6]), True)


def test_square_grid_is_a_subgraph_of_the_hex_grid():
    """Corridors are routed on rows and columns; both must always be adjacencies."""
    f = Battlefield(width=9, height=9)
    for y in range(8):
        for x in range(8):
            check(f"({x},{y}) touches ({x+1},{y})",
                  f.adjacent(f.index(x, y), f.index(x + 1, y)), True)
            check(f"({x},{y}) touches ({x},{y+1})",
                  f.adjacent(f.index(x, y), f.index(x, y + 1)), True)


# --- reachability through obstacles ---------------------------------------


def test_obstacle_wall_separates_regions():
    """A stack cannot reach across a solid column of impassable hexes.

    This is invariant I2: the element regions are separated by obstacles, and a
    speed large enough to cross the whole board must still not cross a wall.
    """
    W, H = 7, 5
    f0 = Battlefield(width=W, height=H)
    wall = frozenset(f0.index(3, y) for y in range(H))
    f = Battlefield(width=W, height=H, obstacles=wall)
    a = Stack(make("a", speed=W * H), 1, 0, 0, f.index(0, 2))
    d = Stack(make("d"), 1, 1, 0, f.index(6, 2))
    b = Battle(f, [a, d])
    check("wall blocks reach", b.attackable(a), [])
    check("wall confines the reachable set",
          all(h % W < 3 for h in b.reachable(a)), True)

    # the same board with one gap in the wall lets it through
    f2 = Battlefield(width=W, height=H, obstacles=wall - {f0.index(3, 2)})
    b2 = Battle(f2, [a.clone(), d.clone()])
    check("a gap in the wall restores reach", len(b2.attackable(b2.stacks[0])), 1)


def test_enemy_hex_blocks_passage_until_it_dies():
    """A living enemy is not enterable; a dead one stops blocking.

    Both halves matter.  The first is what disconnects the element regions
    (`CBattleInfoCallback.cpp:1355-1360`, transcribed at `homm3_model.py:271`).
    The second is the reason the writeup needs the induction of Lemma 5.4:
    once an enemy dies its hex opens, and the proof has to show that this never
    helps a player stack that has not yet acted.
    """
    W, H = 7, 3
    f0 = Battlefield(width=W, height=H)
    wall = frozenset(f0.index(3, y) for y in (0, 2))
    f = Battlefield(width=W, height=H, obstacles=wall)
    gate = f.index(3, 1)

    attacker = Stack(make("a", speed=W * H, attack=1), 1, 0, 0, f.index(0, 1))
    blocker = Stack(make("b", hp=1, defense=1), 1, 1, 0, gate)
    far = Stack(make("f", hp=50), 1, 1, 1, f.index(6, 1))
    b = Battle(f, [attacker, blocker, far])

    reach = b.reachable(attacker)
    check("living blocker seals the gate", any(h % W > 3 for h in reach), False)
    check("only the blocker is attackable",
          [s.slot for s in b.attackable(attacker)], [0])

    blocker.apply_damage(blocker.available())
    check("blocker is dead", blocker.alive(), False)
    reach2 = b.reachable(attacker)
    check("dead blocker no longer seals the gate",
          any(h % W > 3 for h in reach2), True)
    check("the far stack becomes attackable",
          [s.slot for s in b.attackable(attacker)], [1])


def test_ally_blocks_a_corridor_but_not_a_leaf():
    """A stack on a corridor hex blocks it; a stack on a dead-end blocks nothing.

    The construction puts every deployment hex on a dead end precisely so that a
    stack standing there can never obstruct anything (invariant I3b).
    """
    W, H = 8, 3
    f0 = Battlefield(width=W, height=H)
    # corridor along row 1, with a one-hex stub hanging off (2,0)
    free = {f0.index(x, 1) for x in range(W)} | {f0.index(2, 0)}
    f = Battlefield(width=W, height=H,
                    obstacles=frozenset(h for h in range(W * H) if h not in free))

    walker = make("w", speed=W * H, attack=1)
    mover = Stack(walker, 1, 0, 0, f.index(0, 1))
    target = Stack(make("t", hp=50), 1, 1, 0, f.index(7, 1))

    on_corridor = Stack(walker, 1, 0, 1, f.index(4, 1))
    b1 = Battle(f, [mover, on_corridor, target])
    check("ally on the corridor blocks", b1.attackable(b1.stacks[0]), [])

    on_stub = Stack(walker, 1, 0, 1, f.index(2, 0))
    b2 = Battle(f, [mover.clone(), on_stub, target.clone()])
    check("ally on the dead-end does not block",
          len(b2.attackable(b2.stacks[0])), 1)


def test_speed_beyond_the_board_still_respects_obstacles():
    """Candidate D gives the player speed = width*height; reach is then exactly
    the connected region, not the whole board."""
    W, H = 9, 5
    f0 = Battlefield(width=W, height=H)
    room = {f0.index(x, y) for x in range(3) for y in range(3)}
    f = Battlefield(width=W, height=H,
                    obstacles=frozenset(h for h in range(W * H) if h not in room))
    a = Stack(make("a", speed=W * H), 1, 0, 0, f0.index(0, 0))
    b = Battle(f, [a])
    check("reach equals the enclosing room", b.reachable(a), room)


def test_reach_antimonotone_in_blocked_set() -> None:
    """Forbidding more hexes never adds reach. This is the anti-monotonicity
    the ghost-enemy relaxation of empirics' verify_full_model_optima.py leans
    on; its docstring has claimed since round 9 that this file pins the
    property, and round 10 found no test actually did — this is that test."""
    import random
    rng = random.Random(20261019)
    violations = []
    for trial in range(40):
        W, H = rng.randint(4, 8), rng.randint(3, 7)
        cells = list(range(W * H))
        start = rng.choice(cells)
        rest = [h for h in cells if h != start]
        rng.shuffle(rest)
        cut = rng.randint(0, len(rest) // 3)
        small = frozenset(rest[:cut])
        big = small | frozenset(rest[cut:cut + rng.randint(0, 6)])
        reaches = []
        for blocked in (small, big):
            f = Battlefield(width=W, height=H, obstacles=blocked)
            a = Stack(make("a", speed=W * H), 1, 0, 0, start)
            reaches.append(Battle(f, [a]).reachable(a))
        if not reaches[1] <= reaches[0]:
            violations.append((trial, W, H, sorted(reaches[1] - reaches[0])))
    check("reach is anti-monotone in the blocked set (40 random boards)",
          violations, [])


def main() -> int:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        print(f"  {t.__name__}")
        t()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s), {PASSED} passed")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print(f"OK: all {PASSED} checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
