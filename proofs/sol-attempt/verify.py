#!/usr/bin/env python3
"""Finite exhaustive checks for the single-type Planar-3DM reduction.

This script deliberately uses scripts/homm3_model.py for every mechanical
operation.  For each test instance it enumerates every legal allocation of the
stock, and for each allocation it branches over passing and every pair
(living target, legal approach hex), exactly as scripts/solve.py::_play does.

Run from the repository root with:

    python3 verify.py
"""

from __future__ import annotations

import itertools
import sys
from collections import deque
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "scripts"))

from homm3_model import (  # noqa: E402
    Battle,
    Battlefield,
    CreatureType,
    Stack,
    compute_damage,
    defense_skill_factor,
    destroyed_value,
)


PLAYER_ATTACK = 1
ENEMY_DEFENSE = 27


def player_type(speed: int) -> CreatureType:
    return CreatureType(
        "P", attack=PLAYER_ATTACK, defense=1, dmg_min=1, dmg_max=1,
        hp=4, speed=speed,
    )


ENEMY = CreatureType(
    "E", attack=1, defense=ENEMY_DEFENSE, dmg_min=1, dmg_max=1,
    hp=3, speed=1, value=1,
)


@dataclass(frozen=True)
class ReductionCase:
    name: str
    q: int
    sets: tuple[frozenset[int], ...]
    field: Battlefield
    slots: tuple[int, ...]
    enemy_hexes: tuple[int, ...]
    paths: tuple[frozenset[int], ...]
    speed: int


def shortest_path(field: Battlefield, start: int, goal: int) -> list[int]:
    """A deterministic shortest hex-grid path, used only to draw test mazes."""
    todo = deque([start])
    parent: dict[int, int | None] = {start: None}
    while todo:
        cur = todo.popleft()
        if cur == goal:
            break
        neighbours = sorted(
            field.neighbours(cur),
            key=lambda h: (field.distance(h, goal), h),
        )
        for nxt in neighbours:
            if nxt not in parent:
                parent[nxt] = cur
                todo.append(nxt)
    if goal not in parent:
        raise AssertionError("test drawing has no path")
    answer = []
    cur: int | None = goal
    while cur is not None:
        answer.append(cur)
        cur = parent[cur]
    return list(reversed(answer))


def finish_case(
    name: str,
    q: int,
    sets: tuple[frozenset[int], ...],
    width: int,
    height: int,
    centers_xy: tuple[tuple[int, int], ...],
    path_ends_xy: tuple[tuple[tuple[int, int], tuple[int, int]], ...],
) -> ReductionCase:
    """Turn explicitly drawn, mutually separated element paths into a battle."""
    blank = Battlefield(width, height)
    h = lambda xy: blank.index(*xy)
    paths = tuple(
        frozenset(shortest_path(blank, h(start), h(end)))
        for start, end in path_ends_xy
    )
    if len(paths) != 3 * q:
        raise AssertionError("one element path and one slot are required per element")

    # Removing the enemy centers must leave one component per element.  It is
    # enough here to assert the stronger property used by these hand drawings:
    # different paths neither overlap nor have adjacent cells.
    for i, j in itertools.combinations(range(len(paths)), 2):
        if paths[i] & paths[j]:
            raise AssertionError(f"{name}: element paths {i},{j} overlap")
        if any(blank.adjacent(a, b) for a in paths[i] for b in paths[j]):
            raise AssertionError(f"{name}: element paths {i},{j} touch")

    centers = tuple(h(xy) for xy in centers_xy)
    open_cells = set(centers)
    for path in paths:
        open_cells.update(path)
    obstacles = frozenset(range(width * height)) - open_cells
    field = Battlefield(width, height, obstacles)
    slots = tuple(sorted(path)[len(path) // 2] for path in paths)
    # Speed exceeds the diameter of every pristine element component.  This
    # intentionally permits movement through dead target hexes; the no-case
    # therefore exercises the leakage issue addressed in the proof.
    speed = max(len(path) for path in paths) + 2
    return ReductionCase(name, q, sets, field, slots, centers, paths, speed)


def yes_case() -> ReductionCase:
    """Three planar triples; the first and third form an exact cover."""
    # A={0,1,2}, B={0,3,4}, C={3,4,5}.  Targets lie on one row.
    # Elements 0,3,4 are the three horizontal internal corridors; elements
    # 1,2,5 are outward leaves.  Each target's ports alternate around its hex.
    sets = (
        frozenset((0, 1, 2)),
        frozenset((0, 3, 4)),
        frozenset((3, 4, 5)),
    )
    paths = (
        ((11, 15), (24, 15)),  # element 0: A--B
        ((9, 14), (4, 7)),     # element 1: A leaf
        ((9, 16), (4, 23)),    # element 2: A leaf
        ((25, 14), (39, 14)),  # element 3: B--C, upper
        ((25, 16), (39, 16)),  # element 4: B--C, lower
        ((41, 15), (47, 15)),  # element 5: C leaf
    )
    return finish_case(
        "yes-with-distractor", 2, sets, 52, 32,
        ((10, 15), (25, 15), (40, 15)), paths,
    )


def no_case() -> ReductionCase:
    """Three planar triples, every pair intersecting, hence no exact cover."""
    # A={0,1,2}, B={0,3,4}, C={1,3,5}.  The shared-element corridors form a
    # triangle and the other three elements are leaves.
    sets = (
        frozenset((0, 1, 2)),
        frozenset((0, 3, 4)),
        frozenset((1, 3, 5)),
    )
    paths = (
        ((13, 9), (36, 9)),    # element 0: A--B
        ((13, 11), (23, 26)),  # element 1: A--C
        ((11, 10), (4, 10)),   # element 2: A leaf
        ((36, 11), (25, 25)),  # element 3: B--C
        ((37, 10), (44, 10)),  # element 4: B leaf
        ((25, 27), (25, 34)),  # element 5: C leaf
    )
    return finish_case(
        "no-pairwise-intersection", 2, sets, 50, 38,
        ((12, 10), (36, 10), (24, 26)), paths,
    )


def x3c_verdict(case: ReductionCase) -> bool:
    universe = set(range(3 * case.q))
    for chosen in itertools.combinations(range(len(case.sets)), case.q):
        counts = {x: 0 for x in universe}
        for g in chosen:
            for x in case.sets[g]:
                counts[x] += 1
        if all(counts[x] == 1 for x in universe):
            return True
    return False


def make_battle(case: ReductionCase, allocation: tuple[int, ...]):
    ptype = player_type(case.speed)
    stacks = [
        Stack(ptype, count, side=0, slot=x, hex_=case.slots[x])
        for x, count in enumerate(allocation) if count > 0
    ]
    stacks.extend(
        Stack(ENEMY, 1, side=1, slot=g, hex_=hex_)
        for g, hex_ in enumerate(case.enemy_hexes)
    )
    battle = Battle(case.field, stacks)
    initial = {
        i: stack.count()
        for i, stack in enumerate(battle.stacks) if stack.side == 1
    }
    return battle, initial


def allocations(k: int, stock: int):
    """All nonnegative k-tuples whose sum is at most stock."""
    def rec(i: int, left: int, prefix: tuple[int, ...]):
        if i == k:
            yield prefix
            return
        for count in range(left + 1):
            yield from rec(i + 1, left - count, prefix + (count,))
    yield from rec(0, stock, ())


def play_exhaustively(
    battle: Battle,
    initial: dict[int, int],
    stats: dict[str, int],
    order: list[int] | None = None,
    i: int = 0,
) -> int:
    """Exact one-round play, branching over targets and approach cells."""
    stats["nodes"] += 1
    if order is None:
        order = [battle.stacks.index(s) for s in battle.turn_order()]
    if i == len(order):
        return destroyed_value(battle, initial)

    idx = order[i]
    stack = battle.stacks[idx]
    if not stack.alive() or stack.side == 1:  # scripted defence holds
        return play_exhaustively(battle, initial, stats, order, i + 1)

    # Passing is a legal branch.
    best = play_exhaustively(battle, initial, stats, order, i + 1)
    for target in battle.attackable(stack):
        stats["target_branches"] += 1
        target_idx = battle.stacks.index(target)
        spots = battle.attack_spots(stack, target)
        for dest in spots:
            stats["approach_branches"] += 1
            nxt = battle.clone()
            nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[target_idx], dest=dest)
            best = max(
                best,
                play_exhaustively(nxt, initial, stats, order, i + 1),
            )
    return best


def exhaustive_game_optimum(case: ReductionCase):
    stock = 3 * case.q
    best = -1
    witness = None
    stats = {
        "allocations": 0,
        "nodes": 0,
        "target_branches": 0,
        "approach_branches": 0,
    }
    for allocation in allocations(3 * case.q, stock):
        stats["allocations"] += 1
        battle, initial = make_battle(case, allocation)
        value = play_exhaustively(battle, initial, stats)
        if value > best:
            best = value
            witness = allocation
    return best, witness, stats


def audit_damage() -> None:
    probe_player = player_type(speed=2)
    reduction = defense_skill_factor(probe_player.attack, ENEMY.defense)
    multiplier = 1.0 - reduction
    damages = []
    for count in range(1, 13):
        attacker = Stack(probe_player, count, 0, 0, 0)
        defender = Stack(ENEMY, 1, 1, 0, 1)
        damages.append(compute_damage(attacker, defender))
    assert damages[:3] == [1, 1, 1]
    assert all(d <= c for c, d in enumerate(damages, 1))

    minima = []
    for number_of_stacks in (1, 2, 3):
        minimum = None
        for total in range(number_of_stacks, 30):
            for cuts in itertools.combinations(range(1, total), number_of_stacks - 1):
                parts = tuple(
                    b - a for a, b in zip((0,) + cuts, cuts + (total,))
                )
                total_damage = 0
                for count in parts:
                    attacker = Stack(probe_player, count, 0, 0, 0)
                    defender = Stack(ENEMY, 1, 1, 0, 1)
                    total_damage += compute_damage(attacker, defender)
                if total_damage >= 3:
                    minimum = total
                    break
            if minimum is not None:
                break
        minima.append(minimum)
    assert minima == [9, 7, 3]

    # Exhaust the equality case independently: with total cost at most three,
    # three damage occurs only for the composition (1,1,1).
    achieving = []
    for number_of_stacks in (1, 2, 3):
        for total in range(number_of_stacks, 4):
            for cuts in itertools.combinations(range(1, total), number_of_stacks - 1):
                parts = tuple(
                    b - a for a, b in zip((0,) + cuts, cuts + (total,))
                )
                damage = sum(damages[count - 1] for count in parts)
                if damage >= 3:
                    achieving.append(parts)
    assert achieving == [(1, 1, 1)]

    print("DAMAGE AUDIT")
    print(f"  defence reduction = {reduction!r}")
    print(f"  resulting multiplier = {multiplier!r}")
    print(f"  compute_damage(c), c=1..12: {damages}")
    print(f"  minimum creatures using 1,2,3 attacking stacks: {minima}")
    print("  cost <= 3 reaches 3 damage only as: [(1, 1, 1)]")


def audit_obstacles() -> None:
    field = Battlefield(width=5, height=1, obstacles=frozenset((2,)))
    ptype = player_type(speed=4)
    attacker = Stack(ptype, 1, 0, 0, 0)
    defender = Stack(ENEMY, 1, 1, 0, 4)
    battle = Battle(field, [attacker, defender])
    assert battle.reachable(attacker) == {0, 1}
    assert battle.attackable(attacker) == []
    print("OBSTACLE AUDIT")
    print("  one-row wall at hex 2: reachable from 0 = [0, 1]; target at 4 unreachable")


def audit_geometry(case: ReductionCase) -> None:
    ptype = player_type(case.speed)
    expected_by_element = {
        x: tuple(g for g, triple in enumerate(case.sets) if x in triple)
        for x in range(3 * case.q)
    }

    # Loose probes establish exact incidence reachability.
    for x in range(3 * case.q):
        probe = Stack(ptype, 1, 0, x, case.slots[x])
        enemies = [
            Stack(ENEMY, 1, 1, g, h)
            for g, h in enumerate(case.enemy_hexes)
        ]
        battle = Battle(case.field, [probe] + enemies)
        got = tuple(sorted(target.slot for target in battle.attackable(probe)))
        assert got == expected_by_element[x], (case.name, x, got, expected_by_element[x])
        for target in battle.attackable(probe):
            assert len(battle.attack_spots(probe, target)) == 1

    # Filling every slot must not introduce initial blocking.
    battle, _ = make_battle(case, (1,) * (3 * case.q))
    for stack in battle.stacks:
        if stack.side != 0:
            continue
        got = tuple(sorted(target.slot for target in battle.attackable(stack)))
        assert got == expected_by_element[stack.slot]

    reach_signature = ", ".join(
        f"{x}->{expected_by_element[x]}" for x in range(3 * case.q)
    )
    print(f"GEOMETRY {case.name}")
    print(f"  field={case.field.width}x{case.field.height}, speed={case.speed}")
    print(f"  exact loose and fully-occupied reach: {reach_signature}")
    print("  every reachable target has exactly one legal approach hex per element corridor")


def main() -> None:
    audit_damage()
    audit_obstacles()
    cases = (yes_case(), no_case())
    for case in cases:
        audit_geometry(case)
        source_yes = x3c_verdict(case)
        optimum, witness, stats = exhaustive_game_optimum(case)
        game_yes = optimum >= case.q
        assert game_yes == source_yes
        print(f"EXHAUSTIVE {case.name}")
        print(f"  planar-X3C verdict={source_yes}")
        print(f"  game optimum={optimum}, threshold={case.q}, verdict={game_yes}")
        print(f"  first optimum allocation={witness}")
        print(
            "  searched "
            f"allocations={stats['allocations']}, nodes={stats['nodes']}, "
            f"target branches={stats['target_branches']}, "
            f"approach branches={stats['approach_branches']}"
        )
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
