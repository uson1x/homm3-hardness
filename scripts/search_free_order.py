"""Free-order adversarial search against the Theorem 3 reductions.

Promotion to a permanent suite of the one-off searcher built by the round-10
review (reviews/round-10/review-fable-5.md sec. 4), re-run in round 11 and
rebuilt in round 12 after the panel showed the first version could not detect
its own removal (P12-5/P12-10/P12-12).  The repo's own searchers
(`verify_x3c.py`, `crosscheck_sol.py`) walk one fixed activation order per
battle; every claim about order therefore rested on the proofs, not on search.
This suite searches an OVER-APPROXIMATION of the full action space:

  * free order -- at every step ANY player stack that has not yet taken its
    terminal action may act next.  The set of all permutations is a superset
    of every WAIT-realizable interleaving, so nothing the real turn engine
    can produce is missing;
  * pass and a vanish branch -- a passing stack may also vanish outright,
    which dominates every pure move (a stack that moves without attacking
    affects the rest of the round only through which hex it occupies, and
    occupying nothing is the most generous case; under `hold` the enemies
    never act, so a player stack's presence can only ever block the player's
    own approaches).  The vanish branch is offered ONLY to a passing stack,
    never to a striking one: letting strikers vanish would manufacture
    spurious yes-answers, because the confinement argument of Theorem 3
    genuinely depends on dead enemies' dockings staying plugged;
  * `hold` defence -- the enemy never activates, so it never gains the DEFEND
    bonus; this dominates `(‡)` (the paper's WAIT-then-DEFEND policy) for
    the player: without the bonus every searched blow is at least as
    damaging as under `(‡)`, never less;
  * exhaustive approach hexes -- every legal destination of every
    walk-and-attack is branched over, never a canonical one.  (Round 13,
    F-13: on the corpus itself no expanded state ever offers a second
    approach hex -- at W = q every kill is maximally efficient, so a dead
    enemy's three dockings are all plugged by its strikers, which is
    Lemma D.7 seen from the searcher's side.  The branch is therefore
    exercised only by the destination control; the corpus fact is pinned
    as the counter `multi_spot == 0` below, not described as coverage.)

Memoisation is keyed on (acted bitmask, full per-stack state), so no legal
line of play is discarded.  `_best_free` is a THRESHOLD DECISION PROCEDURE,
not a value function: the admissible-bound cutoff returns 0 for subtrees that
cannot reach `target`, so only "value >= target" may be read off it.

ONE corpus of families is built and searched under BOTH constant sets --
the historical (defence 41) and the published (defence 27, hp 4) -- with the
swap asserted at build time, the way `verify_embedding.py` does it (round 12,
P12-10/P12-12).  For every built board the suite asserts that the free-order
answer equals both the X3C answer and the fixed-order answer, over EVERY
allocation, and that yes-instances admit only the all-ones winner.

Because those assertions are equalities, they alone cannot show the
enlargements are ACTIVE (round 12, P12-5: the first version passed all four
deletion drills).  Three discriminating controls therefore assert strict
DISAGREEMENT between the full search and a degraded one:

  * order control -- a doorway board (a slow stack must kill a blocker enemy
    before a fast stack can pass through the freed hex): free order scores 2,
    the fixed decreasing-speed order scores 1 (enemy values are 1 apiece --
    the admissible bound counts kills, so control values must equal 1, as in
    the X3C corpora);
  * vanish control -- a speed-0 friendly blocker walls off the only corridor:
    with the vanish branch the search scores 1, without it 0.  (The real game
    cannot remove the blocker; the control certifies the BRANCH is live, which
    is what the over-approximation argument consumes.)
  * destination control -- the two-destination blocking gadget of
    `test_regressions.destination_case` with the valuable enemy's value set
    to 1: exhaustive approach hexes score 1, the first-spot-only degradation
    scores 0.

A negative control (enemy defence set equal to player attack, so D(c) = c)
must flip a planar no-instance to yes -- proving the game search itself is
not vacuous.

The controls certify that each branch EXISTS on a 2-4-stack fixture; round
13 showed (fable F-04, codex Check 04) that three degraded searchers -- free
choice for the first actor only, two approach hexes, vanish for speed-0
stacks only, and even the corpus entry point swapped for the fixed-order
searcher -- pass the whole suite, controls included.  So the corpus tiers now
COUNT what they exercise (`TRACE`): out-of-order activations (`reorder`),
expanded vanish branches (`vanish`) and states offering more than one
approach hex (`multi_spot`).  The suite asserts reorder > 0 and vanish > 0
on the corpus and prints all three on its final line, where the battery
pins them to the manifest; each degraded searcher zeroes one of them.

Run:  python3 scripts/search_free_order.py           # battery tier
      python3 scripts/search_free_order.py --full    # adds q=3 families
"""

from __future__ import annotations

import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import homm3_model as M
import verify_x3c as V
from crosscheck_sol import (SOL_ENEMY_DEF, SOL_PLAYER_HP, restore,
                            with_sol_stats)
from homm3_model import (Battle, Battlefield, CreatureType, Stack,
                         compute_damage)

HIST_ENEMY_DEF = 41            # verify_x3c's historical constants
HIST_PLAYER_HP = 5

# round 13: what the search actually exercised (see the module docstring).
# Reset before the corpus tiers and snapshotted before the controls run.
TRACE = {"reorder": 0, "vanish": 0, "multi_spot": 0}


def _trace_reset():
    for k in TRACE:
        TRACE[k] = 0


# --- the free-order search --------------------------------------------------


def _state_key(battle, acted_mask: int):
    return (acted_mask,
            tuple((s.full_units, s.first_hp_left, s.hex, s.retaliations_left,
                   s.defending)
                  for s in battle.stacks))


def _upper_bound(battle, players, acted_mask: int, initial) -> int:
    """Same admissible bound as verify_x3c._upper_bound, over the unacted set."""
    capacity = 0
    enemy = None
    for bit, idx in enumerate(players):
        if acted_mask >> bit & 1:
            continue
        s = battle.stacks[idx]
        if s.alive():
            if enemy is None:
                enemy = next(t for t in battle.stacks if t.side == 1)
            capacity += compute_damage(s, enemy)
    need = sorted(s.available() for s in battle.stacks if s.side == 1 and s.alive())
    extra = 0
    for n in need:
        if capacity >= n:
            capacity -= n
            extra += 1
        else:
            break
    return M.destroyed_value(battle, initial) + extra


def _best_free(battle, players, acted_mask: int, initial, target, memo, *,
               free_order=True, vanish=True, all_spots=True) -> int:
    """Threshold decision procedure: is a destroyed value >= target reachable?

    Returns a value >= target iff one is reachable; the bound cutoff prunes
    losing subtrees to 0, so the return is NOT the exact maximum.  Branches,
    per unacted stack: pass; vanish (pure-movement dominator, see module
    docstring); every attack against every reachable target from every
    approach hex.  Enemies never act (`hold`).  Sibling branches never see a
    mutation: every action clones first (the round-7a state-leak lesson).

    The keyword flags exist ONLY for the discriminating controls: they
    degrade the search (one fixed order / no vanish / first approach hex) so
    the controls can assert the full search strictly beats the degraded one.
    The corpus tiers always run with all three enabled.
    """
    full = (1 << len(players)) - 1
    if acted_mask == full:
        return M.destroyed_value(battle, initial)
    key = _state_key(battle, acted_mask)
    if key in memo:
        return memo[key]
    if _upper_bound(battle, players, acted_mask, initial) < target:
        memo[key] = 0
        return 0            # only "< target" is ever asked of this number

    kw = dict(free_order=free_order, vanish=vanish, all_spots=all_spots)
    best = 0
    first_unacted = next(b for b in range(len(players))
                         if not acted_mask >> b & 1)
    for bit, idx in enumerate(players):
        if acted_mask >> bit & 1:
            continue
        if acted_mask and bit != first_unacted:
            TRACE["reorder"] += 1      # a non-first unacted stack acts next
        nmask = acted_mask | (1 << bit)
        stack = battle.stacks[idx]
        if not stack.alive():
            best = max(best, _best_free(battle, players, nmask, initial,
                                        target, memo, **kw))
            if best >= target:
                break
            if not free_order:
                break
            continue
        # pass
        best = max(best, _best_free(battle, players, nmask, initial,
                                    target, memo, **kw))
        # vanish (pure-movement dominator; never offered to a striking stack)
        if vanish and best < target:
            TRACE["vanish"] += 1
            ghost = battle.clone()
            g = ghost.stacks[idx]
            g.apply_damage(g.available())
            best = max(best, _best_free(ghost, players, nmask, initial,
                                        target, memo, **kw))
        # every attack
        if best < target:
            for t in battle.attackable(stack):
                t_idx = battle.stacks.index(t)
                spots = battle.attack_spots(stack, t)
                if len(spots) > 1:
                    TRACE["multi_spot"] += 1
                if not all_spots:
                    spots = spots[:1]
                for dest in spots:
                    nxt = battle.clone()
                    nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[t_idx],
                                       dest=dest)
                    best = max(best, _best_free(nxt, players, nmask, initial,
                                                target, memo, **kw))
                    if best >= target:
                        break
                if best >= target:
                    break
        if best >= target:
            break
        if not free_order:
            break           # degraded mode: only the first unacted stack acts
    memo[key] = best
    return best


def _search_battle(battle, target, **kw) -> int:
    initial = {i: s.count() for i, s in enumerate(battle.stacks)
               if s.side == 1}
    players = [i for i, s in enumerate(battle.stacks) if s.side == 0]
    if not kw.get('free_order', True):
        # the degraded order is the engine's: decreasing speed
        players.sort(key=lambda i: -battle.stacks[i].ctype.speed)
    return _best_free(battle, players, 0, initial, target, {}, **kw)


def free_play_value(inst, alloc: dict, target: int) -> int:
    battle, initial = V.build_battle(inst, alloc)
    players = [i for i, s in enumerate(battle.stacks) if s.side == 0]
    return _best_free(battle, players, 0, initial, target, {})


def free_winning_allocations(inst, stop_at_first=False) -> list[tuple]:
    elements = sorted(inst["deploy"])
    target = inst["target"]
    out = []
    for vec in V._allocations(len(elements), inst["stock"]):
        alloc = dict(zip(elements, vec))
        if free_play_value(inst, alloc, target) >= target:
            out.append(vec)
            if stop_at_first:
                break
    return out


# --- discriminating controls ------------------------------------------------


def _flat(name, hp, speed, value=0):
    return CreatureType(name, attack=10, defense=10, dmg_min=1, dmg_max=1,
                        hp=hp, speed=speed, value=value, no_retaliation=True)


def control_order() -> list[str]:
    """Doorway: the slow stack must open the door BEFORE the fast one moves.

    5x2 board.  P_fast (speed 3) at (0,0); E1 (value 1) at (2,0) walls the
    row-0 corridor and P_slow at (2,1) walls the row-1 bypass; E2 (value 1)
    at (4,0).  P_slow is adjacent to E1 and kills it; only then can P_fast
    walk (1,0)-(2,0)-(3,0) and strike E2.  Under the fixed decreasing-speed
    order P_fast acts first, when every path to E2 is still walled, and the
    vanish branch cannot rescue it (vanishing P_slow does not free E1's hex).
    """
    field = Battlefield(width=5, height=2)
    stacks = [
        Stack(_flat("Pfast", hp=5, speed=3), 1, side=0, slot=0,
              hex_=field.index(0, 0)),
        Stack(_flat("Pslow", hp=5, speed=0), 1, side=0, slot=1,
              hex_=field.index(2, 1)),
        Stack(_flat("E1", hp=1, speed=1, value=1), 1, side=1, slot=0,
              hex_=field.index(2, 0)),
        Stack(_flat("E2", hp=1, speed=1, value=1), 1, side=1, slot=1,
              hex_=field.index(4, 0)),
    ]
    free = _search_battle(Battle(field, [s.clone() for s in stacks]), 2)
    fixed = _search_battle(Battle(field, [s.clone() for s in stacks]), 2,
                           free_order=False)
    fails = []
    if free < 2:
        fails.append(f"order control: free-order search scored {free}, "
                     f"expected 2 (doorway not found)")
    if fixed >= 2:
        fails.append(f"order control: fixed-order search scored {fixed}, "
                     f"expected < 2 -- the control no longer discriminates")
    return fails


def control_vanish() -> list[str]:
    """A speed-0 friendly blocker walls the only corridor to the enemy.

    1x4 row: P_fast (speed 2) at 0, P_block (speed 0) at 1, E (value 1) at 3.
    The real game cannot remove the blocker; the vanish branch (which
    dominates pure movement) can, and it is the only branch that reaches E.
    """
    field = Battlefield(width=4, height=1)
    stacks = [
        Stack(_flat("Pfast", hp=5, speed=2), 1, side=0, slot=0, hex_=0),
        Stack(_flat("Pblock", hp=5, speed=0), 1, side=0, slot=1, hex_=1),
        Stack(_flat("E", hp=1, speed=1, value=1), 1, side=1, slot=0, hex_=3),
    ]
    with_v = _search_battle(Battle(field, [s.clone() for s in stacks]), 1)
    no_v = _search_battle(Battle(field, [s.clone() for s in stacks]), 1,
                          vanish=False)
    fails = []
    if with_v < 1:
        fails.append(f"vanish control: search with vanish scored {with_v}, "
                     f"expected 1")
    if no_v >= 1:
        fails.append(f"vanish control: search without vanish scored {no_v}, "
                     f"expected 0 -- the control no longer discriminates")
    return fails


def control_destination() -> list[str]:
    """The two-destination blocking gadget of test_regressions.destination_case.

    4x2 board; the valuable enemy is killable only if the first striker
    approaches from the non-canonical hex.  Exhaustive approach-hex branching
    scores 1, the first-spot-only degradation misses it.  (The gadget's
    original value 10 is set to 1: the admissible bound counts kills.)
    """
    field = Battlefield(width=4, height=2)
    player = CreatureType("P", 10, 10, 1, 1, hp=1, speed=1,
                          no_retaliation=True)
    quiet = CreatureType("quiet", 10, 10, 1, 1, hp=1, speed=0,
                         no_retaliation=True)
    valuable = CreatureType("valuable", 10, 10, 1, 1, hp=2, speed=0, value=1,
                            no_retaliation=True)
    stacks = [
        Stack(player, 1, side=0, slot=0, hex_=1),
        Stack(player, 2, side=0, slot=1, hex_=0),
        Stack(quiet, 1, side=1, slot=0, hex_=5),
        Stack(valuable, 1, side=1, slot=1, hex_=2),
    ]
    # vanish is disabled in BOTH runs: vanishing the hex-1 striker also frees
    # the canonical approach, which would mask the feature this control
    # isolates (the destination choice, not the vanish branch)
    exhaustive = _search_battle(Battle(field, [s.clone() for s in stacks]), 1,
                                vanish=False)
    first_only = _search_battle(Battle(field, [s.clone() for s in stacks]), 1,
                                vanish=False, all_spots=False)
    fails = []
    if exhaustive < 1:
        fails.append(f"destination control: exhaustive search scored "
                     f"{exhaustive}, expected 1")
    if first_only >= 1:
        fails.append(f"destination control: first-spot search scored "
                     f"{first_only}, expected < 1 -- the control no longer "
                     f"discriminates")
    return fails


# --- the corpus suite -------------------------------------------------------


def run_families(families, seed: int, label: str, want_def: int,
                 want_hp: int, verbose=True):
    """Every built family: X3C answer == fixed-order answer == free-order
    answer, over every allocation; yes-instances admit only the all-ones
    winner.  The constant set in force is asserted on the BUILT instance --
    enemy defence and player hp both (P12-12; round 13 codex Check 18 showed
    a builder ignoring the player hp while the module constant was right)."""
    rng = random.Random(seed)
    stats = {"built": 0, "skipped": 0, "yes": 0, "no": 0}
    fails = []
    for n_elements, sets in families:
        inst = V.build_instance(n_elements, sets, rng)
        if inst is None:
            stats["skipped"] += 1
            continue
        built = (inst["enemy_type"].defense, inst["player_type"].hp)
        if built != (want_def, want_hp):
            fails.append(f"{label} {sets}: built (enemy defence, player hp) "
                         f"= {built}, expected {(want_def, want_hp)} "
                         f"-- the constant swap did not reach the build")
            continue
        stats["built"] += 1
        geo = V.check_geometry(inst)
        if geo:
            fails += [f"{label} {sets}: {g}" for g in geo]
            continue
        want = V.x3c_is_yes(n_elements, sets)
        fixed = V.winning_allocations(inst)
        free = free_winning_allocations(inst)
        stats["yes" if want else "no"] += 1
        if bool(free) != want:
            fails.append(f"{label} {sets}: X3C={want} but free-order game="
                         f"{bool(free)} (allocs {free[:3]})")
        if bool(free) != bool(fixed) or (free and fixed and free != fixed):
            fails.append(f"{label} {sets}: fixed-order winners {fixed[:3]} != "
                         f"free-order winners {free[:3]}")
        if want and free != [(1,) * n_elements]:
            fails.append(f"{label} {sets}: free-order winners are {free[:5]}, "
                         f"expected only all-ones")
        if verbose:
            mark = "ok " if not fails else "FAIL"
            print(f"  {mark} [{label}] q={n_elements // 3} sets={len(sets)} "
                  f"X3C={'Y' if want else 'N'} free winners={len(free)}")
    return stats, fails


def negative_control(seed: int) -> tuple[int, list[str]]:
    """def(Q) = att(P) makes D(c) = c; the planar no-instance fixture must flip
    to yes under the free-order search, or the game search proves nothing."""
    rng = random.Random(seed)
    # every element covered, no exact cover (round 13, fable F-10: the old
    # fixture [(0,1,2), (0,1,3)] was a DEGENERATE no -- elements 4, 5 in no
    # set -- so its flip said less than it seemed to)
    sets = [(0, 1, 2), (2, 3, 4), (1, 4, 5)]
    n = 6
    if not all(any(e in s for s in sets) for e in range(n)):
        return 0, ["negative control: fixture is degenerate"]
    if V.x3c_is_yes(n, sets):
        return 0, ["negative control: fixture is a yes-instance of X3C"]
    fails = []
    flips = 0
    original = V.ENEMY_DEF
    try:
        V.ENEMY_DEF = V.PLAYER_ATT
        inst = V.build_instance(n, sets, rng)
        if inst is None:
            return 0, ["negative control: router could not build the fixture"]
        if free_winning_allocations(inst, stop_at_first=True):
            flips = 1
        else:
            fails.append("negative control: still a no-instance with the "
                         "resource lemma disabled -- the free-order search "
                         "would not notice losing it")
    finally:
        V.ENEMY_DEF = original
    if V.stack_damage(3) != 1:
        fails.append("negative control: failed to restore the enemy's defence")
    return flips, fails


def main() -> int:
    full = "--full" in sys.argv
    t0 = time.time()
    print("free-order search: any unacted player stack may act next "
          "(all permutations >= all WAIT-realizable orders); pass + vanish "
          "branches; exhaustive approach hexes; hold defence")

    fails = []
    totals = {"built": 0, "skipped": 0, "yes": 0, "no": 0}

    def add(stats):
        for k in totals:
            totals[k] += stats[k]

    # ONE corpus, searched under BOTH constant sets (nested, like
    # verify_embedding.py), the swap asserted at build time
    corpora = [(2, V.planted_instances(2, 1, 3, seed=41001)
                + V.random_instances(2, 4, 5, seed=41002))]
    if full:
        corpora.append((3, V.planted_instances(3, 1, 2, seed=41003)
                        + V.random_instances(3, 5, 3, seed=41004)))

    _trace_reset()
    for q, fams in corpora:
        stats, f = run_families(fams, seed=41, label=f"def 41 q={q}",
                                want_def=HIST_ENEMY_DEF,
                                want_hp=HIST_PLAYER_HP)
        add(stats); fails += f
        saved = with_sol_stats()
        try:
            assert V.ENEMY_DEF == SOL_ENEMY_DEF and V.PLAYER_HP == SOL_PLAYER_HP, \
                "with_sol_stats() did not swap the module constants"
            stats, f = run_families(fams, seed=41, label=f"published q={q}",
                                    want_def=SOL_ENEMY_DEF,
                                    want_hp=SOL_PLAYER_HP)
            add(stats); fails += f
        finally:
            restore(saved)
        assert V.ENEMY_DEF == HIST_ENEMY_DEF and V.PLAYER_HP == HIST_PLAYER_HP, \
            "restore() did not bring the historical constants back"

    # what the corpus tiers exercised -- snapshotted BEFORE the controls and
    # the negative control add their own expansions
    trace = dict(TRACE)
    if trace["reorder"] == 0:
        fails.append("corpus trace: no out-of-order activation was ever "
                     "expanded -- free order is not live on the corpus")
    if trace["vanish"] == 0:
        fails.append("corpus trace: no vanish branch was ever expanded -- "
                     "the pure-movement dominator is not live on the corpus")
    print(f"  corpus trace: {trace['reorder']} out-of-order activations, "
          f"{trace['vanish']} vanish branches, {trace['multi_spot']} states "
          f"with a second approach hex")

    controls = 0
    for ctrl in (control_order, control_vanish, control_destination):
        f = ctrl()
        fails += f
        if not f:
            controls += 1
    print(f"  discriminating controls: {controls}/3 pass "
          f"(order, vanish, destination -- full search strictly beats each "
          f"degraded search)")

    flips, f = negative_control(seed=99)
    fails += f

    dt = time.time() - t0
    if fails:
        print(f"FAILED ({len(fails)}):")
        for msg in fails:
            print(f"  - {msg}")
        return 1
    print(f"ALL PASS  (free-order: {totals['built']} built, {totals['yes']} yes"
          f" / {totals['no']} no, {totals['skipped']} skipped, one corpus x "
          f"both constant sets, every allocation, {controls} discriminating "
          f"controls, negative control flips {flips} no-instance, corpus "
          f"trace {trace['reorder']}/{trace['vanish']}/{trace['multi_spot']} "
          f"reorder/vanish/multi-spot, {dt:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
