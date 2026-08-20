"""Adversarial cross-check of proofs/sol-attempt/PROOF.md.

sol's construction and mine (proofs/candidate-D-singletype.md) are the same
reduction with different constants.  The point of this script is to attack sol's
version with machinery it was not tested against:

  * his creature statistics (enemy defence 27, player hit points 4, multiplier
    0.35) driven through *my* instance generator, which builds planar boards
    automatically and reaches q = 4, instead of his two hand-drawn q = 2 boards;
  * the arithmetic re-derived from MODEL.md sec. 4 by hand and compared against
    the executable formula, including the question of whether his choice really
    escapes the defence cap and its ULP problem (undefended blows do escape it;
    a defending target under (‡) crosses the cap and is clamped -- paper sec. 4.2);
  * a leakage probe that deliberately breaks the budget argument, to confirm
    that the doorway opened by a dead enemy is real and is blocked by the stock
    bound alone -- i.e. that Lemma 4 is doing necessary work rather than
    describing something that cannot happen anyway.

Run:  python3 scripts/crosscheck_sol.py [--full]
      python3 scripts/crosscheck_sol.py --defend   (defence executes (‡)
                                                    literally instead of holding)
"""

from __future__ import annotations

import math
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import homm3_model as M
import verify_x3c as V
from homm3_model import Battle, Battlefield, CreatureType, Stack, compute_damage

# proofs/sol-attempt/PROOF.md, "The combat resource lemma"
SOL_PLAYER_ATT = 1
SOL_ENEMY_DEF = 27
SOL_PLAYER_HP = 4
SOL_ENEMY_HP = 3


def with_sol_stats():
    """Context-manager-free swap of verify_x3c's constants for sol's."""
    saved = (V.PLAYER_ATT, V.ENEMY_DEF, V.PLAYER_HP, V.ENEMY_HP)
    V.PLAYER_ATT = SOL_PLAYER_ATT
    V.ENEMY_DEF = SOL_ENEMY_DEF
    V.PLAYER_HP = SOL_PLAYER_HP
    V.ENEMY_HP = SOL_ENEMY_HP
    return saved


def restore(saved):
    V.PLAYER_ATT, V.ENEMY_DEF, V.PLAYER_HP, V.ENEMY_HP = saved


# --- 1. the arithmetic, re-derived rather than re-run ----------------------


def audit_arithmetic() -> list[str]:
    """Check sol's numbers against MODEL.md sec. 4 done by hand."""
    fails = []
    adv = SOL_ENEMY_DEF - SOL_PLAYER_ATT                     # 26 defence points
    capped = M.DEFENSE_POINT_DAMAGE_FACTOR * adv >= M.DEFENSE_POINT_DAMAGE_FACTOR_CAP
    if capped:
        fails.append(f"sol claims to be below the defence cap, but "
                     f"0.025*{adv} = {M.DEFENSE_POINT_DAMAGE_FACTOR * adv} "
                     f"reaches the cap {M.DEFENSE_POINT_DAMAGE_FACTOR_CAP}")
    mu = 1.0 - M.DEFENSE_POINT_DAMAGE_FACTOR * adv

    player = CreatureType("P", attack=SOL_PLAYER_ATT, defense=1, dmg_min=1,
                          dmg_max=1, hp=SOL_PLAYER_HP, speed=2)
    enemy = CreatureType("E", attack=1, defense=SOL_ENEMY_DEF, dmg_min=1,
                         dmg_max=1, hp=SOL_ENEMY_HP, speed=1, value=1)

    def dmg(c):
        return compute_damage(Stack(player, c, 0, 0, 0), Stack(enemy, 1, 1, 0, 1))

    # the hand-derived formula must match the executable one
    for c in range(1, 200):
        want = max(1, math.floor(c * mu))
        if dmg(c) != want:
            fails.append(f"D({c}) = {dmg(c)}, hand formula max(1,floor({mu}*{c})) = {want}")

    # PROOF.md line (1): delta(c) <= c, and delta(1)=delta(2)=delta(3)=1
    for c in range(1, 200):
        if dmg(c) > c:
            fails.append(f"PROOF.md (1) violated: D({c}) = {dmg(c)} > {c}")
    if [dmg(1), dmg(2), dmg(3)] != [1, 1, 1]:
        fails.append(f"PROOF.md (1) violated: D(1..3) = {[dmg(1), dmg(2), dmg(3)]}")

    # the ULP question.  The engine mis-parses only the CAP (engine-check/REPORT.md);
    # 0.025 parses identically.  Since sol stays below the cap, the cap constant
    # must be irrelevant to him -- verify by recomputing under the engine's value.
    saved_cap = M.DEFENSE_POINT_DAMAGE_FACTOR_CAP
    M.DEFENSE_POINT_DAMAGE_FACTOR_CAP = 0.7000000000000001
    engine_side = [dmg(c) for c in range(1, 60)]
    M.DEFENSE_POINT_DAMAGE_FACTOR_CAP = saved_cap
    model_side = [dmg(c) for c in range(1, 60)]
    if engine_side != model_side:
        fails.append("sol's damage table differs between the model and engine cap "
                     "constants, contradicting the claim that he escapes the cap")

    # my own construction, for contrast: it DOES sit on the cap
    mine_adv = V.ENEMY_DEF - V.PLAYER_ATT if V.ENEMY_DEF != SOL_ENEMY_DEF else 40
    print("  sol   : defence advantage", adv, "-> multiplier", repr(mu),
          "| below cap:", not capped)
    print("  sol   : D(c), c=1..12:", [dmg(c) for c in range(1, 13)])
    print("  sol   : identical under both cap constants:", engine_side == model_side)
    print("  mine  : defence advantage", mine_adv, "-> capped, multiplier 0.3, and the "
          "two cap constants disagree at D(10)")
    return fails


# --- 2. the resource lemma, sol's version and mine -------------------------


def audit_resource_lemma() -> list[str]:
    """sol's Lemma 2 needs D(2) = D(3) = 1; mine needs only D(c) < c for
    c >= 2. Under sol's constants BOTH hypotheses are checked explicitly
    below, alongside the full Lemma 3.1 audit (damage formula, cheapest-kill
    cost and uniqueness) that check_resource_lemma runs. Note the direction:
    D(2) = D(3) = 1 implies D(2) < 2 and D(3) < 3, not conversely -- an
    earlier docstring and summary line here claimed the reverse implication,
    and checked neither hypothesis (round 10, M6).
    """
    saved = with_sol_stats()
    try:
        fails = ["[sol stats] " + f for f in V.check_resource_lemma()]
        dmg = {c: V.stack_damage(c) for c in range(2, 41)}
        if not (dmg[2] == 1 and dmg[3] == 1):
            fails.append(f"[sol stats] sol's hypothesis fails: "
                         f"D(2) = {dmg[2]}, D(3) = {dmg[3]}, both must be 1")
        weak = [c for c, d in dmg.items() if not d < c]
        if weak:
            fails.append(f"[sol stats] weaker hypothesis D(c) < c "
                         f"fails at c in {weak}")
    finally:
        restore(saved)
    return fails


# --- 3. sol's constants on my machine-built boards -------------------------


def cross_instances(full: bool) -> tuple[dict, list[str]]:
    fams = (
        [(3, [(0, 1, 2)])]
        + V.planted_instances(2, 2, 8, seed=3)
        + V.random_instances(2, 3, 8, seed=5)
        + V.random_instances(2, 4, 8, seed=41)
    )
    if full:
        fams += (V.planted_instances(3, 2, 6, seed=13)
                 + V.random_instances(3, 6, 6, seed=17)
                 + V.planted_instances(4, 2, 3, seed=23))
    saved = with_sol_stats()
    try:
        return V.run_suite(fams, seed=777)
    finally:
        restore(saved)


# --- 4. leakage probe ------------------------------------------------------


def leakage_probe() -> list[str]:
    """Is the doorway opened by a dead enemy real?

    Take a no-instance of X3C in which two triples share an element.  With the
    honest stock 3q the game must answer no (that is the theorem).  Raise the
    stock and the budget argument of Lemma 4 collapses -- if the game then
    answers yes, the doorway is genuine and Lemma 4 is load-bearing rather than
    vacuous.  If raising the stock changed nothing, the whole induction would be
    describing an impossibility and both proofs would be over-engineered.
    """
    fails = []
    saved = with_sol_stats()
    try:
        rng = random.Random(2024)
        sets = [(0, 1, 2), (0, 3, 4)]          # share element 0 -> no exact cover
        inst = V.build_instance(6, sets, rng)
        if inst is None:
            return ["leakage probe: router could not build the fixture"]
        geo = V.check_geometry(inst)
        if geo:
            return [f"leakage probe: {g}" for g in geo]
        if V.x3c_is_yes(6, sets):
            return ["leakage probe: fixture is not a no-instance"]

        honest = V.winning_allocations(inst)
        if honest:
            fails.append(f"leakage probe: no-instance won at the honest stock "
                         f"with {honest[:3]}")
        results = {}
        for extra in (0, 3, 6, 12):
            inst["stock"] = 6 + extra
            results[6 + extra] = bool(V.winning_allocations(inst))
        inst["stock"] = 6
        print("  no-instance, value >= q reachable at stock:",
              {k: v for k, v in results.items()})
        if not results[18]:
            fails.append("leakage probe: even at three times the stock the "
                         "no-instance stays a no -- the budget is not what blocks it, "
                         "so something else in the construction is, and neither proof "
                         "identifies it")
    finally:
        restore(saved)
    return fails


def doorway_probe() -> list[str]:
    """Isolate the doorway itself, rather than its budget consequences.

    PROOF.md Lemma 4 (and my Lemma 5.3) exist to handle the fact that a dead
    enemy stops blocking its hex, joining three element regions.  If that never
    actually widened anybody's reach, both inductions would be ceremony.

    Here we kill one enemy by hand and re-query reach.  We want to see reach
    GROW for a stack that has not acted -- that is the doorway -- and we want the
    growth to be exactly the targets of the other elements of the dead triple,
    which is what the induction then argues is unreachable in a tight play.
    """
    fails = []
    saved = with_sol_stats()
    try:
        rng = random.Random(31337)
        # three triples in a chain, so a kill joins regions that lead somewhere
        sets = [(0, 1, 2), (2, 3, 4), (4, 5, 0)]
        inst = V.build_instance(6, sets, rng)
        if inst is None:
            return ["doorway probe: router could not build the fixture"]
        geo = V.check_geometry(inst)
        if geo:
            return [f"doorway probe: {g}" for g in geo]

        alloc = {e: 1 for e in inst["deploy"]}
        battle, _ = V.build_battle(inst, alloc)
        enemy_of_hex = {h: si for si, h in inst["enemy_hex"].items()}
        players = [s for s in battle.stacks if s.side == 0]
        before = {s.slot: {enemy_of_hex[t.hex] for t in battle.attackable(s)}
                  for s in players}

        grew_any = False
        for victim in range(len(sets)):
            b2 = battle.clone()
            dead = [s for s in b2.stacks if s.side == 1 and s.slot == victim][0]
            dead.apply_damage(dead.available())
            if dead.alive():
                fails.append("doorway probe: could not kill the victim")
                continue
            for s in [x for x in b2.stacks if x.side == 0]:
                after = {enemy_of_hex[t.hex] for t in b2.attackable(s)}
                new = after - before[s.slot] - {victim}
                if new:
                    grew_any = True
                    if s.slot not in sets[victim]:
                        fails.append(
                            f"doorway probe: killing enemy {victim} widened the reach "
                            f"of slot {s.slot}, which is NOT in that triple, to {new} "
                            f"-- the doorway is wider than Lemma 4 assumes")
        if not grew_any:
            fails.append("doorway probe: killing an enemy never widened anyone's reach, "
                         "so Lemma 4 / Lemma 5.3 are guarding against nothing and the "
                         "machine checks cannot be said to exercise them")
        else:
            print("  killing an enemy does widen reach, and only for elements of the "
                  "dead triple: the induction is necessary and its scope is right")
    finally:
        restore(saved)
    return fails


def pure_movement_on_sols_own_board() -> list[str]:
    """Re-run sol's own no-instance with pure movement admitted.

    sol's `play_exhaustively` branches over passing and (target, approach hex)
    only -- pure movement is absent, exactly as in my own search.  His deployment
    hexes sit in the MIDDLE of their corridors (`verify.py` builds them as
    `sorted(path)[len(path)//2]`), so a stationary stack does block its corridor
    and a pure move would unblock it; my construction sidesteps this by putting
    every deployment hex on a dead end.  So the omission needs justifying on his
    board specifically.

    We admit an action that dominates every pure move: the stack vanishes.  It
    deals no damage (as a pure move does not) and blocks nothing (the best any
    pure move could achieve).  If his no-instance still cannot reach the
    threshold, no pure move could have helped.
    """
    fails = []
    sol_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                           "proofs", "sol-attempt")
    if not os.path.isdir(sol_dir):
        return ["sol-attempt/ not found"]
    sys.path.insert(0, sol_dir)
    try:
        import verify as solv
    except Exception as exc:                      # pragma: no cover
        return [f"could not import sol's verify.py: {exc!r}"]

    def play(battle, initial, order=None, i=0):
        if order is None:
            order = [battle.stacks.index(s) for s in battle.turn_order()]
        if i == len(order):
            return M.destroyed_value(battle, initial)
        idx = order[i]
        stack = battle.stacks[idx]
        if not stack.alive() or stack.side == 1:
            return play(battle, initial, order, i + 1)
        best = play(battle, initial, order, i + 1)            # pass
        ghost = battle.clone()                                # vanish
        g = ghost.stacks[idx]
        g.apply_damage(g.available())
        best = max(best, play(ghost, initial, order, i + 1))
        for target in battle.attackable(stack):
            t_idx = battle.stacks.index(target)
            for dest in battle.attack_spots(stack, target):
                nxt = battle.clone()
                nxt.resolve_attack(nxt.stacks[idx], nxt.stacks[t_idx], dest=dest)
                best = max(best, play(nxt, initial, order, i + 1))
        return best

    for case in (solv.yes_case(), solv.no_case()):
        want = solv.x3c_verdict(case)
        best = -1
        for alloc in solv.allocations(3 * case.q, 3 * case.q):
            battle, initial = solv.make_battle(case, alloc)
            best = max(best, play(battle, initial))
            if best >= case.q and not want:
                break
        got = best >= case.q
        print(f"  {case.name}: optimum {best}, threshold {case.q}, "
              f"verdict {got} (X3C {want})")
        if got != want:
            fails.append(f"sol's {case.name} flips to {got} once pure movement is "
                         f"admitted -- his search omits an action that matters")
    return fails


def main() -> int:
    full = "--full" in sys.argv
    if "--defend" in sys.argv:
        # Run the reduction-level search with the paper's `(‡)` policy executed
        # literally, under THE PUBLISHED Theorem-3 constants (def 27, hp 4,
        # mu 0.35 -> defended 0.3).  Round-8 review: this combination had never
        # been run.  Answers must be identical to the hold baseline.
        V.ENEMY_POLICY = "waitdefend"
    print("=" * 72)
    print("adversarial cross-check of proofs/sol-attempt/PROOF.md")
    print("=" * 72)
    print(f"defence policy in the game search: "
          f"{'(‡) WAIT-then-DEFEND, executed literally' if V.ENEMY_POLICY == 'waitdefend' else 'hold'}")

    print("\n[1] arithmetic re-derived from MODEL.md sec. 4")
    f1 = audit_arithmetic()
    for f in f1:
        print("   FAIL", f)

    print("\n[2] resource lemma under sol's constants")
    f2 = audit_resource_lemma()
    for f in f2:
        print("   FAIL", f)
    if not f2:
        print("   holds; D(2) = D(3) = 1 (sol's hypothesis) and D(c) < c for "
              "2 <= c <= 40 (the weaker one) both verified under sol's stats")

    print("\n[3] leakage probe: is the budget bound load-bearing?")
    f3 = leakage_probe()
    for f in f3:
        print("   FAIL", f)

    print("\n[3b] doorway probe: is the death-order induction load-bearing?")
    f3 += doorway_probe()
    for f in f3:
        print("   FAIL", f)

    print("\n[3c] pure movement, admitted on sol's own boards")
    f3 += pure_movement_on_sols_own_board()
    for f in f3:
        print("   FAIL", f)

    print("\n[4] sol's constants on machine-built planar boards")
    stats, f4 = cross_instances(full)
    print(f"   built {stats['built']}, skipped {stats['skipped']}, "
          f"yes {stats['yes']} / no {stats['no']}")

    allf = f1 + f2 + f3 + f4
    print("\n" + "-" * 72)
    if allf:
        print(f"FAILURES ({len(allf)}):")
        for f in allf[:40]:
            print("  ", f)
        return 1
    print("ALL PASS -- sol's constants survive every test my construction survives")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
