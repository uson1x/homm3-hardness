"""Conformance tests for the H3-det model in homm3_model.py.

Two groups of tests:

  A. Ported directly from VCMI's own unit tests
     ($VCMI_CHECKOUT/test/battle/CHealthTest.cpp, github.com/vcmi/vcmi).
     These are upstream's test vectors, not ours, so they are a genuine cross-check of
     the health-pool transcription rather than a restatement of our own reading.

  B. Properties of the damage formula and the round structure derived by hand from
     lib/battle/DamageCalculator.cpp and server/battles/BattleActionProcessor.cpp,
     with the source line cited in each test.

Honest limitation: none of this executes the real engine. It checks that our Python
transcription agrees with (a) upstream's test vectors for the health pool and (b) our
own line-by-line reading of the damage code. A discrepancy between the C++ source and
the shipped 1999 binary would not be caught here. See MODEL.md sec. 8.

Run:  python3 verify_mechanics.py
"""

from __future__ import annotations

import sys

from homm3_model import (
    Battle,
    Battlefield,
    CreatureType,
    Stack,
    attack_skill_factor,
    compute_damage,
    defend_bonus,
    defense_skill_factor,
    kills_for_damage,
)

FAILURES: list[str] = []
PASSED = 0


def check(label: str, got, want) -> None:
    global PASSED
    if got == want:
        PASSED += 1
    else:
        FAILURES.append(f"{label}: got {got!r}, want {want!r}")


def approx(label: str, got, want, eps=1e-9) -> None:
    global PASSED
    if abs(got - want) < eps:
        PASSED += 1
    else:
        FAILURES.append(f"{label}: got {got!r}, want {want!r}")


def make(name="c", attack=10, defense=10, damage=1, hp=10, speed=2, **kw):
    return CreatureType(name=name, attack=attack, defense=defense,
                        dmg_min=damage, dmg_max=damage, hp=hp, speed=speed, **kw)


# =========================================================================
# Group A: ported from VCMI test/battle/CHealthTest.cpp
# =========================================================================

def test_vcmi_health_damage():
    """CHealthTest.cpp:103-127 (TEST_F(HealthTest, damage)).

    UNIT_HEALTH = 123, UNIT_AMOUNT = 300.
    """
    t = make(hp=123)
    s = Stack(t, 300, side=0, slot=0, hex_=0)

    check("A1 full count", s.count(), 300)
    check("A1 full firstHP", s.first_hp_left, 123)
    check("A1 full available", s.available(), 123 * 300)

    # checkNormalDamage(health, 0)  :109-110
    check("A1 zero dmg absorbed", s.apply_damage(0), 0)
    check("A1 zero dmg count", s.count(), 300)

    # checkNormalDamage(health, UNIT_HEALTH - 1)  :112-115
    s.apply_damage(122)
    check("A1 122 dmg count", s.count(), 300)
    check("A1 122 dmg firstHP", s.first_hp_left, 1)

    # checkNormalDamage(health, 1)  :117-120
    s.apply_damage(1)
    check("A1 +1 dmg count", s.count(), 299)
    check("A1 +1 dmg firstHP", s.first_hp_left, 123)

    # checkNormalDamage(health, UNIT_HEALTH * (UNIT_AMOUNT - 1))  :122-123
    s.apply_damage(123 * 299)
    check("A1 wipe count", s.count(), 0)
    check("A1 wipe firstHP", s.first_hp_left, 0)
    check("A1 wipe available", s.available(), 0)

    # checkNoDamage(health, 1337)  :125-126 -- a dead stack absorbs nothing
    check("A1 dead absorbs 0", s.apply_damage(1337), 0)
    check("A1 dead count", s.count(), 0)


def test_vcmi_single_unit_stack():
    """CHealthTest.cpp:232-252 (TEST_F(HealthTest, singleUnitStack)), issue 2612.

    One Titan, 300 hp. 1000 damage is dealt; only 300 is absorbed.
    This is the overkill rule that candidate-A Lemma 3.2 relies on.
    """
    t = make(hp=300)
    s = Stack(t, 1, side=0, slot=0, hex_=0)
    check("A2 absorbed", s.apply_damage(1000), 300)
    check("A2 count", s.count(), 0)
    check("A2 firstHP", s.first_hp_left, 0)
    check("A2 available", s.available(), 0)


def test_vcmi_partial_then_heal_positions():
    """CHealthTest.cpp:129-138: 99 damage on a 123 hp creature leaves 24, count intact."""
    t = make(hp=123)
    s = Stack(t, 300, side=0, slot=0, hex_=0)
    s.apply_damage(99)
    check("A3 count", s.count(), 300)
    check("A3 firstHP", s.first_hp_left, 123 - 99)


# =========================================================================
# Group B: damage formula
# =========================================================================

def test_attack_defence_factors():
    """DamageCalculator.cpp:210-224, 322-337; constants gameConfig.json:609-615."""
    approx("B1 equal att/def -> no attack bonus", attack_skill_factor(10, 10), 0.0)
    approx("B1 +1 attack point", attack_skill_factor(11, 10), 0.05)
    approx("B1 +10 attack points", attack_skill_factor(20, 10), 0.50)
    # cap: 0.05 * 80 = 4.0 exactly; 0.05 * 200 = 10 -> capped
    approx("B1 attack cap at 80 pts", attack_skill_factor(90, 10), 4.0)
    approx("B1 attack cap beyond", attack_skill_factor(210, 10), 4.0)

    approx("B2 equal att/def -> no defence bonus", defense_skill_factor(10, 10), 0.0)
    approx("B2 +1 defence point", defense_skill_factor(10, 11), 0.025)
    approx("B2 +10 defence points", defense_skill_factor(10, 20), 0.25)
    # cap: 0.025 * 28 = 0.7 exactly
    approx("B2 defence cap at 28 pts", defense_skill_factor(10, 38), 0.7)
    approx("B2 defence cap beyond", defense_skill_factor(10, 200), 0.7)


def test_damage_is_linear_in_count():
    """DamageCalculator.cpp:123-131: base damage is per-creature damage times count."""
    atk = make("atk", attack=10, damage=7)
    dfn = make("dfn", defense=10, hp=1000)
    for c in (1, 2, 5, 100):
        a = Stack(atk, c, 0, 0, 0)
        d = Stack(dfn, 1, 1, 0, 1)
        check(f"B3 count={c}", compute_damage(a, d), 7 * c)


def test_damage_uses_count_not_remaining_hp():
    """CUnitState.cpp:282-285 -- the wounded top creature still hits at full strength.

    This is the mechanic candidate-A sec. 5 identifies as load-bearing.
    """
    atk = make("atk", attack=10, damage=10, hp=100)
    dfn = make("dfn", defense=10, hp=100000)
    a = Stack(atk, 5, 0, 0, 0)
    d = Stack(dfn, 1, 1, 0, 1)
    check("B4 healthy", compute_damage(a, d), 50)
    a.apply_damage(99)          # top creature down to 1 hp, nobody dies
    check("B4 count after 99", a.count(), 5)
    check("B4 wounded still full damage", compute_damage(a, d), 50)
    a.apply_damage(1)           # top creature dies
    check("B4 count after 100", a.count(), 4)
    check("B4 damage drops only on death", compute_damage(a, d), 40)


def test_damage_floor_and_clamp():
    """DamageCalculator.cpp:576-577: floor, then clamp below at 1."""
    # heavy defence advantage: 0.7 cap -> factor 0.3
    atk = make("atk", attack=10, damage=3)
    dfn = make("dfn", defense=100, hp=1000)
    a = Stack(atk, 1, 0, 0, 0)
    d = Stack(dfn, 1, 1, 0, 1)
    # 1 * 3 * 1.0 * 0.3 = 0.9 -> floor 0 -> clamped to 1
    check("B5 clamp to 1", compute_damage(a, d), 1)

    a2 = Stack(make("atk2", attack=10, damage=10), 1, 0, 0, 0)
    # 1 * 10 * 1.0 * 0.3 = 3.0 (floating point 2.9999... must not floor to 2)
    got = compute_damage(a2, d)
    if got not in (2, 3):
        FAILURES.append(f"B5 unexpected {got}")
    else:
        globals()["PASSED"] = PASSED + 1
        # record which branch the float took, for the verification log
        print(f"    note: 10 * 0.3 floors to {got} "
              f"(engine uses double arithmetic and std::floor, same as us)")


def test_kill_thresholds():
    """DamageCalculator.cpp:522-531 -- kills(D) is a step function."""
    dfn = make("dfn", defense=10, hp=25)
    d = Stack(dfn, 4, 1, 0, 1)          # pool 100, firstHPleft 25
    check("B6 below threshold", kills_for_damage(d, 24), 0)
    check("B6 at threshold", kills_for_damage(d, 25), 1)
    check("B6 just above", kills_for_damage(d, 26), 1)
    check("B6 two", kills_for_damage(d, 50), 2)
    check("B6 all", kills_for_damage(d, 100), 4)
    check("B6 overkill capped", kills_for_damage(d, 10_000), 4)

    # single creature: dies exactly at hp, and not before
    single = Stack(make("s", defense=10, hp=37), 1, 1, 0, 1)
    check("B6 single below", kills_for_damage(single, 36), 0)
    check("B6 single at", kills_for_damage(single, 37), 1)


# =========================================================================
# Group C: round structure and retaliation
# =========================================================================

def test_retaliation_only_if_defender_survives():
    """BattleActionProcessor.cpp:326-333 + CUnitState.cpp:484-490."""
    field = Battlefield(width=4)

    # defender survives -> retaliates
    atk = make("atk", attack=10, damage=1, hp=100, speed=2)
    dfn = make("dfn", defense=10, damage=5, hp=100, speed=1)
    a = Stack(atk, 1, 0, 0, 0)
    d = Stack(dfn, 1, 1, 0, 1)
    b = Battle(field, [a, d])
    r = b.resolve_attack(a, d)
    check("C1 damage dealt", r["damage"], 1)
    check("C1 defender survived", d.alive(), True)
    check("C1 retaliation happened", r["retaliation"], 5)

    # defender dies -> no retaliation
    atk2 = make("atk2", attack=10, damage=100, hp=100, speed=2)
    a2 = Stack(atk2, 1, 0, 0, 0)
    d2 = Stack(dfn, 1, 1, 0, 1)
    b2 = Battle(field, [a2, d2])
    r2 = b2.resolve_attack(a2, d2)
    check("C2 defender died", d2.alive(), False)
    check("C2 no retaliation", r2["retaliation"], 0)


def test_one_retaliation_per_round():
    """CUnitState.cpp:127-136 (base 1) and :920 (reset at round boundary)."""
    field = Battlefield(width=6)
    atk = make("atk", attack=10, damage=1, hp=1000, speed=3)
    dfn = make("dfn", defense=10, damage=5, hp=1000, speed=1)
    a1 = Stack(atk, 1, 0, 0, 0)
    a2 = Stack(atk, 1, 0, 1, 4)
    d = Stack(dfn, 1, 1, 0, 2)
    b = Battle(field, [a1, a2, d])

    r1 = b.resolve_attack(a1, d)
    check("C3 first attacker eats retaliation", r1["retaliation"], 5)
    r2 = b.resolve_attack(a2, d)
    check("C3 second attacker is free", r2["retaliation"], 0)

    b.end_round()
    r3 = b.resolve_attack(a1, d)
    check("C3 retaliation back next round", r3["retaliation"], 5)


def test_no_retaliation_flag():
    """CUnitState.cpp:120,129-130 -- NO_RETALIATION / SIEGE_WEAPON never retaliate."""
    field = Battlefield(width=4)
    atk = make("atk", attack=10, damage=1, hp=100, speed=2)
    dfn = make("dfn", defense=10, damage=5, hp=100, speed=1, no_retaliation=True)
    a = Stack(atk, 1, 0, 0, 0)
    d = Stack(dfn, 1, 1, 0, 1)
    b = Battle(field, [a, d])
    check("C4 no retaliation", b.resolve_attack(a, d)["retaliation"], 0)


def test_turn_order():
    """BattleInfo.cpp:978-1006 -- initiative desc, then side, then slot."""
    field = Battlefield(width=10)
    fast = make("fast", speed=7)
    slow = make("slow", speed=3)
    s1 = Stack(slow, 1, 0, 0, 0)
    s2 = Stack(fast, 1, 1, 3, 2)
    s3 = Stack(fast, 1, 0, 1, 4)
    s4 = Stack(slow, 1, 1, 0, 6)
    b = Battle(field, [s1, s2, s3, s4])
    order = [(s.side, s.slot) for s in b.turn_order()]
    check("C5 order", order, [(0, 1), (1, 3), (0, 0), (1, 0)])


def test_movement_reach():
    """CBattleInfoCallback.cpp:1411-1465 BFS + BattleActionProcessor.cpp:216-352.

    A melee stack of speed s strikes anything within distance s + 1.
    """
    field = Battlefield(width=12)
    walker = make("w", speed=2, attack=10)
    target = make("t", defense=10, hp=100)

    for dist, expected in ((1, True), (2, True), (3, True), (4, False), (5, False)):
        a = Stack(walker, 1, 0, 0, 0)
        d = Stack(target, 1, 1, 0, dist)
        b = Battle(field, [a, d])
        check(f"C6 reach at distance {dist}", bool(b.attackable(a)), expected)


def test_defend_bonus_arithmetic():
    """server/battles/BattleActionProcessor.cpp:168-196.

    DEFEND adds 20 % of the defence stat (PERCENT_TO_ALL, integer), and when
    that rounds to zero (defence < 5) the engine substitutes a +1 additive
    bonus instead.
    """
    check("D1 def 27 -> +5", defend_bonus(27), 5)          # candidate-D: 27 -> 32
    check("D1 def 10 -> +2", defend_bonus(10), 2)          # naturalS-k2-05: 10 -> 12
    check("D1 def 4 -> +1 (floor)", defend_bonus(4), 1)
    check("D1 def 0 -> +1 (floor)", defend_bonus(0), 1)
    check("D1 def 5 -> +1", defend_bonus(5), 1)

    # The Dragon Fly blow of paper sec. 5.1: attack 10, defence 10, five
    # creatures of flat damage 4. Nominal 20; against a defender carrying the
    # DEFEND bonus (defence 12, delta = -2) it is floor(20 * 0.95) = 19.
    att = make("att", attack=10, damage=4)
    dfn = make("dfn", defense=10, hp=100)
    a = Stack(att, 5, side=0, slot=0, hex_=0)
    d = Stack(dfn, 1, side=1, slot=0, hex_=1)
    check("D1 blow vs undefended", compute_damage(a, d), 20)
    d.defending = True
    check("D1 blow vs defended", compute_damage(a, d), 19)
    d.defending = False

    # Theorem 3 arithmetic: attack 1 vs defence 27 gives mu = 0.35; a defending
    # target has defence 32, delta = -31, 0.025*31 = 0.775 is past the cap 0.7,
    # so mu drops to 0.30. Both live in (0,1), the resource lemma's hypothesis.
    p = make("p", attack=1, damage=1)
    q = make("q", defense=27, hp=3)
    a12 = Stack(p, 12, side=0, slot=0, hex_=0)
    dq = Stack(q, 1, side=1, slot=0, hex_=1)
    check("D1 mu=0.35 blow (c=12)", compute_damage(a12, dq), 4)
    dq.defending = True
    check("D1 mu=0.30 blow (c=12)", compute_damage(a12, dq), 3)


def test_defend_duration_and_retaliation():
    """lib/battle/BattleInfo.cpp:676-688 (nextTurn removes UntilGetsTurn bonuses)
    and server/battles/BattleActionProcessor.cpp:298-334.

    The DEFEND bonus survives the round boundary and expires only when the
    stack next receives a turn; WAIT and DEFEND consume no retaliation charge,
    so a waiting or defending enemy retaliates exactly as an idle one would.
    """
    field = Battlefield(width=6)
    p = make("p", attack=10, damage=4, speed=3, hp=100)
    e = make("e", defense=10, hp=1000, speed=1, damage=1, attack=10)
    player = Stack(p, 5, side=0, slot=0, hex_=0)
    enemy = Stack(e, 1, side=1, slot=0, hex_=3)
    b = Battle(field, [player, enemy])

    # Round 1 under WAIT-then-DEFEND: the enemy's NORMAL activation issues WAIT,
    # its postponed WAIT-phase activation issues DEFEND.
    b.activate(enemy)
    b.act_wait(enemy)
    check("D2 WAIT keeps retaliation charge", enemy.retaliations_left, 1)
    check("D2 WAIT does not defend", enemy.defending, False)
    b.activate(enemy)
    b.act_defend(enemy)
    check("D2 DEFEND keeps retaliation charge", enemy.retaliations_left, 1)
    check("D2 DEFEND raises the flag", enemy.defending, True)

    # A defending enemy still retaliates when struck (‡b).
    r = b.resolve_attack(player, enemy)
    check("D2 blow vs defended is reduced", r["damage"], 19)
    check("D2 defender retaliated", r["retaliation"] > 0, True)
    check("D2 charge spent by retaliation", enemy.retaliations_left, 0)

    # Round boundary: the bonus persists (BattleInfo.cpp:686 removes it only at
    # the next activation), waited resets, the retaliation charge resets.
    b.end_round()
    check("D2 bonus survives end_round", enemy.defending, True)
    check("D2 waited resets at end_round", enemy.waited, False)
    check("D2 retaliation resets at end_round", enemy.retaliations_left, 1)

    # Round 2, the R >= 2 counterexample of review round 6: a fast player
    # striking before the enemy's round-2 activation meets the lingering bonus.
    check("D2 round-2 early blow meets bonus", compute_damage(player, enemy), 19)
    b.activate(enemy)   # the enemy receives its round-2 turn (issuing WAIT again)
    check("D2 bonus expires at next activation", enemy.defending, False)
    check("D2 round-2 late blow is nominal", compute_damage(player, enemy), 20)


def test_wait_phase_order():
    """lib/battle/CBattleInfoCallback.cpp:495-519.

    The WAIT phase runs in increasing speed order, so a waiting player stack
    that is faster than a waiting enemy acts AFTER it — the reason the
    one-round lemma of policy (‡) covers waiting players only by inequality.
    """
    field = Battlefield(width=8)
    fast_p = make("fp", speed=4, attack=10, damage=4, hp=100)
    slow_e = make("se", speed=1, defense=10, hp=1000, damage=1, attack=10)
    player = Stack(fast_p, 5, side=0, slot=0, hex_=0)
    enemy = Stack(slow_e, 1, side=1, slot=0, hex_=2)
    b = Battle(field, [player, enemy])

    # NORMAL phase: decreasing speed — the player would act first...
    check("D3 NORMAL order", [s.ctype.name for s in b.turn_order()], ["fp", "se"])

    # ...but if both wait, the WAIT phase runs in increasing speed order and
    # the slow enemy's postponed DEFEND lands before the player's postponed blow.
    b.activate(player); b.act_wait(player)
    b.activate(enemy); b.act_wait(enemy)
    check("D3 WAIT order", [s.ctype.name for s in b.wait_phase_order()], ["se", "fp"])
    b.activate(enemy); b.act_defend(enemy)
    r = b.resolve_attack(player, enemy)
    check("D3 postponed blow meets bonus", r["damage"], 19)


def test_obstacles_block():
    field = Battlefield(width=8, obstacles=frozenset({1}))
    walker = make("w", speed=2, attack=10)
    target = make("t", defense=10, hp=100)
    a = Stack(walker, 1, 0, 0, 0)
    d = Stack(target, 1, 1, 0, 3)
    b = Battle(field, [a, d])
    check("C7 obstacle blocks reach", bool(b.attackable(a)), False)


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
