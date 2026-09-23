"""Exact-rational damage, and a dual-arithmetic instrumentation of the reference
simulator (review round 14, gpt-6-astra pro, finding F2).

MODEL.md section 4 ("Arithmetic semantics") defines the *mathematical* damage
formula over the exact rationals 1/20, 4, 1/40, 7/10 with an exact integer
floor, while `homm3_model.compute_damage` -- the operative definition of every
empirical optimum in `empirics/` -- evaluates the same formula in Python
floats.  The two do NOT agree everywhere: `0.025 * 12` is the double
0.30000000000000004 and `1 - 0.30000000000000004` is the double nearest 0.7,
which lies BELOW 7/10, so a defended blow of base 90 against attack 0 /
defence 10 (effective defence 12) floors to 62 in floats and to 63 exactly;
on a grid of attack and defence in 0..60, base in 1..2000 and both DEFEND
states the two arithmetics split on 93 983 of 14 884 000 cells (round 14).
Whether the empirical corpus ever crosses such a boundary is therefore a
question to be MEASURED, not asserted.

`exact_compute_damage` is the exact-rational formula.  `install_dual` replaces
`compute_damage` in the model module and in every module that bound the name
at import (`solve`, like `check_ability_shift.py` does) by a wrapper that
evaluates BOTH arithmetics on every call, records the counts and every
disagreement, and returns the float result -- so an instrumented suite runs
exactly the computation the paper reports, and the trace says whether the
exact semantics would have said anything different.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

import homm3_model as M

ATTACK_FACTOR = Fraction(1, 20)
ATTACK_CAP = Fraction(4)
DEFENSE_FACTOR = Fraction(1, 40)
DEFENSE_CAP = Fraction(7, 10)


def exact_factors(attack: int, def_eff: int, shooting: bool,
                  shooter: bool, no_melee_penalty: bool
                  ) -> tuple[Fraction, Fraction]:
    """(attackFactorTotal, defenseFactorTotal) over the exact rationals."""
    adv = attack - def_eff
    attack_total = Fraction(1) + (min(ATTACK_FACTOR * adv, ATTACK_CAP)
                                  if adv > 0 else Fraction(0))
    dadv = def_eff - attack
    factors = [min(DEFENSE_FACTOR * dadv, DEFENSE_CAP) if dadv > 0 else Fraction(0)]
    if not shooting and shooter and not no_melee_penalty:
        factors.append(Fraction(1, 2))
    defense_total = Fraction(1)
    for f in factors:
        defense_total *= Fraction(1) - min(Fraction(1), f)
    return attack_total, defense_total


def exact_compute_damage(attacker, defender, shooting: bool = False) -> int:
    """MODEL.md section 4 formula, exact rationals, exact floor, clamp at 1."""
    a, d = attacker.ctype, defender.ctype
    base = attacker.count() * a.damage
    def_eff = d.defense + (M.defend_bonus(d.defense) if defender.defending else 0)
    attack_total, defense_total = exact_factors(
        a.attack, def_eff, shooting, a.shooter, a.no_melee_penalty)
    return max(1, math.floor(base * attack_total * defense_total))


@dataclass
class DualTrace:
    calls: int = 0
    fractional: int = 0        # a factor other than 1 was in play
    boundary: int = 0          # the exact product is an integer (where floats bite)
    disagreements: list = field(default_factory=list)

    def summary(self) -> str:
        return (f"{self.calls} damage calls, {self.fractional} with a fractional "
                f"factor, {self.boundary} at an integer boundary, "
                f"{len(self.disagreements)} float/exact disagreements")


def probe_call(compute_damage) -> int:
    """Feed the base-90 / attack 0 / defence 10 / DEFEND cell (float 62,
    exact 63) through `compute_damage` -- the positive control for the dual
    instrumentation and for the battery's drill."""
    att = M.CreatureType("probe-att", attack=0, defense=0, dmg_min=1, dmg_max=1,
                         hp=1, speed=1)
    deff = M.CreatureType("probe-def", attack=0, defense=10, dmg_min=1, dmg_max=1,
                          hp=1000, speed=1)
    a = M.Stack(att, 90, 0, 0, 0)
    d = M.Stack(deff, 1, 1, 0, 1)
    d.defending = True
    return compute_damage(a, d)


def install_dual(trace: DualTrace, *modules, raise_on_disagreement: bool = False):
    """Patch `compute_damage` in homm3_model and in `modules`; return the undo."""
    original = M.compute_damage

    def dual(attacker, defender, shooting: bool = False) -> int:
        got = original(attacker, defender, shooting)
        want = exact_compute_damage(attacker, defender, shooting)
        a, d = attacker.ctype, defender.ctype
        def_eff = d.defense + (M.defend_bonus(d.defense) if defender.defending else 0)
        at, dt = exact_factors(a.attack, def_eff, shooting, a.shooter,
                               a.no_melee_penalty)
        trace.calls += 1
        if at != 1 or dt != 1:
            trace.fractional += 1
            if (attacker.count() * a.damage * at * dt).denominator == 1:
                trace.boundary += 1
        if got != want:
            rec = (attacker.count() * a.damage, a.attack, d.defense,
                   defender.defending, got, want)
            trace.disagreements.append(rec)
            if raise_on_disagreement:
                raise AssertionError(f"float/exact disagreement: {rec}")
        return got

    saved = [(M, original)]
    M.compute_damage = dual
    for mod in modules:
        if hasattr(mod, "compute_damage"):
            saved.append((mod, mod.compute_damage))
            mod.compute_damage = dual

    def undo() -> None:
        for mod, fn in saved:
            mod.compute_damage = fn

    return undo
