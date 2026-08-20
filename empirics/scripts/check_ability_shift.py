#!/usr/bin/env python3
"""Round 11 (PANEL-10 §5 item 8, promised in round 10 and pinned here):
the ability projection changes OPTIMA, not just flavour — demonstrate it
on the paper's own example and keep the demonstration pinned.

`naturalS-k6-02` fields 4 Efreet Sultans against, among others, 5 Genies.
The projection drops every shipped ability, including the Efreet's
`hateGenies`/`hateMasterGenies` (VCMI config/creatures/inferno.json:296-307,
`HATE`, val 50) — an extra +0.5 in attackFactorTotal against genies
(lib/battle/DamageCalculator.cpp:288-293). This script certifies the
recorded optimum under the projection, then restores that single ability
and re-certifies: the optimum moves 1136 -> 2020, i.e. the certified
optimum is 56% of the optimum of the instance the creature names
describe. Section 5.1 states this in one sentence; test_regressions.py
pins this script's output line.

Stdlib only, no VCMI checkout needed: the HATE fact above is transcribed
with its source, like every rule in MODEL.md.
"""

import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "scripts"))

import homm3_model  # noqa: E402
import solve  # noqa: E402

INSTANCE = "naturalS-k6-02"
HATER, HATED = "Efreet Sultan", "Genie"
PROJECTED, RESTORED = 1136, 2020

_orig_compute_damage = homm3_model.compute_damage


def hate_aware_damage(attacker, defender, shooting=False):
    """compute_damage with exactly one dropped ability restored: HATE adds
    its val/100 to attackFactorTotal (DamageCalculator.cpp:154-166 sums the
    attack factors; :288-293 yields 0.5 for hateGenies)."""
    dmg = _orig_compute_damage(attacker, defender, shooting)
    if attacker.ctype.name == HATER and defender.ctype.name == HATED:
        a, d = attacker.ctype, defender.ctype
        base = attacker.count() * a.damage
        def_eff = d.defense + (homm3_model.defend_bonus(d.defense)
                               if defender.defending else 0)
        attack_total = 1.0 + homm3_model.attack_skill_factor(
            a.attack, def_eff) + 0.5
        defense_total = 1.0 - min(
            1.0, homm3_model.defense_skill_factor(a.attack, def_eff))
        return max(1, math.floor(base * attack_total * defense_total))
    return dmg


def certified_optimum(inst: dict) -> int:
    res = solve.exact_optimum(inst)
    if not res["certified"]:
        raise SystemExit(f"{INSTANCE}: optimum no longer certified "
                         f"(bound {res['relaxation_bound']}, simulated "
                         f"{res['simulated_value']})")
    return res["optimum"]


def main() -> int:
    inst = json.loads(
        (ROOT / "empirics" / "instances" / f"{INSTANCE}.json").read_text())
    recorded = json.loads(
        (ROOT / "empirics" / "instances" / "optima.json").read_text())
    want = recorded[INSTANCE]["optimum"]

    base = certified_optimum(inst)
    if base != want or base != PROJECTED:
        raise SystemExit(f"projected optimum {base} != recorded {want} / "
                         f"pinned {PROJECTED}")

    solve.compute_damage = hate_aware_damage
    homm3_model.compute_damage = hate_aware_damage
    try:
        shifted = certified_optimum(inst)
    finally:
        solve.compute_damage = _orig_compute_damage
        homm3_model.compute_damage = _orig_compute_damage
    if shifted != RESTORED:
        raise SystemExit(f"restored-ability optimum {shifted} != pinned "
                         f"{RESTORED}")

    control = certified_optimum(inst)
    if control != base:
        raise SystemExit(f"negative control failed: optimum {control} after "
                         f"unpatching, expected {base}")

    pct = round(100 * base / shifted)
    print(f"OK: ability shift on {INSTANCE}: certified optimum {base} under "
          f"the projection, {shifted} with hateGenies restored — the "
          f"projected optimum is {pct}% of the ability-aware one")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
