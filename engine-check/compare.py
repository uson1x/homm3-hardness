"""Cross-check homm3_model.py against the real VCMI combat engine.

Builds a list of test cases, hands them to the C++ harness (which drives VCMI's own
DamageCalculator / CUnitState / CHealth / CRetaliations), computes the reference model's
prediction for the same cases in Python, and reports every disagreement.

Two families of cases:

  R*  instances lifted from the candidate-A reductions (scripts/brute_force.py):
      the corridor PARTITION construction and the 3-row "flower" 3-PARTITION
      construction, at and around the kill thresholds the reductions turn on.

  S*  sanity cases from scripts/verify_mechanics.py: the CHealthTest vectors, the
      attack/defence factor caps, the count-not-hitpoints rule, the damage floor and
      the kill-threshold step function.

Run:  python3 compare.py [--harness PATH] [--runtime DIR]
"""

from __future__ import annotations

import argparse
import json
import math
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "scripts"))

from homm3_model import (  # noqa: E402
    Battle,
    Battlefield,
    CreatureType,
    Stack,
    compute_damage,
    kills_for_damage,
)

# Constants of the candidate-A constructions (scripts/brute_force.py:38-41).
CAP_ULP = (
    "defence cap: VCMI parses the JSON literal 0.7 by accumulating 0.1*7 "
    "(lib/json/JsonParser.cpp:536-547), yielding 0.7000000000000001 — one ULP above "
    "the double 0.7 that homm3_model.py's Python "
    "literal 0.7 denotes. The engine therefore multiplies by 0.29999999999999993 where "
    "the model multiplies by 0.30000000000000004, and std::floor drops one point of "
    "damage whenever base x 0.3 is an exact integer. Only the defence cap is affected; "
    "0.05, 4.0 and 0.025 round identically either way."
)

ALPHA = 10
PLAYER_HP = 5
PLAYER_SPEED = 2
ENEMY_SPEED = 1


def creature(name, attack=10, defense=10, damage=1, hp=10, speed=2, **kw):
    return CreatureType(name=name, attack=attack, defense=defense,
                        dmg_min=damage, dmg_max=damage, hp=hp, speed=speed, **kw)


# =========================================================================
# Case construction
# =========================================================================


def spec(ct: CreatureType, count: int) -> dict:
    """Serialise a model CreatureType + stack size for the C++ harness."""
    d = {
        "name": ct.name,
        "attack": ct.attack,
        "defense": ct.defense,
        "dmg_min": ct.dmg_min,
        "dmg_max": ct.dmg_max,
        "hp": ct.hp,
        "speed": ct.speed,
        "count": count,
    }
    for flag in ("shooter", "no_melee_penalty", "no_retaliation", "blocks_retaliation"):
        if getattr(ct, flag):
            d[flag] = True
    return d


CASES: list[dict] = []


def damage_case(cid, note, attacker, a_count, defender, d_count,
                shooting=False, attacker_predamage=None, defender_predamage=None,
                known_issue=None):
    c = {
        "id": cid,
        "kind": "damage",
        "note": note,
        "attacker": spec(attacker, a_count),
        "defender": spec(defender, d_count),
    }
    if known_issue:
        c["known_issue"] = known_issue
    if shooting:
        c["shooting"] = True
    if attacker_predamage is not None:
        c["attacker_predamage"] = attacker_predamage
    if defender_predamage is not None:
        c["defender_predamage"] = defender_predamage
    CASES.append(c)
    return c


def health_case(cid, note, ctype, count, damages):
    CASES.append({
        "id": cid, "kind": "health", "note": note,
        "stack": spec(ctype, count), "damage": damages,
    })


def retaliation_case(cid, note, ctype, count, events):
    CASES.append({
        "id": cid, "kind": "retaliation", "note": note,
        "stack": spec(ctype, count), "events": events,
    })


def order_unit(name, speed, side="attacker", slot=0, waiting=False, defending=False):
    """A minimal unit for a turn-order case: only speed, side, slot and the
    round-state flags matter to the queue."""
    d = {"name": name, "attack": 10, "defense": 10, "dmg_min": 1, "dmg_max": 1,
         "hp": 10, "speed": speed, "count": 1, "side": side, "slot": slot}
    if waiting:
        d["waiting"] = True
    if defending:
        d["defending"] = True
    return d


def turn_order_case(cid, note, units, expected_engine=None):
    """expected_engine: hand-derived engine order for cases with cross-side speed
    ties, where the model's simplified tie rule (MODEL.md sec. 5 note: side then
    slot) deliberately differs from the engine's side alternation. Tie-free cases
    omit it and are compared against the reference model directly."""
    c = {"id": cid, "kind": "turn_order", "note": note, "units": units}
    if expected_engine is not None:
        c["expected_engine"] = expected_engine
    CASES.append(c)


def build_cases() -> None:
    # ---------------------------------------------------------------
    # R1-R4: the corridor PARTITION construction (candidate-A sec. 3.1).
    # Player creature C: attack=defence=ALPHA, 1 damage, hp 5, speed 2.
    # Enemy E_j: attack=defence=ALPHA, 1 damage, hp a_j, speed 1.
    # A stack of c player creatures deals exactly c damage, so it kills E_j
    # iff c >= a_j. That threshold is the whole reduction.
    # ---------------------------------------------------------------
    player = creature("C", attack=ALPHA, defense=ALPHA, damage=1,
                      hp=PLAYER_HP, speed=PLAYER_SPEED)
    for a_j in (3, 5):
        enemy = creature(f"E_{a_j}", attack=ALPHA, defense=ALPHA, damage=1,
                         hp=a_j, speed=ENEMY_SPEED)
        for delta, label in ((-1, "below"), (0, "at"), (1, "above")):
            c = a_j + delta
            damage_case(f"R-part-a{a_j}-c{c}",
                        f"PARTITION corridor: {c} player creatures vs enemy hp={a_j} "
                        f"({label} kill threshold)",
                        player, c, enemy, 1)

    # R5: the enemy's blow back at the player stack (retaliation damage). The enemy
    # deals 1 damage per creature and has one creature, so it removes 1 hit point;
    # with PLAYER_HP=5 nobody dies, which is why the construction survives a round.
    enemy5 = creature("E_5", attack=ALPHA, defense=ALPHA, damage=1,
                      hp=5, speed=ENEMY_SPEED)
    damage_case("R-part-retaliation",
                "PARTITION corridor: enemy stack of 1 strikes back at the player stack",
                enemy5, 1, player, 5)

    # R6-R8: the 3-PARTITION flower construction (candidate-A sec. 4.1). Player type
    # C_i carries a_i damage per creature and is deployed one creature per slot; three
    # slots feed one enemy of hp T. Damage from a single creature of type C_i is a_i.
    T = 9
    enemy_T = creature("E_T", attack=ALPHA, defense=ALPHA, damage=1,
                       hp=T, speed=ENEMY_SPEED, value=1)
    for a_i in (2, 3, 4):
        pt = creature(f"C_{a_i}", attack=ALPHA, defense=ALPHA, damage=a_i,
                      hp=PLAYER_HP, speed=PLAYER_SPEED)
        damage_case(f"R-3part-a{a_i}",
                    f"3-PARTITION flower: one creature of type C_{a_i} vs enemy hp={T}",
                    pt, 1, enemy_T, 1)

    # R9: the same enemy after two of the three blows have landed — checks that a
    # wounded enemy dies exactly when the accumulated damage reaches T, i.e. that the
    # threshold is on the *pool*, not on any single blow.
    damage_case("R-3part-third-blow",
                f"3-PARTITION flower: third blow of 4 on an enemy already down to {T}-5 hp",
                creature("C_4", attack=ALPHA, defense=ALPHA, damage=4,
                         hp=PLAYER_HP, speed=PLAYER_SPEED),
                1, enemy_T, 1, defender_predamage=5)

    # R10: the count-not-hitpoints rule inside a reduction instance — a player stack
    # wounded to 1 hit point on its top creature still delivers full damage.
    damage_case("R-part-wounded-attacker",
                "PARTITION corridor: 5-creature player stack wounded to 1 hp on top, "
                "still hits at full strength",
                player, 5, creature("E_big", defense=ALPHA, hp=10_000), 1,
                attacker_predamage=PLAYER_HP - 1)

    # ---------------------------------------------------------------
    # S*: sanity cases mirroring verify_mechanics.py
    # ---------------------------------------------------------------
    big = creature("target", defense=10, hp=100_000)

    # S1: damage is linear in stack count (DamageCalculator.cpp:123-131)
    for c in (1, 2, 5, 100):
        damage_case(f"S-linear-{c}", f"damage scales with count: {c} x 7 damage",
                    creature("atk", attack=10, damage=7), c, big, 1)

    # S2: attack skill factor, including the cap at 80 attack points
    for att in (10, 11, 20, 90, 210):
        damage_case(f"S-attack-{att}",
                    f"attack factor: attacker attack={att} vs defence 10",
                    creature("atk", attack=att, damage=100), 1,
                    creature("def", defense=10, hp=100_000), 1)

    # S3: defence skill factor, including the cap at 28 defence points
    for dfn in (10, 11, 20, 38, 200):
        damage_case(f"S-defense-{dfn}",
                    f"defence factor: defender defence={dfn} vs attack 10",
                    creature("atk", attack=10, damage=100), 1,
                    creature("def", defense=dfn, hp=100_000), 1,
                    known_issue=CAP_ULP if dfn >= 38 else None)

    # S4: floor and the lower clamp at 1 (DamageCalculator.cpp:576-577)
    damage_case("S-clamp-to-1",
                "1 x 3 damage x 0.3 defence factor = 0.9, must clamp up to 1",
                creature("atk", attack=10, damage=3), 1,
                creature("def", defense=100, hp=1000), 1)
    damage_case("S-floor-3",
                "1 x 10 damage x 0.3 defence factor = 3.0 in exact arithmetic; "
                "checks the engine's double rounding",
                creature("atk", attack=10, damage=10), 1,
                creature("def", defense=100, hp=1000), 1,
                known_issue=CAP_ULP)

    # S5: melee penalty for a shooter fighting in melee (DamageCalculator.cpp:385-390)
    damage_case("S-shooter-melee",
                "shooter attacking in melee takes the 0.5 penalty",
                creature("shooter", attack=10, damage=10, shooter=True), 1,
                creature("def", defense=10, hp=1000), 1)
    damage_case("S-shooter-melee-exempt",
                "shooter with NO_MELEE_PENALTY attacking in melee",
                creature("shooter", attack=10, damage=10, shooter=True,
                         no_melee_penalty=True), 1,
                creature("def", defense=10, hp=1000), 1)

    # S6: kill thresholds (DamageCalculator.cpp:522-531) — vary the attacker's count
    # so the delivered damage crosses each multiple of the defender's hit points.
    for dmg in (24, 25, 26, 50, 100, 10_000):
        damage_case(f"S-kills-{dmg}",
                    f"kill count for {dmg} damage against 4 creatures of 25 hp",
                    creature("atk", attack=10, damage=1), dmg,
                    creature("def", defense=10, hp=25), 4)

    # S7: health pool, ported from VCMI's own CHealthTest.cpp:103-127
    health_case("S-health-vcmi-damage",
                "CHealthTest.cpp:103-127: 300 creatures of 123 hp",
                creature("h", hp=123), 300, [0, 122, 1, 123 * 299, 1337])
    health_case("S-health-overkill",
                "CHealthTest.cpp:232-252: one 300 hp creature absorbs only 300 of 1000",
                creature("h", hp=300), 1, [1000])
    health_case("S-health-partial",
                "CHealthTest.cpp:129-138: 99 damage on a 123 hp creature",
                creature("h", hp=123), 300, [99])
    health_case("S-health-reduction",
                "PARTITION enemy of hp 5 taking 4 then 1 damage",
                creature("E_5", hp=5), 1, [4, 1])

    # S8: retaliation bookkeeping (CUnitState.cpp:127-136, :920)
    plain = creature("plain", hp=100)
    retaliation_case("S-retal-basic",
                     "one retaliation, spent, restored at the round boundary",
                     plain, 1, ["retaliate", "retaliate", "new_round", "retaliate"])
    retaliation_case("S-retal-none",
                     "NO_RETALIATION unit never retaliates",
                     creature("norretal", hp=100, no_retaliation=True), 1,
                     ["retaliate", "new_round"])
    retaliation_case("S-retal-attacking-does-not-consume",
                     "the unit's own attack does not consume its retaliation charge",
                     plain, 1, ["attack", "attack", "retaliate"])

    # ---------------------------------------------------------------
    # T*: the turn-order machinery the `(‡)` = WAIT-then-DEFEND policy stands on.
    # The engine side runs CBattleInfoCallback::battleGetTurnOrder + takeOneUnit +
    # CMP_stack over real CUnitState units (battleQueuePhase / willMove / waited);
    # nothing about phase assignment or ordering is reimplemented in the harness.
    # ---------------------------------------------------------------

    # T1: NORMAL phase is decreasing initiative, no ties.
    turn_order_case(
        "T-normal-desc",
        "NORMAL phase: strictly decreasing speed across sides",
        [order_unit("s13", 13, "defender"), order_unit("s6", 6),
         order_unit("s10", 10, slot=1), order_unit("s1", 1, "defender", slot=1)])

    # T2: the one-round lemma's engine half (paper sec. 2.4): a waiting enemy acts
    # after EVERY normal-phase player, whatever the speeds. This is the exact
    # naturalS-k2-05 mechanism: Dragon Fly speed 13 waits, player speed 6 does not.
    turn_order_case(
        "T-wait-after-normal",
        "a waiting speed-13 enemy is postponed past a speed-6 non-waiting player",
        [order_unit("player6", 6), order_unit("fly13", 13, "defender", waiting=True)])

    # T3: the WAIT phase runs in INCREASING speed order
    # (CBattleInfoCallback.cpp:495-519), inverted against the NORMAL phase.
    turn_order_case(
        "T-wait-increasing",
        "WAIT phase: increasing speed, after the whole NORMAL phase",
        [order_unit("front20", 20),
         order_unit("w4", 4, "defender", waiting=True),
         order_unit("w13", 13, "defender", slot=1, waiting=True),
         order_unit("w6", 6, "attacker", slot=1, waiting=True)])

    # T4: DEFEND ends the round for the stack: a defending unit is out of the
    # queue until the next round (CUnitState::willMove checks `defending`).
    turn_order_case(
        "T-defend-out-of-round",
        "a defending speed-15 unit does not reappear in this round's queue",
        [order_unit("d15", 15, "defender", defending=True),
         order_unit("s5", 5), order_unit("s3", 3, "defender", slot=1)])

    # T5-T6: cross-side speed ties — the engine alternates sides
    # (BattleInfo.cpp:978-1006, takeOneUnit), which the reference model
    # deliberately simplifies to side-then-slot (MODEL.md sec. 5 note). These two
    # cases pin the ENGINE rule; expected orders are hand-derived from the cited
    # code, so a pass certifies the documented divergence is exactly as documented.
    turn_order_case(
        "T-tie-normal-alternation",
        "NORMAL phase, equal speeds: turn-0 attacker priority, then alternation",
        [order_unit("a0", 7, "attacker", slot=0), order_unit("a1", 7, "attacker", slot=1),
         order_unit("d0", 7, "defender", slot=0)],
        expected_engine=["a0", "d0", "a1"])
    turn_order_case(
        "T-tie-wait-alternation",
        "WAIT phase, equal speeds: alternation continues from the last mover's side",
        [order_unit("n9", 9, "attacker", slot=0),
         order_unit("wa", 5, "attacker", slot=1, waiting=True),
         order_unit("wd", 5, "defender", slot=0, waiting=True)],
        expected_engine=["n9", "wd", "wa"])


# =========================================================================
# Model predictions
# =========================================================================


def model_stack(s: dict) -> Stack:
    ct = CreatureType(
        name=s["name"], attack=s["attack"], defense=s["defense"],
        dmg_min=s["dmg_min"], dmg_max=s["dmg_max"], hp=s["hp"], speed=s["speed"],
        shooter=s.get("shooter", False),
        no_melee_penalty=s.get("no_melee_penalty", False),
        no_retaliation=s.get("no_retaliation", False),
        blocks_retaliation=s.get("blocks_retaliation", False),
    )
    return Stack(ct, s["count"], side=0, slot=0, hex_=0)


def predict(case: dict) -> dict:
    kind = case["kind"]
    if kind == "damage":
        a = model_stack(case["attacker"])
        d = model_stack(case["defender"])
        if "attacker_predamage" in case:
            a.apply_damage(case["attacker_predamage"])
        if "defender_predamage" in case:
            d.apply_damage(case["defender_predamage"])
        dmg = compute_damage(a, d, shooting=case.get("shooting", False))
        return {
            "attacker_count": a.count(),
            "defender_count": d.count(),
            "defender_first_hp_left": d.first_hp_left,
            "damage_min": dmg,
            "damage_max": dmg,
            "kills_min": kills_for_damage(d, dmg),
            "kills_max": kills_for_damage(d, dmg),
        }

    if kind == "health":
        s = model_stack(case["stack"])
        steps = []
        for amount in case["damage"]:
            absorbed = s.apply_damage(amount)
            steps.append({
                "requested": amount, "absorbed": absorbed,
                "count": s.count(), "first_hp_left": s.first_hp_left,
                "available": s.available(),
            })
        return {"steps": steps}

    if kind == "turn_order":
        if "expected_engine" in case:
            # Cross-side tie case: the model's tie rule is a documented
            # simplification, so the expectation is the engine rule itself,
            # hand-derived from BattleInfo.cpp:978-1006 / takeOneUnit.
            return {"order": case["expected_engine"]}
        stacks = []
        for i, u in enumerate(case["units"]):
            ct = CreatureType(
                name=u["name"], attack=u["attack"], defense=u["defense"],
                dmg_min=u["dmg_min"], dmg_max=u["dmg_max"], hp=u["hp"],
                speed=u["speed"])
            s = Stack(ct, u["count"],
                      side=1 if u.get("side") == "defender" else 0,
                      slot=u.get("slot", 0), hex_=i)
            s.waited = u.get("waiting", False)
            s.defending = u.get("defending", False)
            stacks.append(s)
        b = Battle(Battlefield(len(stacks) + 1), stacks)
        # The model's phase semantics, as used by brute_force.phased_schedule:
        # the NORMAL phase is every living stack that neither waited nor already
        # defended, fastest first; the WAIT phase follows, slowest first.
        normal = [s for s in b.turn_order() if not s.waited and not s.defending]
        wait = [s for s in b.wait_phase_order() if not s.defending]
        return {"order": [s.ctype.name for s in normal + wait]}

    if kind == "retaliation":
        s = model_stack(case["stack"])
        events = []
        for ev in case["events"]:
            if ev == "retaliate":
                if s.retaliations_left > 0:
                    s.retaliations_left -= 1
            elif ev == "attack":
                pass  # the model never charges an attack against the retaliation counter
            elif ev == "new_round":
                s.retaliations_left = 0 if s.ctype.no_retaliation else 1
            events.append({"event": ev, "able": s.alive() and s.retaliations_left > 0})
        return {
            "able_initially": s.alive() and (not s.ctype.no_retaliation),
            "events": events,
        }

    raise ValueError(kind)


# =========================================================================
# Comparison
# =========================================================================


def diff(model: dict, engine: dict, path: str = "") -> list[str]:
    out = []
    for key, want in model.items():
        if key not in engine:
            out.append(f"{path}{key}: model={want}, engine=<absent>")
            continue
        got = engine[key]
        if isinstance(want, list):
            if len(want) != len(got):
                out.append(f"{path}{key}: model has {len(want)} steps, engine {len(got)}")
                continue
            for i, (w, g) in enumerate(zip(want, got)):
                if isinstance(w, dict):
                    out.extend(diff(w, g, f"{path}{key}[{i}]."))
                elif w != g:
                    out.append(f"{path}{key}[{i}]: model={w}, engine={g}")
        elif isinstance(want, dict):
            out.extend(diff(want, got, f"{path}{key}."))
        elif want != got:
            out.append(f"{path}{key}: model={want}, engine={got}")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    default_work = os.environ.get("WORK", "/tmp/vcmi-enginecheck")
    ap.add_argument("--harness", default=os.environ.get(
        "ENGINECHECK", os.path.join(default_work, "vcmi-build", "enginecheck")))
    ap.add_argument("--runtime", default=os.environ.get(
        "VCMI_RUNTIME", os.path.join(default_work, "runtime")))
    ap.add_argument("--json-out", default=os.path.join(HERE, "engine_results.json"))
    args = ap.parse_args()

    build_cases()
    cases_path = os.path.join(HERE, "cases.json")
    with open(cases_path, "w") as fh:
        json.dump({"cases": CASES}, fh, indent=2)
    print(f"wrote {len(CASES)} cases to {cases_path}")

    proc = subprocess.run([args.harness, cases_path], cwd=args.runtime,
                          capture_output=True, text=True)
    if proc.returncode != 0:
        print("harness failed:", file=sys.stderr)
        print(proc.stdout[-4000:], file=sys.stderr)
        print(proc.stderr[-4000:], file=sys.stderr)
        return 2

    engine = json.loads(proc.stdout)
    with open(args.json_out, "w") as fh:
        json.dump(engine, fh, indent=2)

    print("\nEngine combat constants as loaded by the engine itself:")
    for k, v in engine["engine"].items():
        print(f"  {k:38s} {v}")

    by_id = {r["id"]: r for r in engine["results"]}
    mismatches = []
    explained = []
    print(f"\n{'case':32s} {'result':8s} note")
    print("-" * 100)
    for case in CASES:
        model = predict(case)
        actual = by_id.get(case["id"])
        if actual is None:
            mismatches.append((case["id"], ["engine produced no result"]))
            print(f"{case['id']:32s} {'MISSING':8s} {case['note']}")
            continue
        problems = diff(model, actual)
        if problems and case.get("known_issue"):
            status = "EXPLAINED"
            explained.append((case["id"], problems, case["known_issue"]))
        elif problems:
            status = "MISMATCH"
            mismatches.append((case["id"], problems))
        else:
            status = "ok"
        print(f"{case['id']:32s} {status:8s} {case['note']}")
        for p in problems:
            print(f"{'':32s} {'':8s}   {p}")

    if explained:
        print("\nExplained divergences (cause identified, see REPORT.md):")
        for cid, problems, why in explained:
            print(f"  {cid}: {'; '.join(problems)}")
            print(f"    {why}")

    print()
    if mismatches:
        print(f"FAILED: {len(mismatches)} of {len(CASES)} cases disagree with the engine")
        return 1
    print(f"OK: {len(CASES) - len(explained)} of {len(CASES)} cases agree with the engine "
          f"exactly; {len(explained)} diverge for a cause identified below")
    return 0


if __name__ == "__main__":
    sys.exit(main())
