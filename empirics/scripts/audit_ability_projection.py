#!/usr/bin/env python3
"""Generates the §5.1 ability-projection disclosure numbers (round 9, F6;
widened in round 10, M2).

The natural empirical instances carry shipped creature NUMBERS but none of
the shipped combat abilities (extract_creatures.py filters only on shooter
and doubleWide). This script counts, against VCMI's config/creatures/*.json,
how many natural instances name a creature whose ability the projection
drops — in THREE scopes, so the disclosure cannot understate the projection
by picking a flattering subset (the round-10 finding):

  melee     the five abilities that would change the modelled melee
            arithmetic itself;
  extended  five more combat-adjacent abilities the projection also drops
            (casts, regeneration, resistance, drains);
  any       every shipped ability whatsoever (FLYING, HATE, undead flags…).

Requires a local VCMI checkout (path below), which is why it is NOT part of
test_regressions.py — the battery instead pins the paper's quoted numbers to
the committed results/ability_projection.json; run this by hand when the
instance corpus or the disclosure sentence changes.
"""

import json
import os
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
VCMI = Path(os.environ.get(
    "VCMI_CHECKOUT",
    "/Users/ivanparfenchuk/Projects/AI/vcmi-upstream")) / "config" / "creatures"
ABIL_MELEE = {"BLOCKS_RETALIATION", "ATTACKS_ALL_ADJACENT",
              "RETURN_AFTER_STRIKE", "FIRE_SHIELD", "ADDITIONAL_ATTACK"}
ABIL_EXTENDED = {"SPELL_AFTER_ATTACK", "HP_REGENERATION", "MAGIC_RESISTANCE",
                 "MANA_DRAIN", "LIFE_DRAIN"}

import re


def json5ish(text: str):
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    out_lines = []
    for line in text.splitlines():
        # strip // comments outside of strings (no URLs in these configs'
        # structural positions; a conservative check: cut at // only if the
        # prefix has an even number of unescaped quotes)
        idx = line.find("//")
        while idx != -1:
            if line[:idx].count('"') % 2 == 0:
                line = line[:idx]
                break
            idx = line.find("//", idx + 1)
        out_lines.append(line)
    text = "\n".join(out_lines)
    text = re.sub(r",(\s*[}\]])", r"\1", text)
    return json.loads(text)


abil_by_ident = {}
for f in sorted(VCMI.glob("*.json")):
    try:
        data = json5ish(f.read_text())
    except Exception as e:
        print("skip", f.name, e)
        continue
    for ident, spec in data.items():
        if not isinstance(spec, dict):
            continue
        kinds = set()
        for a in (spec.get("abilities") or {}).values():
            if isinstance(a, dict) and "type" in a:
                kinds.add(a["type"])
        abil_by_ident[ident] = kinds

cr = json.loads((ROOT / "empirics" / "data" / "creatures_h3.json").read_text())
ident_by_name = {c["singular"]: c["identifier"] for c in cr["creatures"]}

nat_files = sorted((ROOT / "empirics" / "instances").glob("natural*.json"))
affected = Counter()          # scope -> instances with ≥1 dropped ability
player_hits = enemy_hits = 0  # melee scope only, as before
tally_melee = Counter()
tally_extended = Counter()
tally_any = Counter()
missing = set()
per_instance = {}
per_instance_ext = {}
for f in nat_files:
    inst = json.loads(f.read_text())
    types = list(inst.get("types", {}).keys())
    ptypes = set(inst.get("provenance", {}).get("player_types", []))
    dropped_here = {}
    dropped_ext_here = {}
    hit_any = False
    for name in types:
        ident = ident_by_name.get(name)
        if ident is None or ident not in abil_by_ident:
            missing.add(name)
            continue
        kinds = abil_by_ident[ident]
        for d in kinds:
            tally_any[d] += 1
        if kinds:
            hit_any = True
        dropped = kinds & ABIL_MELEE
        if dropped:
            dropped_here[name] = sorted(dropped)
            for d in dropped:
                tally_melee[d] += 1
            if name in ptypes:
                player_hits += 1
            else:
                enemy_hits += 1
        dropped_ext = kinds & ABIL_EXTENDED
        if dropped_ext:
            dropped_ext_here[name] = sorted(dropped_ext)
            for d in dropped_ext:
                tally_extended[d] += 1
    if dropped_here:
        affected["melee"] += 1
        per_instance[f.stem] = dropped_here
    if dropped_here or dropped_ext_here:
        affected["melee_or_extended"] += 1
    if dropped_ext_here:
        per_instance_ext[f.stem] = dropped_ext_here
    if hit_any:
        affected["any"] += 1

# Per-instance record of which shipped combat abilities the projection drops.
# Written to results/ rather than into the instance files themselves: the
# instances are generated (gen_instances.py) and a hand-added provenance field
# would silently vanish on the next regeneration.
out = ROOT / "empirics" / "results" / "ability_projection.json"
out.write_text(json.dumps({
    "comment": "shipped abilities carried by each natural instance's "
               "creatures and dropped by the H3-det-melee projection "
               "(see paper §5.1); three scopes so the disclosure cannot "
               "understate the projection; generated by "
               "audit_ability_projection.py against a local VCMI checkout",
    "abilities_audited_melee": sorted(ABIL_MELEE),
    "abilities_audited_extended": sorted(ABIL_EXTENDED),
    "natural_instances": len(nat_files),
    "affected_instances_melee": affected["melee"],
    "affected_instances_melee_or_extended": affected["melee_or_extended"],
    "affected_instances_any_ability": affected["any"],
    "tally_melee": dict(tally_melee.most_common()),
    "tally_extended": dict(tally_extended.most_common()),
    "tally_any_ability": dict(tally_any.most_common()),
    "dropped_by_instance": per_instance,
    "dropped_by_instance_extended": per_instance_ext,
}, indent=2, ensure_ascii=False) + "\n")

print(f"natural instances: {len(nat_files)}; affected: "
      f"melee {affected['melee']}, "
      f"melee|extended {affected['melee_or_extended']}, "
      f"any ability {affected['any']}")
print(f"type-slots (melee): player {player_hits}, enemy {enemy_hits}")
print("tally melee:", dict(tally_melee.most_common()))
print("tally extended:", dict(tally_extended.most_common()))
print("tally any (top 8):", dict(tally_any.most_common(8)))
print(f"wrote {out.relative_to(ROOT)}")
if missing:
    print("UNRESOLVED NAMES:", sorted(missing))
