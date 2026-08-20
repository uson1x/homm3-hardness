#!/usr/bin/env python3
"""Build the self-contained prompts for the LLM run.

Each task is one instance, one prompt, no external references: the rules are
inlined (transcribed from MODEL.md, but with no mention of files, papers or
complexity theory), the instance is given in full, and the required answer is a
single strict JSON object.

Two variants per instance:

  assisted  the prompt states, for each slot, which enemy stacks that slot can
            strike. This is the headline condition. The claim under test is
            about the *allocation* decision, so we hand the model the geometry
            and let it spend everything on the choice we care about. If agents
            still fall short here, the gap cannot be blamed on hex arithmetic.

  raw       the prompt gives the coordinates and the distance rule and nothing
            else. Harder, and confounded with spatial reasoning; useful as a
            contrast, not as the headline.

Output: ../llm_tasks.jsonl, one JSON object per line:
    {"task_id", "instance_id", "family", "size", "variant", "prompt"}

Run:  python3 scripts/make_llm_tasks.py [--variants assisted,raw]
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import instance as inst_mod  # noqa: E402
import solve  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
INST_DIR = ROOT / "instances"
OUT = ROOT / "llm_tasks.jsonl"


RULES = """\
You are choosing how to deploy an army before a battle in a turn-based tactics
game. The rules below are complete: everything you need is stated here.

BATTLEFIELD
A hex grid with W columns and H rows. A hex is written (x, y) with 0 <= x < W
and 0 <= y < H. Each hex has up to six neighbours. Two of them are always
(x-1, y) and (x+1, y). The other four are the diagonals, and they shift by one
column depending on the parity of the row:
  row y even:  (x, y-1), (x+1, y-1), (x, y+1), (x+1, y+1)
  row y odd:   (x-1, y-1), (x, y-1), (x-1, y+1), (x, y+1)
Distance between hexes p and q: put a = x + floor(y / 2) for each hex, then let
dx = a_q - a_p and dy = y_q - y_p. The distance is max(|dx|, |dy|) if dx and dy
are both >= 0 or both < 0, and |dx| + |dy| otherwise.

YOUR ARMY AND THE SLOTS
You have k slots, each pinned to a fixed hex. Each slot holds creatures of a
single type. One type may be split across several slots. Across all slots you
may not place more creatures of a type than your stock of that type. Slots may
be left empty, and creatures you do not place are simply left behind.

STACKS AND HEALTH
A stack of c creatures of a type with hp hit points each has a health pool of
c * hp. Damage is subtracted from that pool. The number of creatures still
standing is ceil(remaining pool / hp). A creature dies only when accumulated
damage finishes it off, and a creature left with 1 hit point still fights at
full strength.

DAMAGE
A stack of c creatures whose type has per-creature damage d, attacking a target
whose type has defence def, deals
    max(1, floor(c * d * A * D))
where, with att the attacking type's attack:
    A = 1 + min(0.05 * (att - def), 4.0)   if att > def, otherwise A = 1
    D = 1 - min(0.025 * (def - att), 0.7)  if def > att, otherwise D = 1
Damage beyond the target's remaining pool is wasted.

MOVEMENT AND REACH
Stacks act in order of decreasing speed. On its turn a stack may move up to
`speed` hexes along free hexes and then attack an adjacent enemy, so it can
strike any enemy at distance at most speed + 1, provided a free path exists.
Hexes occupied by another stack cannot be entered or crossed.

RETALIATION
When a stack attacks and the target survives, the target strikes back, once per
round. A target killed outright does not retaliate. Retaliation damages your
stacks but has no effect on your score.

THE DEFENCE
The enemy holds position for the entire battle. It never moves and never
attacks.

OBJECTIVE
Maximise the total value of enemy CREATURES KILLED. Each enemy type carries a
value; killing n creatures of that type scores n * value. Damage that does not
finish a creature scores nothing at all. Wounding a stack you cannot kill is
worth zero.
"""


def fmt_xy(inst: dict, h: int) -> str:
    w = inst["field"]["width"]
    return f"({h % w}, {h // w})"


def describe_types(inst: dict, names: list[str]) -> list[str]:
    lines = []
    for name in names:
        t = inst["types"][name]
        lines.append(
            f"    {name}: attack {t['attack']}, defence {t['defense']}, "
            f"damage {t['dmg_min']} per creature, {t['hp']} hit points, "
            f"speed {t['speed']}")
    return lines


def build_prompt(inst: dict, variant: str) -> str:
    w, h = inst["field"]["width"], inst["field"]["height"]
    k = inst["size"]
    only = inst_mod.single_type(inst)

    out = [RULES, "", "=" * 70, "", "THIS BATTLE", ""]
    out.append(f"Battlefield: {w} columns x {h} rows.")
    obstacles = inst["field"].get("obstacles", [])
    out.append(f"Impassable hexes: {'none' if not obstacles else obstacles}.")
    out.append(f"Rounds: {inst['rounds']}.")
    out.append("")

    out.append(f"Your {k} slots, in order, are at these hexes:")
    for j, hx in enumerate(inst["slots"]):
        out.append(f"    slot {j}: hex {fmt_xy(inst, hx)}")
    out.append("")

    out.append("Your stock (these are the only creatures you have):")
    for a in inst["army"]:
        t = inst["types"][a["type"]]
        out.append(
            f"    {a['stock']} x {a['type']} — attack {t['attack']}, "
            f"defence {t['defense']}, damage {t['dmg_min']} per creature, "
            f"{t['hp']} hit points, speed {t['speed']}")
    out.append("")

    out.append("The defence (it holds position and never attacks):")
    for g, e in enumerate(inst["enemies"]):
        t = inst["types"][e["type"]]
        out.append(
            f"    enemy {g}: {e['count']} x {e['type']} at hex "
            f"{fmt_xy(inst, e['hex'])} — attack {t['attack']}, "
            f"defence {t['defense']}, damage {t['dmg_min']} per creature, "
            f"{t['hp']} hit points, speed {t['speed']}, "
            f"value {t['value']} per creature")
    out.append("")

    if variant == "assisted":
        reach = solve.reach_table(inst)
        out.append("Reach, worked out for you from the rules above — which enemy")
        out.append("stacks each slot can strike this battle:")
        for j in range(k):
            per_type = []
            for a in inst["army"]:
                rs = reach[(j, a["type"])]
                per_type.append(
                    f"{a['type']} -> " + ("none" if not rs else
                                          ", ".join(f"enemy {g}" for g in rs)))
            out.append(f"    slot {j}: " + "; ".join(per_type))
        if not solve.blocking_free(inst):
            out.append("")
            out.append("Note: each line assumes the other slots are empty. On this")
            out.append("battlefield a stack of your own can stand in the way, so")
            out.append("filling every slot may cost some of the reach listed above.")
        out.append("")

    out.append("YOUR ANSWER")
    out.append("")
    out.append(f"Reply with one JSON object and nothing else — no explanation, no")
    out.append("code fence, no extra keys:")
    out.append("")
    out.append('    {"allocation": [e_0, ..., e_%d]}' % (k - 1))
    out.append("")
    out.append(f"The list must have exactly {k} entries, one per slot, in slot order.")
    out.append("Each entry is either null, meaning the slot is left empty, or a")
    out.append('two-element list ["<creature type>", <count>] with a positive')
    out.append("integer count.")
    if only is not None:
        out.append(f"Because your army is a single type ({only}), you may also write")
        out.append("a plain integer instead of a pair: the number of creatures in")
        out.append("that slot, 0 meaning empty.")
    out.append("")
    out.append("An answer that places more creatures of a type than you have in")
    out.append("stock is invalid and scores zero.")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--variants", default="assisted,raw")
    ap.add_argument("--out", default=str(OUT))
    args = ap.parse_args()
    variants = [v.strip() for v in args.variants.split(",") if v.strip()]

    paths = sorted(p for p in INST_DIR.glob("*.json")
                   if p.name not in ("optima.json", "index.json"))
    rows = []
    for path in paths:
        inst = inst_mod.load(path)
        for variant in variants:
            rows.append({
                "task_id": f"{inst['id']}::{variant}",
                "instance_id": inst["id"],
                "family": inst["family"],
                "size": inst["size"],
                "variant": variant,
                # False on the few boards where filling every slot costs
                # someone reach; the scorer reports this subgroup separately so
                # the headline cannot rest on instances whose reach table is
                # optimistic
                "blocking_free": solve.blocking_free(inst),
                "prompt": build_prompt(inst, variant),
            })

    with open(args.out, "w") as fh:
        for r in rows:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")

    lens = [len(r["prompt"]) for r in rows]
    print(f"{len(rows)} tasks ({len(paths)} instances x {len(variants)} variants)")
    print(f"prompt length: min {min(lens)}, median "
          f"{sorted(lens)[len(lens) // 2]}, max {max(lens)} characters")
    print(f"-> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
