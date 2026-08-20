#!/usr/bin/env python3
"""Extract the shipped HoMM3 creature roster from the original game data.

Why this script exists: VCMI's `config/creatures/*.json` carries only graphics,
sound and upgrade metadata (MODEL.md sec. 4 already flags this). The numeric
statistics live in `DATA/CRTRAITS.TXT` inside the original `H3bitmap.lod`
archive, which VCMI reads at runtime:

    lib/CCreatureHandler.cpp:497   CLegacyConfigParser(TextPath::builtin("DATA/CRTRAITS.TXT"))
    lib/CCreatureHandler.cpp:519-563  the column order reproduced below

LOD container format, transcribed from
    lib/filesystem/CArchiveLoader.cpp:56-101 (initLODArchive)
    header: uint32 totalFiles at offset 8; entry table starts at 0x5c;
    entry: char name[16], uint32 offset, uint32 fullSize, uint32 unused,
           uint32 compressedSize.  compressedSize != 0 => zlib deflate.

Output: ../data/creatures_h3.json — one record per creature with the fields the
H3-det model needs (attack, defense, dmg_min, dmg_max, hp, speed, aiValue,
shots) plus provenance.

The archive is read-only; nothing outside homm3/empirics/ is written.
"""

from __future__ import annotations

import json
import os
import re
import struct
import sys
import zlib
from pathlib import Path

LOD_PATH = Path(os.environ.get(
    "H3_LOD_PATH",
    "/Users/ivanparfenchuk/Library/Application Support/vcmi/Data/H3bitmap.lod"))
VCMI_CREATURE_CONFIG = Path(os.environ.get(
    "VCMI_CHECKOUT",
    "/Users/ivanparfenchuk/Projects/AI/vcmi-upstream")) / "config" / "creatures"
OUT_PATH = Path(__file__).resolve().parent.parent / "data" / "creatures_h3.json"

# lib/constants/GameConstants.h: RESOURCE_QUANTITY
RESOURCE_QUANTITY = 7


def read_lod_entry(path: Path, wanted: str) -> bytes:
    """Return the raw bytes of `wanted` from a .lod archive."""
    blob = path.read_bytes()
    (total,) = struct.unpack_from("<I", blob, 8)
    for i in range(total):
        base = 0x5C + 32 * i
        raw_name = blob[base : base + 16]
        name = raw_name.split(b"\0", 1)[0].decode("latin-1")
        offset, full_size, _unused, comp_size = struct.unpack_from("<IIII", blob, base + 16)
        if name.upper() != wanted.upper():
            continue
        if comp_size:
            return zlib.decompress(blob[offset : offset + comp_size])
        return blob[offset : offset + full_size]
    raise KeyError(f"{wanted} not found in {path} ({total} entries)")


def parse_crtraits(text: str) -> list[dict]:
    """Column order per lib/CCreatureHandler.cpp:519-563 (loadLegacyData)."""
    lines = text.replace("\r\n", "\n").split("\n")
    # line 0 is a section header, line 1 is the column header
    header = lines[1].split("\t")
    names_count = 3 if len(header) > 2 and header[2].strip() == "Plural2" else 2
    if header[0].strip() != "Singular" or header[1].strip() != "Plural":
        raise ValueError("Incorrect format of CrTraits.txt (header mismatch)")

    def num(s: str) -> int:
        s = s.strip()
        if not s:
            return 0
        return int(float(s))

    out = []
    for raw in lines[2:]:
        if not raw.strip():
            continue
        f = raw.split("\t")
        if len(f) < 20 or not f[0].strip():
            continue
        i = 0
        singular = f[i].strip(); i += 1
        if names_count == 3:
            i += 1
        plural = f[i].strip(); i += 1
        i += RESOURCE_QUANTITY                      # cost
        fight_value = num(f[i]); i += 1
        ai_value = num(f[i]); i += 1
        i += 2                                      # growth, horde
        hp = num(f[i]); i += 1
        speed = num(f[i]); i += 1
        attack = num(f[i]); i += 1
        defense = num(f[i]); i += 1
        dmg_min = num(f[i]); i += 1
        dmg_max = num(f[i]); i += 1
        shots = num(f[i]); i += 1
        out.append({
            "singular": singular,
            "plural": plural,
            "fightValue": fight_value,
            "aiValue": ai_value,
            "hp": hp,
            "speed": speed,
            "attack": attack,
            "defense": defense,
            "dmg_min": dmg_min,
            "dmg_max": dmg_max,
            "shots": shots,
        })
    return out


def load_vcmi_creature_flags() -> dict[int, dict]:
    """index -> {identifier, doubleWide} from VCMI's config/creatures/*.json.

    These files carry no statistics (see the module docstring) but they do carry
    `index` and `doubleWide`, which we need: MODEL.md sec. 7 leaves double-wide
    creatures out of the reference simulator, so instances must avoid them.
    VCMI's JSON dialect allows // comments and trailing commas, hence the
    pre-pass before json.loads.
    """
    out: dict[int, dict] = {}
    for path in sorted(VCMI_CREATURE_CONFIG.glob("*.json")):
        text = path.read_text(encoding="utf-8")
        text = re.sub(r"//[^\n]*", "", text)
        text = re.sub(r",(\s*[}\]])", r"\1", text)
        data = json.loads(text)
        for ident, node in data.items():
            if not isinstance(node, dict) or "index" not in node:
                continue
            out[int(node["index"])] = {
                "identifier": ident,
                "faction": path.stem,
                "doubleWide": bool(node.get("doubleWide", False)),
            }
    return out


def main() -> int:
    if not LOD_PATH.exists():
        print(f"missing archive: {LOD_PATH}", file=sys.stderr)
        return 1
    raw = read_lod_entry(LOD_PATH, "CRTRAITS.TXT")
    text = raw.decode("cp1252", errors="replace")
    creatures = parse_crtraits(text)

    # CRTRAITS rows are in creature-index order (CCreatureHandler.cpp:518-520
    # fills objects[i] from row i), so the row number is the creature index.
    flags = load_vcmi_creature_flags()
    for i, c in enumerate(creatures):
        c["index"] = i
        c["shooter"] = c["shots"] > 0
        meta = flags.get(i, {})
        c["identifier"] = meta.get("identifier")
        c["faction"] = meta.get("faction")
        c["doubleWide"] = meta.get("doubleWide", False)

    # Drop the placeholder rows the original file carries ("NOT USED", zero stats)
    # and creatures with no offensive statistics at all.
    clean = [
        c for c in creatures
        if c["hp"] > 0 and c["speed"] > 0 and c["dmg_max"] > 0
        and "NOT USED" not in c["singular"].upper()
    ]

    flat = [c for c in clean if c["dmg_min"] == c["dmg_max"]]
    usable = [c for c in flat if not c["shooter"] and not c["doubleWide"]]

    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps({
        "source": {
            "archive": str(LOD_PATH),
            "member": "DATA/CRTRAITS.TXT",
            "column_order": "lib/CCreatureHandler.cpp:519-563",
            "lod_format": "lib/filesystem/CArchiveLoader.cpp:56-101",
        },
        "counts": {
            "parsed": len(creatures),
            "with_stats": len(clean),
            "flat_damage": len(flat),
            "h3det_native": len(usable),
        },
        "h3det_native": [c["singular"] for c in usable],
        "creatures": clean,
    }, indent=1, ensure_ascii=False) + "\n")

    print(f"parsed {len(creatures)} rows, {len(clean)} with statistics, "
          f"{len(flat)} with dmg_min == dmg_max, "
          f"{len(usable)} of those melee and single-hex")
    print(f"-> {OUT_PATH}")
    for c in flat:
        mark = "  " if c in usable else "x "
        print(f" {mark}{c['singular']:<22} hp={c['hp']:<4} spd={c['speed']:<3} "
              f"att={c['attack']:<3} def={c['defense']:<3} "
              f"dmg={c['dmg_min']}-{c['dmg_max']} ai={c['aiValue']:<6} "
              f"shooter={c['shooter']} wide={c['doubleWide']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
