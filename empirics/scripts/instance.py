#!/usr/bin/env python3
"""Instance schema for the ARMY-ALLOCATION empirics, and the glue to the model.

An instance is a self-contained JSON description of one optimisation problem:

    given a stock of creatures and k deployment slots, choose what goes in each
    slot so as to maximise the value of enemy creatures destroyed in R rounds
    against a scripted defence.

This is the optimisation version of ARMY-ALLOCATION (MODEL.md sec. 9); the
decision version asks whether the optimum reaches a target W.

Schema
------
{
  "id":            unique string
  "family":        corridor-partition | flower-3partition | natural-single | natural-multi
  "size":          k, the number of slots
  "seed":          the RNG seed the generator used
  "field":         {"width": int, "height": int, "obstacles": [int]}
  "rounds":        R
  "enemy_policy":  "hold"
  "types":         {name: {attack, defense, dmg_min, dmg_max, hp, speed, value, shooter}}
  "army":          [{"type": name, "stock": int}]          player's stock
  "slots":         [hex, ...]                              length k, deployment hexes
  "enemies":       [{"type": name, "count": int, "hex": int}]
  "provenance":    free-form dict (source problem, ground truth, layout name, ...)
}

An *allocation* is a list of length k. Element j is either `null` (slot j empty)
or a pair `[type_name, count]`. For single-type instances a bare integer is also
accepted and means "that many creatures of the one available type".
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "scripts"))

from homm3_model import (  # noqa: E402
    Battle,
    Battlefield,
    CreatureType,
    Stack,
    destroyed_value,
)

# ---------------------------------------------------------------------------


class IllegalAllocation(ValueError):
    """Raised when an allocation violates the instance's own constraints."""


def load(path: str | Path) -> dict:
    with open(path) as fh:
        return json.load(fh)


CACHE_KEY = "_derived"


def _cached(inst: dict, key: str, make):
    """Memoise derived objects on the instance itself.

    Keeping the cache in the dict (rather than in a table keyed by id()) means
    it cannot outlive the instance or be handed to a different dict that happens
    to land on the same address. `dump` strips it before serialising.
    """
    slot = inst.setdefault(CACHE_KEY, {})
    if key not in slot:
        slot[key] = make()
    return slot[key]


def invalidate(inst: dict) -> None:
    """Drop derived objects after the instance has been edited in place."""
    inst.pop(CACHE_KEY, None)


def dumps(inst: dict, **kw) -> str:
    """Serialise an instance without the derived-object cache."""
    return json.dumps({k: v for k, v in inst.items() if k != CACHE_KEY}, **kw)


def creature_types(inst: dict) -> dict[str, CreatureType]:
    return _cached(inst, "types", lambda: _make_types(inst))


def _make_types(inst: dict) -> dict[str, CreatureType]:
    out = {}
    for name, t in inst["types"].items():
        out[name] = CreatureType(
            name=name,
            attack=t["attack"],
            defense=t["defense"],
            dmg_min=t["dmg_min"],
            dmg_max=t["dmg_max"],
            hp=t["hp"],
            speed=t["speed"],
            value=t.get("value", 0),
            shooter=t.get("shooter", False),
            no_melee_penalty=t.get("no_melee_penalty", False),
            no_retaliation=t.get("no_retaliation", False),
            blocks_retaliation=t.get("blocks_retaliation", False),
        )
    return out


def battlefield(inst: dict) -> Battlefield:
    def make():
        f = inst["field"]
        return Battlefield(width=f["width"], height=f.get("height", 1),
                           obstacles=frozenset(f.get("obstacles", [])))
    return _cached(inst, "field", make)


def single_type(inst: dict) -> str | None:
    """The one player type, if the instance has exactly one; else None."""
    if len(inst["army"]) == 1:
        return inst["army"][0]["type"]
    return None


# --- allocations -----------------------------------------------------------


def normalise_allocation(inst: dict, alloc) -> list[tuple[str, int] | None]:
    """Coerce a raw allocation into [(type, count) | None] * k, or raise.

    Accepts, per slot: null / [] / 0 for "empty"; an int (single-type instances
    only); [type, count]; {"type": t, "count": c}. Anything else is illegal.
    Deliberately permissive about *shape* and strict about *semantics* — a model
    that says `[3, 0, 5]` on a single-type instance is answering the question,
    while a model that overspends its stock is not.
    """
    k = inst["size"]
    only = single_type(inst)
    known = set(inst["types"])

    if not isinstance(alloc, list):
        raise IllegalAllocation(f"allocation must be a list, got {type(alloc).__name__}")
    if len(alloc) != k:
        raise IllegalAllocation(f"allocation must have {k} entries, got {len(alloc)}")

    out: list[tuple[str, int] | None] = []
    for j, entry in enumerate(alloc):
        if entry is None or entry == [] or entry == {}:
            out.append(None)
            continue
        if isinstance(entry, bool):
            raise IllegalAllocation(f"slot {j}: booleans are not counts")
        if isinstance(entry, int):
            if only is None:
                raise IllegalAllocation(
                    f"slot {j}: bare integer is only allowed when the army has "
                    f"one creature type")
            out.append(None if entry == 0 else (only, entry))
            continue
        if isinstance(entry, dict):
            if "type" not in entry or "count" not in entry:
                raise IllegalAllocation(f"slot {j}: object needs 'type' and 'count'")
            entry = [entry["type"], entry["count"]]
        if isinstance(entry, list) and len(entry) == 2:
            t, c = entry
            if not isinstance(t, str) or isinstance(c, bool) or not isinstance(c, int):
                raise IllegalAllocation(f"slot {j}: expected [type: string, count: integer]")
            if t not in known:
                raise IllegalAllocation(f"slot {j}: unknown creature type {t!r}")
            out.append(None if c == 0 else (t, c))
            continue
        raise IllegalAllocation(f"slot {j}: cannot read entry {entry!r}")
    return out


def check_feasible(inst: dict, alloc: list[tuple[str, int] | None]) -> None:
    """Raise IllegalAllocation unless the allocation respects the stock."""
    stock = {a["type"]: a["stock"] for a in inst["army"]}
    used: dict[str, int] = {}
    for j, entry in enumerate(alloc):
        if entry is None:
            continue
        t, c = entry
        if c < 0:
            raise IllegalAllocation(f"slot {j}: negative count {c}")
        if t not in stock:
            raise IllegalAllocation(f"slot {j}: type {t!r} is not in the army")
        used[t] = used.get(t, 0) + c
    for t, u in used.items():
        if u > stock[t]:
            raise IllegalAllocation(
                f"type {t!r}: allocated {u} but only {stock[t]} available")


def build_battle(inst: dict, alloc: list[tuple[str, int] | None]) -> tuple[Battle, dict]:
    """Assemble the Battle for a (already normalised, already checked) allocation."""
    types = creature_types(inst)
    field = battlefield(inst)
    stacks: list[Stack] = []
    for j, entry in enumerate(alloc):
        if entry is None:
            continue
        t, c = entry
        if c > 0:
            stacks.append(Stack(types[t], c, side=0, slot=j, hex_=inst["slots"][j]))
    for g, e in enumerate(inst["enemies"]):
        stacks.append(Stack(types[e["type"]], e["count"], side=1, slot=g, hex_=e["hex"]))
    battle = Battle(field, stacks)
    initial = {i: s.count() for i, s in enumerate(battle.stacks) if s.side == 1}
    return battle, initial


def max_enemy_value(inst: dict) -> int:
    """Value of the whole defence: the ceiling any allocation could reach."""
    types = inst["types"]
    return sum(e["count"] * types[e["type"]].get("value", 0) for e in inst["enemies"])


def evaluate(inst: dict, alloc_raw) -> dict:
    """Score a raw allocation. Never raises; reports the reason instead.

    Returns {"legal": bool, "value": int, "reason": str|None, "allocation": [...]}.
    An illegal allocation scores 0 (see REPORT-DESIGN.md sec. 5 for the rationale).
    """
    from solve import play_optimally  # local import: solve.py imports this module

    try:
        alloc = normalise_allocation(inst, alloc_raw)
        check_feasible(inst, alloc)
    except IllegalAllocation as exc:
        return {"legal": False, "value": 0, "reason": str(exc), "allocation": None}

    # The exhaustive search, not the fast approximation: `play_fast` misses
    # both directions of the movement interaction (an ally can block a path, and
    # a stack that has already moved frees the hex it left), so it is not a
    # bound in either direction and must not decide a reported number.
    value = play_optimally(inst, alloc)
    return {"legal": True, "value": value, "reason": None,
            "allocation": [list(a) if a else None for a in alloc]}


__all__ = [
    "IllegalAllocation", "load", "creature_types", "battlefield", "single_type",
    "normalise_allocation", "check_feasible", "build_battle", "max_enemy_value",
    "evaluate", "destroyed_value",
]
