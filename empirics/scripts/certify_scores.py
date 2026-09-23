#!/usr/bin/env python3
"""Certify the 870 per-response scores for the FULL H3-det action model.

Why this exists (review round 4, finding 1). `verify_full_model_optima.py`
closes the same question for the 145 recorded *optima* -- the denominators of
every published ratio. It says nothing about the numerators: the value credited
to each model's own allocation. Those come from `instance.evaluate` ->
`solve.play_optimally`, whose search omits WAIT, MOVE-only and DEFEND, so on its
face each is the optimum of a reduced action model. The reviewer inferred that
the reported ratios may therefore be underestimates.

They are not, and this script is the evidence. It reuses the ghost-enemy
relaxation of `verify_full_model_optima.py`, applied with the allocation held
fixed instead of quantified over:

  lower bound   the recorded value is achieved by an explicit play in the
                reference simulator, and every action that play uses is legal in
                the full model.

  upper bound   with the allocation fixed, each occupied slot contributes at
                most one strike, at a target drawn from its GHOST reach (the
                target is strikeable on a board holding nothing but the probe
                and that target). Whatever a real play does -- allies vacating,
                WAITs reordering, enemies dying and opening hexes -- the
                blockers at strike time are a superset of {target}, and reach is
                anti-monotone in the blocked set, so ghost reach dominates.
                Damage is position-independent and at most nominal, accumulates
                order-independently in one pool with overkill discarded, and the
                defence never initiates. Hence this bound dominates every legal
                full-model play of that allocation.

POLICY (review rounds 5-6). The sandwich above is computed against the corpus's
scripted defence `hold`. The paper's policy (‡) is WAIT-then-DEFEND: every
enemy waits at its NORMAL-phase activation and defends at its postponed
WAIT-phase activation, so its DEFEND lands after every NORMAL-phase player
action regardless of relative speed. To certify the recorded values as
(‡)-numbers and not merely `hold`-numbers, this script ALSO replays every
response's allocation through the phase-aware attack-only search of
check_defend_policy.py, with the defence literally executing (‡), and requires
the replayed value to equal the recorded one exactly. (Under the pre-round-6
policy -- DEFEND at the enemy's own NORMAL turn -- this replay fails on the
natural instances with fast enemies; check_defend_policy.py --legacy-defend
keeps that negative control runnable.)

Where all three meet, the recorded value is exact for the full action model,
under `hold` and under (‡) alike.

COVERAGE (review round 14, gpt-6-astra pro F5). The old coverage check compared
the SET of (task_id, model) keys seen in responses_final.jsonl with the SET of
keys in results/llm.json -- and both sides were built through a dict / set, so
multiplicity was discarded: replacing one cell by a duplicate of another in
BOTH files kept 870 records, 869 keys on each side, equal sets, and printed
ALL PASS (reproduced on a shadow copy in round 14). `check_coverage` now runs
BEFORE any dict is built, on the raw key lists: every key unique on each side,
and both equal to the DECLARED design -- every task of llm_tasks.jsonl (145
instances x 2 variants) crossed with the three model tiers of the companion note --
not to whichever records happen to be present.

Run from homm3/empirics/:

    python3 scripts/certify_scores.py

Exit status is non-zero if any response fails to certify.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "scripts"))

import instance as inst_mod  # noqa: E402
import solve  # noqa: E402
from check_defend_policy import best_under_policy  # noqa: E402
from score_llm import extract_allocation, load_instances  # noqa: E402
from verify_full_model_optima import ghost_reach_table  # noqa: E402

ROOT = HERE.parent


def fixed_allocation_ghost_bound(inst: dict, alloc: list, ghost: dict) -> int:
    """Upper bound on every full-model play of `alloc`.

    Each occupied slot strikes at most one enemy, chosen from its ghost reach;
    damage accumulates per enemy pool with overkill discarded.
    """
    enemies = inst["enemies"]
    pools = tuple(e["count"] * inst["types"][e["type"]]["hp"] for e in enemies)

    states = {(0,) * len(enemies)}
    for j, slot in enumerate(alloc):
        if slot is None:
            continue
        name, count = slot
        nxt = set()
        for dmg in states:
            nxt.add(dmg)  # this stack does not strike
            for g in ghost[(j, name)]:
                acc = min(dmg[g] + solve.damage_of(inst, name, count, g), pools[g])
                nxt.add(dmg[:g] + (acc,) + dmg[g + 1:])
        states = nxt
    return max(solve.value_of_damage(inst, dmg) for dmg in states)


# The three tiers the companion note (paper/companion-empirics.md) reports; the matrix is
# every task (instance x prompt variant) crossed with these.
MODELS = ("claude-haiku-4-5", "claude-sonnet-5", "claude-opus-5")


def expected_keys(tasks_path: Path = ROOT / "llm_tasks.jsonl") -> set:
    tasks = [json.loads(l)["task_id"] for l in open(tasks_path) if l.strip()]
    if len(tasks) != len(set(tasks)):
        raise SystemExit("llm_tasks.jsonl carries a duplicate task_id")
    return {(t, m) for t in tasks for m in MODELS}


def check_coverage(raw_keys: list, scored_keys: list, expected: set) -> list[str]:
    """Uniqueness and completeness of the (task_id, model) matrix, on the raw
    LISTS -- before anything is converted to a set or a dict."""
    problems = []
    for label, keys in (("responses", raw_keys), ("scored rows", scored_keys)):
        if len(keys) != len(set(keys)):
            dup = sorted({k for k in keys if keys.count(k) > 1})[:5]
            problems.append(f"{label}: {len(keys) - len(set(keys))} duplicate "
                            f"key(s), e.g. {dup}")
    for label, keys in (("responses", raw_keys), ("scored rows", scored_keys)):
        got = set(keys)
        if got != expected:
            missing = sorted(expected - got)[:5]
            extra = sorted(got - expected)[:5]
            problems.append(f"{label}: {len(got)} keys vs {len(expected)} "
                            f"declared cells; missing e.g. {missing}; "
                            f"undeclared e.g. {extra}")
    return problems


def bind_row(row: dict, value: int, optimum: int) -> list[str]:
    """Round 13 (codex Check 16): the certification used to bind only the
    VALUE of a scored row; the row's `optimum`, `ratio` and task metadata
    were read by stats_recheck.py as written. A ratio edited from 1.0 to
    0.0 with the raw response and value untouched still certified 870/870.
    Every field the statistics consume is now derived from the certified
    pair (value, optimum) and compared -- the ratio to the float
    value/optimum the scorer itself computed, within 1e-12 relative."""
    problems = []
    if row["optimum"] != optimum:
        problems.append(f"row optimum {row['optimum']} != certified "
                        f"instance optimum {optimum}")
    if optimum <= 0:
        problems.append(f"certified optimum {optimum} is not positive")
    elif not math.isclose(row["ratio"], value / optimum, rel_tol=1e-12,
                          abs_tol=1e-12):
        problems.append(f"row ratio {row['ratio']} != value/optimum = "
                        f"{value}/{optimum}")
    iid, _, variant = row["task_id"].partition("::")
    if row["instance_id"] != iid or row["variant"] != variant:
        problems.append(f"row names instance {row['instance_id']!r} / "
                        f"variant {row['variant']!r}, task_id says "
                        f"{iid!r} / {variant!r}")
    if row["exact"] != (value == optimum):
        problems.append(f"row exact={row['exact']} but value {value} vs "
                        f"optimum {optimum}")
    return problems


def main() -> int:
    instances = load_instances()
    optima = json.load(open(ROOT / "instances" / "optima.json"))
    per_response = json.load(open(ROOT / "results" / "llm.json"))["per_response"]
    raw_records = [json.loads(l) for l in open(ROOT / "responses_final.jsonl")
                   if l.strip()]
    # Round 14 (F5): uniqueness and completeness of the experimental matrix,
    # checked on the raw lists before any dict/set can hide a duplicate.
    coverage = check_coverage(
        [(r["task_id"], r["model"]) for r in raw_records],
        [(r["task_id"], r["model"]) for r in per_response],
        expected_keys())
    if coverage:
        print("COVERAGE FAILED before certification:")
        for c in coverage:
            print(f"    {c}")
        print("\nFAILED")
        return 1
    # A task_id names an instance and a prompt variant, not a response: the same
    # task_id appears once per model. Key by both or the three tiers collapse.
    scored = {(r["task_id"], r["model"]): r for r in per_response}

    ghost_cache: dict[str, dict] = {}
    certified = 0
    failures: list[str] = []

    for line in open(ROOT / "responses_final.jsonl"):
        line = line.strip()
        if not line:
            continue
        record = json.loads(line)
        key = (record["task_id"], record["model"])
        if key not in scored:
            continue
        iid = record["task_id"].split("::")[0]
        inst = instances[iid]
        label = f"{record['task_id']} [{record['model']}]"

        raw, _reason = extract_allocation(record.get("response"))
        if raw is None:
            failures.append(f"{label}: allocation did not parse")
            continue
        try:
            alloc = inst_mod.normalise_allocation(inst, raw)
            inst_mod.check_feasible(inst, alloc)
        except Exception as exc:  # noqa: BLE001 - report, do not mask
            failures.append(f"{label}: infeasible allocation ({exc})")
            continue

        if iid not in ghost_cache:
            ghost_cache[iid] = ghost_reach_table(inst)

        value = solve.play_optimally(inst, alloc)
        if value != scored[key]["value"]:
            failures.append(
                f"{label}: recomputed {value} != recorded {scored[key]['value']}")
            continue
        bound = fixed_allocation_ghost_bound(inst, alloc, ghost_cache[iid])
        if value != bound:
            failures.append(f"{label}: value {value} < full-model bound {bound}")
            continue
        under_policy = best_under_policy(inst, alloc, legacy=False)
        if under_policy != value:
            failures.append(
                f"{label}: (‡) replay {under_policy} != recorded {value}")
            continue
        bound_row = bind_row(scored[key], value, optima[iid]["optimum"])
        if bound_row:
            failures.append(f"{label}: " + "; ".join(bound_row))
            continue
        certified += 1

    # Coverage is part of the claim: silently checking 869 rows and printing ALL PASS
    # would be exactly the kind of unguarded quantitative sentence this project keeps
    # getting caught by. The matrix check above is the guard; this set comparison
    # stays as the older, weaker line (it cannot see duplicates -- round 14, F5).
    seen = {(r["task_id"], r["model"]) for r in raw_records}
    if seen != set(scored):
        only_scored = sorted(set(scored) - seen)[:5]
        only_seen = sorted(seen - set(scored))[:5]
        failures.append(
            f"coverage mismatch: {len(scored)} scored vs {len(seen)} responses; "
            f"scored-only e.g. {only_scored}; response-only e.g. {only_seen}")

    print(f"responses checked   {certified + len(failures)}")
    print(f"  certified exact   {certified}")
    print(f"  not certified     {len(failures)}")
    for f in failures:
        print(f"    {f}")
    if failures:
        print("\nFAILED")
        return 1
    print("\nALL PASS: every scored response is an exact optimum for its own "
          "allocation over the full action model, under the corpus defence `hold`\n"
          "AND under the paper's policy (‡) = WAIT-then-DEFEND (phase-aware replay,\n"
          "exact equality on every response); every row's optimum, ratio, exact\n"
          "flag and task metadata are bound to the certified (value, optimum) pair.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
