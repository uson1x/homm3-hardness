#!/usr/bin/env python3
"""Score LLM answers against the certified optima.

Input: a JSONL file of responses, one object per line. Required fields:

    {"task_id": "...", "response": <string or object>}

`instance_id` and `variant` are read from `task_id` when absent (task ids are
"<instance_id>::<variant>"). Any other fields (model name, latency, token
counts) are carried through to the per-response record untouched. A `model`
field, if present, groups the aggregate; otherwise everything is one group.

`response` may be the raw text the model produced. The extractor is deliberately
forgiving about packaging and strict about content: it will dig a JSON object
out of prose, a code fence or a "here is my answer:" preamble, because the
failure we want to measure is bad allocation, not bad formatting. It will not
repair the allocation itself.

How invalid answers are handled
-------------------------------
The headline metric scores an invalid answer as 0 and flags it. The reasoning:
the stock constraint is not packaging, it is the problem. An allocation that
places creatures the player does not own is not a worse solution, it is not a
solution — and if overspending were merely clipped, a model could score by
ignoring the one constraint that makes the problem a knapsack. Dropping invalid
answers instead of zeroing them would be worse still: it would quietly reward a
model for failing to answer on exactly the instances it found hardest.

So that this choice cannot be doing the work, every run also reports:

    strict     invalid -> 0                     (headline)
    valid_only mean over parseable, legal answers only
    repaired   counts clipped to fit the stock, then scored

and the counts of each failure kind. If the three tell the same story, the
choice is immaterial and the report says so; if they diverge, that is a finding
and it must be reported, not hidden.

Run:  python3 scripts/score_llm.py responses.jsonl [-o results/llm.json]
"""

from __future__ import annotations

import argparse
import json
import re
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import instance as inst_mod  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
INST_DIR = ROOT / "instances"
RESULTS = ROOT / "results"


# --- getting JSON out of whatever the model said ---------------------------


def _candidate_objects(text: str):
    """Yield JSON-looking substrings, most promising first."""
    fenced = re.findall(r"```(?:json)?\s*(.*?)```", text, re.S | re.I)
    for block in fenced:
        yield block.strip()
    # balanced-brace scan, longest first, so nested objects are handled
    starts = [i for i, ch in enumerate(text) if ch == "{"]
    for start in starts:
        depth, in_str, esc = 0, False, False
        for i in range(start, len(text)):
            ch = text[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    yield text[start:i + 1]
                    break
    yield text.strip()


def extract_allocation(response):
    """Return (allocation, error). allocation is the raw value under key
    "allocation"; error is a string when nothing usable was found."""
    if response is None:
        return None, "empty response"
    if isinstance(response, dict):
        if "allocation" not in response:
            return None, "object has no 'allocation' key"
        return response["allocation"], None
    if isinstance(response, list):
        return response, None       # a bare list is accepted as the allocation
    if not isinstance(response, str):
        return None, f"unexpected response type {type(response).__name__}"

    for chunk in _candidate_objects(response):
        try:
            obj = json.loads(chunk)
        except (json.JSONDecodeError, ValueError):
            continue
        if isinstance(obj, dict) and "allocation" in obj:
            return obj["allocation"], None
        if isinstance(obj, list):
            return obj, None
    return None, "no JSON object with an 'allocation' key"


# --- repair (reported alongside, never as the headline) --------------------


def repair(inst: dict, raw) -> list | None:
    """Best-effort coercion into a legal allocation, for the robustness column.

    Fixes only mechanical problems: wrong length, negative counts, unknown
    types, and overspending (largest slots are trimmed first). Returns None when
    there is nothing to work with.
    """
    if not isinstance(raw, list):
        return None
    k = inst["size"]
    only = inst_mod.single_type(inst)
    known = set(inst["types"])
    stock = {a["type"]: a["stock"] for a in inst["army"]}

    fixed: list = []
    for entry in list(raw)[:k]:
        if isinstance(entry, bool) or entry in (None, [], {}, 0):
            fixed.append(None)
        elif isinstance(entry, int):
            fixed.append((only, max(0, entry)) if only else None)
        elif isinstance(entry, dict) and "type" in entry and "count" in entry:
            t, c = entry["type"], entry["count"]
            fixed.append((t, max(0, int(c))) if t in known and isinstance(c, int) else None)
        elif isinstance(entry, list) and len(entry) == 2 and entry[0] in known:
            c = entry[1]
            fixed.append((entry[0], max(0, int(c))) if isinstance(c, int) else None)
        else:
            fixed.append(None)
    fixed += [None] * (k - len(fixed))

    for t, cap in stock.items():
        idxs = [i for i, e in enumerate(fixed) if e and e[0] == t]
        total = sum(fixed[i][1] for i in idxs)
        while total > cap and idxs:
            i = max(idxs, key=lambda i: fixed[i][1])
            take = min(fixed[i][1], total - cap)
            fixed[i] = (t, fixed[i][1] - take)
            total -= take
            if fixed[i][1] == 0:
                fixed[i] = None
                idxs.remove(i)
    # drop types that are not in the army at all
    fixed = [e if (e is None or e[0] in stock) else None for e in fixed]
    return [None if e is None or e[1] == 0 else [e[0], e[1]] for e in fixed]


# --- scoring ---------------------------------------------------------------


def load_instances() -> dict[str, dict]:
    return {p.stem: inst_mod.load(p) for p in INST_DIR.glob("*.json")
            if p.name not in ("optima.json", "index.json")}


def classify(reason: str | None) -> str:
    if reason is None:
        return "ok"
    r = reason.lower()
    if "no json" in r or "empty response" in r or "no 'allocation'" in r:
        return "unparseable"
    if "only" in r and "available" in r:
        return "over_budget"
    if "entries" in r or "must be a list" in r:
        return "wrong_shape"
    if "unknown creature type" in r:
        return "unknown_type"
    if "negative" in r:
        return "negative_count"
    return "other_invalid"


def score_file(path: Path) -> dict:
    instances = load_instances()
    optima = json.loads((INST_DIR / "optima.json").read_text())

    records = []
    with open(path) as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                records.append({"line": lineno, "error": f"bad JSONL: {exc}"})
                continue

            task_id = row.get("task_id") or ""
            iid = row.get("instance_id") or task_id.split("::")[0]
            variant = row.get("variant") or (
                task_id.split("::")[1] if "::" in task_id else "unknown")
            inst = instances.get(iid)
            if inst is None:
                records.append({"line": lineno, "task_id": task_id,
                                "instance_id": iid, "variant": variant,
                                "model": row.get("model", "unspecified"),
                                "error": f"unknown instance {iid!r}"})
                continue

            opt = optima[iid]["optimum"]
            raw, err = extract_allocation(row.get("response"))
            if err is not None:
                res = {"legal": False, "value": 0, "reason": err, "allocation": None}
            else:
                res = inst_mod.evaluate(inst, raw)

            rep_alloc = repair(inst, raw) if raw is not None else None
            rep = inst_mod.evaluate(inst, rep_alloc) if rep_alloc is not None else None

            rec = {
                "task_id": task_id or f"{iid}::{variant}",
                "instance_id": iid,
                "variant": variant,
                "family": inst["family"],
                "size": inst["size"],
                "model": row.get("model", "unspecified"),
                "optimum": opt,
                "value": res["value"],
                "ratio": res["value"] / opt if opt else 0.0,
                "legal": res["legal"],
                "exact": res["legal"] and res["value"] == opt,
                "failure": classify(res["reason"]),
                "reason": res["reason"],
                "repaired_value": rep["value"] if rep else 0,
                "repaired_ratio": (rep["value"] / opt) if (rep and opt) else 0.0,
                "blocking_free": optima[iid].get("blocking_free", True),
            }
            for extra in ("latency_ms", "prompt_tokens", "completion_tokens"):
                if extra in row:
                    rec[extra] = row[extra]
            records.append(rec)
    return {"records": records}


def summarise(rows: list[dict]) -> dict:
    if not rows:
        return {"n": 0}
    strict = [r["ratio"] for r in rows]
    legal = [r["ratio"] for r in rows if r["legal"]]
    repaired = [r["repaired_ratio"] for r in rows]
    failures: dict[str, int] = {}
    for r in rows:
        failures[r["failure"]] = failures.get(r["failure"], 0) + 1
    return {
        "n": len(rows),
        "strict_mean_ratio": round(statistics.mean(strict), 4),
        "strict_median_ratio": round(statistics.median(strict), 4),
        "valid_only_mean_ratio": round(statistics.mean(legal), 4) if legal else None,
        "repaired_mean_ratio": round(statistics.mean(repaired), 4),
        "exact_rate": round(sum(r["exact"] for r in rows) / len(rows), 4),
        "legal_rate": round(sum(r["legal"] for r in rows) / len(rows), 4),
        "failures": failures,
    }


def aggregate(records: list[dict]) -> dict:
    rows = [r for r in records if "error" not in r]
    agg = {"overall": summarise(rows), "by_model": {}, "by_variant": {},
           "by_family": {}, "by_size": {}, "by_model_family": {}}
    for m in sorted({r["model"] for r in rows}):
        agg["by_model"][m] = summarise([r for r in rows if r["model"] == m])
    for v in sorted({r["variant"] for r in rows}):
        agg["by_variant"][v] = summarise([r for r in rows if r["variant"] == v])
    for f in sorted({r["family"] for r in rows}):
        agg["by_family"][f] = summarise([r for r in rows if r["family"] == f])
    for s in sorted({r["size"] for r in rows}):
        agg["by_size"][str(s)] = summarise([r for r in rows if r["size"] == s])
    agg["blocking_free_only"] = summarise([r for r in rows if r["blocking_free"]])
    for m in sorted({r["model"] for r in rows}):
        for f in sorted({r["family"] for r in rows}):
            sub = [r for r in rows if r["model"] == m and r["family"] == f]
            if sub:
                agg["by_model_family"][f"{m}/{f}"] = summarise(sub)
    return agg


def check_matrix(records) -> list[str]:
    """The experimental matrix must be complete and unique per model.

    Missing tasks silently bias means (a model that fails to answer the hard
    tasks looks better); duplicates double-count. Rows for unknown tasks or
    rows whose explicit metadata disagrees with their task id are also errors.
    An empty response file is an error rather than an empty experiment. All
    problems are hard errors unless explicitly waived, and the waiver still
    prints every hole.
    """
    with open(INST_DIR.parent / "llm_tasks.jsonl") as fh:
        tasks = [json.loads(line) for line in fh if line.strip()]
    expected = {t["task_id"]: t for t in tasks}
    problems = []
    by_model = {}

    if not records:
        problems.append("empty response file")

    for r in records:
        task_id = r.get("task_id")
        model = r.get("model", "unspecified")
        task = expected.get(task_id)
        if not task_id:
            problems.append(f"missing task_id: ({model}, line {r.get('line', '?')})")
            continue
        if task is None:
            problems.append(f"unexpected: ({model}, {task_id})")
            continue

        expected_iid = task.get("instance_id") or task_id.split("::", 1)[0]
        expected_variant = task.get("variant") or (
            task_id.split("::", 1)[1] if "::" in task_id else "unknown")
        if ("instance_id" in r and r["instance_id"] != expected_iid):
            problems.append(
                f"inconsistent instance_id: ({model}, {task_id}) has "
                f"{r['instance_id']!r}, want {expected_iid!r}")
        if ("variant" in r and r["variant"] != expected_variant):
            problems.append(
                f"inconsistent variant: ({model}, {task_id}) has "
                f"{r['variant']!r}, want {expected_variant!r}")

        if "error" not in r:
            by_model.setdefault(model, []).append(task_id)

    for model, ids in sorted(by_model.items()):
        seen = set()
        for tid in ids:
            if tid in seen:
                problems.append(f"duplicate: ({model}, {tid})")
            seen.add(tid)
        for tid in sorted(set(expected) - seen):
            problems.append(f"missing: ({model}, {tid})")
    return problems


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("responses", help="JSONL of model responses")
    ap.add_argument("-o", "--out", default=str(RESULTS / "llm.json"))
    ap.add_argument("--allow-incomplete", action="store_true",
                    help="downgrade missing/duplicate matrix entries from a "
                         "hard error to a printed warning")
    args = ap.parse_args()

    scored = score_file(Path(args.responses))
    records = scored["records"]
    broken = [r for r in records if "error" in r]

    matrix_problems = check_matrix(records)
    if matrix_problems:
        head = "MATRIX INCOMPLETE" if args.allow_incomplete else "MATRIX ERROR"
        print(f"{head}: {len(matrix_problems)} problem(s)")
        for p in matrix_problems:
            print(f"  {p}")
        if not args.allow_incomplete:
            print("refusing to aggregate; pass --allow-incomplete to override")
            return 1

    agg = aggregate(records)

    print(f"{len(records)} responses, {len(broken)} unreadable lines")
    for title, block in (("OVERALL", {"all": agg["overall"]}),
                         ("BY MODEL", agg["by_model"]),
                         ("BY VARIANT", agg["by_variant"]),
                         ("BY FAMILY", agg["by_family"]),
                         ("BY SIZE (k)", agg["by_size"])):
        print(f"\n{title}")
        print(f"  {'group':<26} {'n':>4} {'strict':>7} {'valid':>7} "
              f"{'repair':>7} {'exact':>7} {'legal':>7}")
        for group, s in block.items():
            if not s.get("n"):
                continue
            vo = s["valid_only_mean_ratio"]
            print(f"  {group:<26} {s['n']:>4} {s['strict_mean_ratio']:>7.3f} "
                  f"{(vo if vo is not None else float('nan')):>7.3f} "
                  f"{s['repaired_mean_ratio']:>7.3f} {s['exact_rate']:>7.3f} "
                  f"{s['legal_rate']:>7.3f}")

    fails = agg["overall"].get("failures", {})
    if fails:
        print("\nFAILURE KINDS")
        for kind, n in sorted(fails.items(), key=lambda kv: -kv[1]):
            print(f"  {kind:<18} {n}")

    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps({
        "source": str(args.responses),
        "aggregate": agg,
        "unreadable_lines": broken,
        "per_response": records,
    }, indent=1) + "\n")
    print(f"\n-> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
