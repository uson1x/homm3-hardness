#!/usr/bin/env python3
"""Smoke tests for the scorer: it must survive anything a model can emit.

The scorer sits between the LLM run and every number in the report, so it gets
its own tests. Most of these are things models actually do — fencing the JSON,
prefacing it with a sentence, using an object per slot instead of a pair,
counting in strings, or quietly overspending the stock.

Run:  python3 scripts/test_scorer.py     (expects OK)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import instance as inst_mod  # noqa: E402
import score_llm  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
INST_DIR = ROOT / "instances"

failures: list[str] = []


def check(name: str, got, want) -> None:
    if got != want:
        failures.append(f"{name}: got {got!r}, want {want!r}")


def check_true(name: str, cond) -> None:
    if not cond:
        failures.append(name)


def main() -> int:
    optima = json.loads((INST_DIR / "optima.json").read_text())

    # a single-type instance (bare integers allowed) and a multi-type one
    single = inst_mod.load(next(INST_DIR.glob("corridor-k3-y00.json")))
    multi = inst_mod.load(next(INST_DIR.glob("naturalM-k4-00.json")))
    s_opt = optima[single["id"]]["optimum"]
    s_alloc = optima[single["id"]]["allocation"]

    # --- extraction is forgiving about packaging --------------------------
    for label, text in [
        ("plain", '{"allocation": [1, 2, 0]}'),
        ("fenced", '```json\n{"allocation": [1, 2, 0]}\n```'),
        ("preamble", 'Sure! Here is my answer:\n\n{"allocation": [1, 2, 0]}\n'),
        ("trailing prose", '{"allocation": [1, 2, 0]}\nThat spends the budget.'),
        ("nested extra keys", '{"reasoning": "x", "allocation": [1, 2, 0]}'),
        ("bare list", '[1, 2, 0]'),
    ]:
        alloc, err = score_llm.extract_allocation(text)
        check(f"extract/{label}", (alloc, err), ([1, 2, 0], None))

    for label, text in [
        ("prose only", "I would put most of them in the first slot."),
        ("empty", ""),
        ("broken json", '{"allocation": [1, 2,'),
    ]:
        alloc, err = score_llm.extract_allocation(text)
        check_true(f"extract/{label} must fail", alloc is None and err)

    # --- the optimal answer scores exactly 1.0 ----------------------------
    res = inst_mod.evaluate(single, s_alloc)
    check("optimal allocation is legal", res["legal"], True)
    check("optimal allocation hits the optimum", res["value"], s_opt)

    # --- semantic violations are illegal, not silently clipped ------------
    over = [["C", single["army"][0]["stock"] + 5]] + [None] * (single["size"] - 1)
    res = inst_mod.evaluate(single, over)
    check("overspending is illegal", res["legal"], False)
    check("overspending scores zero", res["value"], 0)
    check("overspending is classified", score_llm.classify(res["reason"]),
          "over_budget")

    res = inst_mod.evaluate(single, [-1] + [None] * (single["size"] - 1))
    check("negative count is illegal", res["legal"], False)

    res = inst_mod.evaluate(single, [None] * (single["size"] + 2))
    check("wrong length is illegal", res["legal"], False)

    res = inst_mod.evaluate(multi, [["Nosuchcreature", 1]] + [None] * 3)
    check("unknown type is illegal", res["legal"], False)
    check("unknown type is classified", score_llm.classify(res["reason"]),
          "unknown_type")

    res = inst_mod.evaluate(multi, "not a list at all")
    check("non-list is illegal", res["legal"], False)

    res = inst_mod.evaluate(single, [1.5, None, None])
    check("fractional count is illegal", res["legal"], False)

    res = inst_mod.evaluate(single, [True, None, None])
    check("boolean count is illegal", res["legal"], False)

    # --- matrix integrity is a hard gate ----------------------------------
    with open(ROOT / "llm_tasks.jsonl") as fh:
        tasks = [json.loads(line) for line in fh if line.strip()]
    matrix = [{"task_id": t["task_id"], "model": "matrix-test",
               "instance_id": t["instance_id"], "variant": t["variant"]}
              for t in tasks]
    check_true("empty matrix is a hard error",
               any("empty response file" in p for p in score_llm.check_matrix([])))
    check_true("missing matrix row is flagged",
               any("missing:" in p for p in score_llm.check_matrix(matrix[1:])))
    check_true("duplicate matrix row is flagged",
               any("duplicate:" in p for p in score_llm.check_matrix(matrix + [matrix[0]])))
    check_true("unexpected task id is flagged",
               any("unexpected:" in p for p in score_llm.check_matrix(
                   matrix + [{"task_id": "not-a-task::raw", "model": "matrix-test"}])))
    inconsistent = [dict(row) for row in matrix]
    inconsistent[0]["instance_id"] = "wrong-instance"
    inconsistent[0]["variant"] = "wrong-variant"
    inconsistent_problems = score_llm.check_matrix(inconsistent)
    check_true("inconsistent instance_id is flagged",
               any("inconsistent instance_id:" in p for p in inconsistent_problems))
    check_true("inconsistent variant is flagged",
               any("inconsistent variant:" in p for p in inconsistent_problems))

    # bare integers must be refused when the army has several types
    res = inst_mod.evaluate(multi, [1, 1, 1, 1])
    check("bare int on multi-type is illegal", res["legal"], False)

    # object-per-slot form is accepted
    name = multi["army"][0]["type"]
    res = inst_mod.evaluate(multi, [{"type": name, "count": 1}, None, None, None])
    check("object form is legal", res["legal"], True)

    # --- repair only fixes mechanics, and never invents legality ----------
    rep = score_llm.repair(single, [single["army"][0]["stock"] + 5, 0, 0])
    check_true("repair trims to the stock",
               inst_mod.evaluate(single, rep)["legal"])
    rep = score_llm.repair(single, [1, 2])          # too short
    check("repair pads to length", len(rep), single["size"])
    check_true("repair of junk is None", score_llm.repair(single, "junk") is None)

    # --- end to end through score_file ------------------------------------
    tmp = ROOT / "results" / "_test_responses.jsonl"
    tmp.parent.mkdir(parents=True, exist_ok=True)
    rows = [
        {"task_id": f"{single['id']}::assisted", "model": "t",
         "response": json.dumps({"allocation": s_alloc})},
        {"task_id": f"{single['id']}::raw", "model": "t",
         "response": "I refuse to answer."},
        {"task_id": f"{single['id']}::assisted", "model": "t",
         "response": json.dumps({"allocation": over})},
        {"task_id": "no-such-instance::assisted", "model": "t", "response": "{}"},
    ]
    with open(tmp, "w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")
        fh.write("this line is not json at all\n")

    recs = score_llm.score_file(tmp)["records"]
    check("score_file reads every line", len(recs), 5)
    good = [r for r in recs if r.get("exact")]
    check("one response is exactly optimal", len(good), 1)
    check("refusal is unparseable", recs[1]["failure"], "unparseable")
    check("refusal scores zero", recs[1]["ratio"], 0.0)
    check("overspending is over_budget", recs[2]["failure"], "over_budget")
    check_true("unknown instance is reported", "error" in recs[3])
    check_true("bad JSONL line is reported", "error" in recs[4])

    agg = score_llm.aggregate(recs)
    check("aggregate counts only readable rows", agg["overall"]["n"], 3)
    tmp.unlink()

    if failures:
        print(f"FAILED ({len(failures)}):")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("OK: scorer survives malformed, illegal and adversarial input")
    return 0


if __name__ == "__main__":
    sys.exit(main())
