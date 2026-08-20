#!/usr/bin/env python3
"""Recomputes the §5.2 observation-2 statistics from results/llm.json.

Round 9 (DeepSeek API leg) pointed out that the Spearman coefficients, the
k-bucket table and the natural-family sequence in §5.2 were computed once by
hand and written into the paper with no generating artifact — the exact
failure mode this project keeps finding in itself. This script IS the
generating artifact now: it recomputes every number of observation 2 from
`results/llm.json` (which certify_scores.py in turn re-derives from the raw
responses), prints them in the paper's own formatting, and
test_regressions.py compares the printed lines against the paper's prose.

No dependencies; Spearman is computed with average ranks over ties.
"""

from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LLM = HERE.parent / "results" / "llm.json"

NATURAL_PREFIX = "natural"
MODELS = ("claude-haiku-4-5", "claude-sonnet-5", "claude-opus-5")


def ranks(xs: list[float]) -> list[float]:
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and xs[order[j + 1]] == xs[order[i]]:
            j += 1
        avg = (i + j) / 2 + 1
        for t in range(i, j + 1):
            out[order[t]] = avg
        i = j + 1
    return out


def spearman(xs: list[float], ys: list[float]) -> float:
    rx, ry = ranks(xs), ranks(ys)
    n = len(rx)
    mx = sum(rx) / n
    my = sum(ry) / n
    cov = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    vx = sum((a - mx) ** 2 for a in rx) ** 0.5
    vy = sum((b - my) ** 2 for b in ry) ** 0.5
    return cov / (vx * vy)


def main() -> int:
    per = json.loads(LLM.read_text())["per_response"]
    haiku = [r for r in per
             if r["model"] == "claude-haiku-4-5" and r["variant"] == "assisted"]
    ks = [r["size"] for r in haiku]
    rs = [r["ratio"] for r in haiku]
    nat = [r for r in haiku if r["family"].startswith(NATURAL_PREFIX)]
    print(f"haiku assisted responses: {len(haiku)} "
          f"({len(nat)} on the natural families)")
    print(f"Spearman(k, ratio) all = {spearman(ks, rs):.2f}; "
          f"natural = {spearman([r['size'] for r in nat], [r['ratio'] for r in nat]):.2f}")

    sizes = sorted({r["size"] for r in per})
    for model in MODELS:
        cells = []
        for k in sizes:
            sub = [r["ratio"] for r in per
                   if r["model"] == model and r["variant"] == "assisted"
                   and r["size"] == k]
            cells.append(f"{sum(sub) / len(sub):.3f}" if sub else "—")
        print(f"| `{model}` | " + " | ".join(cells) + " |")

    seq = []
    for k in sizes:
        sub = [r["ratio"] for r in haiku
               if r["family"].startswith(NATURAL_PREFIX) and r["size"] == k]
        seq.append(f"{sum(sub) / len(sub):.3f}" if sub else "—")
    print("natural-family haiku sequence: " + ", ".join(seq))

    # round 10 (fable minor): the §5.2 HEADLINE table, the baseline rows and
    # observation 3's percentage-point figures were the last §5.2 numbers
    # with no generating artifact — they join the printed set here and
    # test_regressions.py sweeps them against both papers
    def agg(model: str, variant: str) -> tuple[float, float]:
        sub = [r["ratio"] for r in per
               if r["model"] == model and r["variant"] == variant]
        exact = sum(1 for x in sub if x == 1.0)
        return sum(sub) / len(sub), 100.0 * exact / len(sub)

    pps = {}
    for model in MODELS:
        a_mean, a_exact = agg(model, "assisted")
        r_mean, r_exact = agg(model, "raw")
        pps[model] = (a_mean - r_mean) * 100
        print(f"| `{model}` | {a_mean:.3f} | {a_exact:.1f} % | "
              f"{r_mean:.3f} | {r_exact:.1f} % |")
    print("geometry-removal cost: "
          f"Haiku {pps['claude-haiku-4-5']:.2g} percentage points, "
          f"Sonnet {pps['claude-sonnet-5']:.2g}, and "
          f"Opus {pps['claude-opus-5']:.2g}")

    ov = json.loads((HERE.parent / "results" / "baselines.json")
                    .read_text())["aggregate"]["overall"]
    gv, gd = ov["greedy-value"], ov["greedy-density"]
    print(f"| greedy-value heuristic | {gv['mean_ratio']:.3f} | "
          f"{round(100 * gv['exact_rate'])} % | — | — |")
    print(f"| greedy-density heuristic | {gd['mean_ratio']:.3f} | "
          f"{round(100 * gd['exact_rate'])} % | — | — |")
    rnd = ov["random"]
    print(f"| 100-sample random search baseline | "
          f"{rnd['best_of_n_mean']:.3f} | — | — | — |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
