"""Exact-rational cross-check of the empirical certificates (round 14, F2).

MODEL.md section 4 states the theorems over exact-rational damage arithmetic;
the reference simulator (`scripts/homm3_model.py`) evaluates the same formula
in Python floats, and that float routine is the operative definition of every
optimum in `instances/optima.json` and every value in `results/llm.json`.
The two arithmetics do NOT agree on every call (`scripts/exact_damage.py`:
base 90 against attack 0 / defence 10 with the DEFEND bonus floors to 62 in
floats and to 63 exactly), so whether any of the 145 optima or 870 scores
would change under the exact semantics is a question this script MEASURES,
in two passes over the three certification suites the paper cites:

  * verify_full_model_optima  -- ghost bound recomputed for all 145 instances
  * check_defend_policy       -- (‡) phase-aware replay of all 145 optima
  * certify_scores            -- all 870 scored responses, bound + replay

Pass 1 (DUAL): `exact_damage.install_dual` wraps `compute_damage` everywhere
the suites reach it; every call is evaluated in BOTH arithmetics, the float
result is returned (so the suites run exactly the computation the paper
reports) and every call-level split is recorded.  Pass 2 (EXACT): the exact
routine is installed outright and the same three suites judge the RECORDED
numbers against it; a suite failure there names a certified number the exact
semantics would change.  A positive control (the base-90 cell) is fed through
the instrumented routine first, so a silent instrumentation failure cannot
print zero splits.

Round-14 result (2026-09-11): 909 638 damage calls, 202 call-level splits
(every one a float result one point BELOW the exact one, all on non-witness
branches of the searches), and all three suites pass unchanged under the
exact routine: no recorded optimum, replay or score moves.  So the 145 optima
and 870 scores are certified under both arithmetics -- a measured fact about
this corpus, not a property of the formula.

Policy: like `audit_ability_projection.py` and `check_artifact_repo.py`, this
script is NOT part of `test_regressions.py` (it re-runs the 84-second scoring
suite twice); the battery drills the instrumentation (positive control), runs
the exact routine through the 145-optimum replay in-process, and pins this
script's recorded final-line counters in `verification_manifest.json`.

Run:  python3 empirics/scripts/exact_arithmetic_crosscheck.py
"""

from __future__ import annotations

import contextlib
import io
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "scripts"))

import exact_damage  # noqa: E402
import homm3_model as M  # noqa: E402
import solve  # noqa: E402
import verify_full_model_optima  # noqa: E402
import check_defend_policy  # noqa: E402
import certify_scores  # noqa: E402

SUITES = (("verify_full_model_optima", verify_full_model_optima.main),
          ("check_defend_policy", check_defend_policy.main),
          ("certify_scores", certify_scores.main))


def positive_control() -> None:
    """The instrumented routine must SEE a known float/exact split."""
    trace = exact_damage.DualTrace()
    undo = exact_damage.install_dual(trace, solve)
    try:
        got = exact_damage.probe_call(M.compute_damage)
    finally:
        undo()
    if not (got == 62 and trace.disagreements
            and trace.disagreements[0][-2:] == (62, 63)):
        raise SystemExit(f"positive control failed: {got}, {trace.disagreements}")


def run_quiet(fn, argv: list[str]) -> tuple[int, str]:
    saved = sys.argv
    sys.argv = argv
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            rc = fn()
    finally:
        sys.argv = saved
    return rc, buf.getvalue()


def main() -> int:
    positive_control()
    print("positive control: the instrumented routine reports the base-90 split "
          "(float 62, exact 63)")

    # pass 1: dual trace, float results returned
    trace = exact_damage.DualTrace()
    undo = exact_damage.install_dual(trace, solve)
    dual_ok = True
    try:
        for name, fn in SUITES:
            before, t0 = trace.calls, time.time()
            rc, out = run_quiet(fn, [name])
            print(f"dual  {name}: rc={rc}, {trace.calls - before} damage calls, "
                  f"{time.time() - t0:.0f}s")
            dual_ok = dual_ok and rc == 0
    finally:
        undo()
    deltas = sorted({want - got for *_, got, want in trace.disagreements})
    for base, att, deff, defending, got, want in trace.disagreements[:5]:
        print(f"      e.g. base {base} att {att} def {deff} defending {defending}: "
              f"float {got} exact {want}")
    print(f"dual  trace: {trace.summary()}; exact minus float on the splits: {deltas}")

    # pass 2: exact routine installed outright, recorded numbers judged by it
    original = M.compute_damage
    M.compute_damage = exact_damage.exact_compute_damage
    solve.compute_damage = exact_damage.exact_compute_damage
    exact_ok = True
    exact_fail_lines = []
    try:
        for name, fn in SUITES:
            t0 = time.time()
            rc, out = run_quiet(fn, [name])
            print(f"exact {name}: rc={rc}, {time.time() - t0:.0f}s")
            exact_ok = exact_ok and rc == 0
            if rc != 0:
                exact_fail_lines.append(f"--- {name} under exact arithmetic ---\n{out}")
    finally:
        M.compute_damage = original
        solve.compute_damage = original
    for block in exact_fail_lines:
        print(block)

    moved = "0 certified numbers moved" if exact_ok else "CERTIFIED NUMBERS MOVED"
    print(f"exact-arithmetic cross-check: {trace.calls} damage calls, "
          f"{trace.fractional} with a fractional factor, "
          f"{len(trace.disagreements)} call-level float/exact splits, "
          f"{moved}; suites under floats "
          f"{'pass' if dual_ok else 'FAIL'}, under exact rationals "
          f"{'pass' if exact_ok else 'FAIL'}")
    if not (dual_ok and exact_ok):
        print("FAILED")
        return 1
    print("ALL PASS: the 145 recorded optima (bound and witness), their (‡) replays "
          "and the 870 scored responses are reproduced exactly by the exact-rational "
          "routine of MODEL.md section 4; the call-level splits above lie on branches "
          "that do not decide any certified number")
    return 0


if __name__ == "__main__":
    sys.exit(main())
