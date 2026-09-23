# Two Sources of Hardness in Generalized Heroes of Might and Magic III Combat — artifact

This repository is the complete verification artifact for the paper
*Two Sources of Hardness in Generalized Heroes of Might and Magic III Combat*
(Ivan Parfenchuk, 2026). It contains the full proofs the paper's body
sketches, the executable model, every verification suite the paper's
Section 4 describes together with the table of their current outcomes
(below), the engine cross-check harness, and the empirical companion note
`paper/companion-empirics.md` with its instance corpus and model responses —
the paper's `\src{...}` pointers resolve against this tree's root.

## Layout

| Path | What |
|---|---|
| `paper/` | The paper itself: `main.md` (Markdown master), `main.tex`, `main.pdf`; and `companion-empirics.md`, the empirical companion note (not part of the paper's claims) |
| `MODEL.md` | The combat model `H3-det`, every rule cited to VCMI source `file:line` |
| `proofs/candidate-A.md` | Full proofs: Theorem 1 (+ Proposition 1.1), Theorem 2 |
| `proofs/candidate-C-featureless.md` | Full proof: Theorem 4 and its corollaries |
| `proofs/candidate-D-singletype.md` | Theorem 3 working document (the paper's Appendix D supersedes it) |
| `proofs/attempts/` | Failed reduction attempts, kept with the reason each breaks |
| `scripts/` | The executable model and every verification suite (stdlib-only Python 3) |
| `verification_manifest.json` | Single source of truth for every number the verification-suite table below quotes |
| `engine-check/` | The VCMI engine cross-check: C++ harness, cases, shipped engine outputs, report |
| `empirics/` | The companion note's instance corpus, certified optima, LLM responses, scoring and statistics |
| `VERIFICATION.md` | The verification protocol log, iteration by iteration (Russian) |
| `LIT-REVIEW.md`, `RELATED-WORK.md`, `LIT-AIIDE.md` | Literature notes with per-citation reading depth |
| `STATE.md`, `ASSESSMENT.md`, `CLAUDE.md` | Working documents of the project, kept for provenance (Russian) |

## Running the checks

Python 3, standard library only (the engine cross-check additionally needs a
VCMI checkout and CMake). The complete reproduction block — every suite the
table in the next section reports, with the tier flags that select each row:

```
python3 scripts/verify_mechanics.py          # 90 checks: damage formula, WAIT/DEFEND phases
python3 scripts/test_obstacles.py            # 158 checks on geometry and blocking
python3 scripts/brute_force.py               # Theorems 1-2; defence variants incl. literal (‡)
python3 scripts/brute_force.py --full        # ... adds the unrestricted Theorem 2 tier (4 instances, hold; not re-run by the battery)
python3 scripts/dp_single_type.py            # Prop. 1.1: knapsack, corridors vs the game, control
python3 scripts/verify_featureless.py        # Theorem 4, tiers C1-C5 + the exhaustive play tier C6 on the 2 smallest instances
python3 scripts/verify_featureless.py --full # ... C6 on all 4 smallest instances (not re-run by the battery)
python3 scripts/verify_x3c.py                # Theorem 3, historical constants (def 41)
python3 scripts/verify_x3c.py --vacate       # ... admitting pure movement
python3 scripts/verify_x3c.py --defend       # ... with the defence playing (‡) literally
python3 scripts/verify_x3c.py --full --vacate  # ... q ≤ 4 corpus (minutes; not re-run by the battery)
python3 scripts/crosscheck_sol.py            # Theorem 3 as PUBLISHED (def 27, hp 4, μ = 0.35)
python3 scripts/crosscheck_sol.py --defend   # ... published constants AND literal (‡)
python3 scripts/crosscheck_sol.py --full     # ... the full corpus (minutes; not re-run by the battery)
python3 scripts/search_free_order.py         # free activation order, vanish; both constant sets
python3 scripts/verify_embedding.py          # Lemma D.4's algorithm itself, on the whole corpus
python3 scripts/classify_skips.py            # classify every router skip (minutes, by hand)
python3 scripts/fuzz_pipeline.py             # seeded fuzz of the Lemma D.4 pipeline + planarity oracle (minutes; outside the battery)
python3 scripts/verify_hp_objective.py       # Corollary 4.2 (hit-point objective)
python3 scripts/check_stub.py                # Lemma D.4 step 5: the deployment-stub clause, 64 cases
python3 empirics/scripts/verify_full_model_optima.py  # companion-note optima, full action model
python3 empirics/scripts/certify_scores.py   # companion-note per-response scores, full action model
python3 empirics/scripts/check_defend_policy.py  # (‡) replay; --legacy-defend = control
python3 empirics/scripts/check_ability_shift.py  # ability projection shifts an optimum (pinned)
python3 empirics/scripts/stats_recheck.py    # every statistic the companion note quotes
python3 empirics/scripts/exact_arithmetic_crosscheck.py  # floats vs exact rationals, three suites twice
python3 scripts/test_regressions.py          # regressions + the doc-consistency battery
cd engine-check && ./build.sh && ./run.sh && python3 compare.py
```

Section 4.4 of the paper prints the four-line summary of this block; the
table in the next section is what each suite runs and its current outcome.

## Verification suites

What each suite runs, at what scale, and its current outcome. The table is
rendered from `verification_manifest.json` by
`scripts/gen_verification_table.py` between the marker comments below and is
not edited by hand: `scripts/test_regressions.py` re-renders it in check mode
(an edit that bypasses the manifest fails the battery) and pins every counter
to the artifact that generates it — by re-running the generating suite and
parsing its own final line for the mechanics, obstacle, DP, hp-objective,
embedding, featureless, brute-force, free-order, stub and legacy-control
suites and the default tiers of both Theorem 3 suites; by re-deriving the
engine verdicts offline from the shipped engine outputs; by the lengths of the
shipped empirical artifacts for the instance and response counts; by the
recorded log plus an in-process replay of its witness half for the arithmetic
cross-check; for the two `--full` Theorem 3 tiers (`verify_x3c.py --full
--vacate` and `crosscheck_sol.py --full`, eight counters, minutes each), by
sweeping the documents that quote them, since only rerunning those tiers
re-derives the counts; and for the `--full` extension of the featureless
suite's C6 tier, by the length of that suite's own small-instance list,
read in-process — sweeps the counters the paper and the companion note
quote, and bans retired claims verbatim. The
generator validates each row against the manifest's declared ordered sequence
of counter placeholders, their per-cell placement, and the row's declared
literal digit-runs (read with a free-standing sign); the battery rebuilds six
demonstrated mutations in memory on every run — a counter retyped as a literal
digit, two placeholders swapped inside one row, a counter moved across a cell
boundary, a deleted duplicate digit-run, the (SEP′) class minima reordered, a
sign placed in front of a literal — and requires each to fail validation. The
guard's reach stops at the numbers and their placement and establishes no
numeric *meaning*: the table's prose is rendered from the manifest but not
generated from the artifacts, so a rewritten claim is a manifest edit the
drills cannot see. Which review round demonstrated which mutation, and what
each check does and does not establish, is `VERIFICATION.md`. Two further
checks live outside the battery by policy, like `audit_ability_projection.py`:
`scripts/check_artifact_repo.py`, which needs the network, and
`scripts/fuzz_pipeline.py`, a seeded fuzz of the Lemma D.4 pipeline (300
random families through the router, every board checked for (I1)–(I4) and
(SEP′), every no-certificate checked for truth) together with an exhaustive
comparison of the DMP planarity test against an independent forbidden-subgraph
oracle on all 32 768 labelled graphs on six vertices.

Two scope details that Section 4.1 of the paper states in summary and this
table quantifies. *What "the allocation space" means differs by suite:*
Theorem 1's PARTITION suite enumerates *every* count vector summing to at most
the stock, nothing pruned; Theorem 2's 3-PARTITION suite enumerates every
deployment fielding each type exactly once — the shape its witnesses take —
with an unrestricted tier (arbitrary partial assignments) run under `--full`
on four instances and the `hold` variant only. *The capped defended branch* —
`def 32`, `0.025 · 31 = 0.775`, crossing the cap — is never struck in the
reduction suites' `(‡)` runs (no searched player waits, so no blow lands on a
target that is already defending; review round 13 instrumented the damage
calls and recorded zero such calls); it is exercised arithmetically by
`verify_mechanics.py` and by a phase-ordered trace in `test_regressions.py` in
which a waiting player strikes a defended target at the capped multiplier, and
its engine reading is pinned by the harness's ULP cases.

<!-- verification-table:begin -->
| suite | scale | outcome |
|---|---|---|
| `verify_mechanics.py` | 90 checks | all pass |
| `brute_force.py` | 28 + 14 instances × 3 defence variants (`hold`, literal `(‡)`, attacking + `NO_RETALIATION`); the 3-PARTITION tier is m = 2 only, 11 yes / 3 no | all agree with PARTITION / 3-PARTITION |
| `test_obstacles.py` | 158 checks | all pass |
| `dp_single_type.py` | 2000 random instances against exhaustive knapsack search, 40 single-creature corridors played out exhaustively in the game model, plus a multi-creature negative control | agrees everywhere; the control disagrees, exactly as Proposition 1.1's hypotheses require |
| `verify_featureless.py` | 46 instance runs, `m ∈ {2,3}`, two defence variants, through the tiers C1–C5 (reachability, separation, every balanced assignment simulated, the arithmetic relaxation, saturation); plus the exhaustive play tier C6 — targets AND approach hexes, a passing stack may vanish — on the 2 smallest legal instances (`T = 13`, one yes and one no) × 3 allocations each | no mismatches; C6's exact maximum decides 3-PARTITION and never exceeds the relaxation |
| `verify_featureless.py --full` | C6 on all 4 smallest legal instances (`T ∈ {13, 16}`, two yes, two no) × 3 allocations; outside the battery, which pins the instance list's length in-process | same |
| `verify_x3c.py` | 31 instances (17 yes, 14 no), `q ≤ 2`, historical constants (`def 41`, `μ = 0.3`) | all agree, all winners canonical |
| `verify_x3c.py --vacate` | the same 31, pure movement admitted | identical answers |
| `verify_x3c.py --defend` | the same 31, defence executing `(‡)` literally | identical answers |
| `verify_x3c.py --full --vacate` | 55 instances (30 yes, 25 no), `q ≤ 4`, 4 skipped by the router | all agree |
| `crosscheck_sol.py --full` | 37 machine-built planar boards (23 yes, 14 no), 3 skipped by the router, under the **published** Theorem 3 constants (`def 27`, `hp 4`, `μ = 0.35`) | all agree |
| `crosscheck_sol.py --defend` | 25 instances, published constants AND literal `(‡)` — the combination round 8 found had never been run | all agree |
| `search_free_order.py` | 16 boards — one corpus of eight q = 2 families, each built and searched under BOTH the historical (def 41) and the published (def 27) constants, the swap asserted at build time — searched with free activation order (any unacted player stack may act next), pass and vanish branches and exhaustive approach hexes, over every allocation (12 yes / 4 no builds), under the `hold` defence, which dominates (‡) for the player | the free-order answer equals X3C and the fixed order on every (family, constant set, allocation) triple; yes-instances admit only the all-ones winner; 3 discriminating controls — order, vanish, destination — on which the full search strictly beats its degraded variants; the negative control (defence = attack) flips 1 planar no-instance to yes; the corpus tiers expanded 3860 out-of-order activations and 6312 vanish branches and met 0 states offering a second approach hex — Lemma D.7 from the searcher's side, so the destination branch is exercised by its control only |
| `verify_embedding.py` | 61 corpus families through the Lemma D.4 embedding algorithm itself (DMP planarity → orthogonal drawing → `λ = 20` scaling, adapters, stubs): 44 boards built; 17 certified degenerate no-instances, 3 of them also non-planar; 0 certified non-planar — plus a separate battery of 17 malformed encodings and one planted non-planar control, all deterministic | I1–I4, the Lemma D.4 feature counts (4|C| boxes, 6|C| − |X| corridors) and the feature-based (SEP′) separation hold on every board (28151 non-incident feature pairs, class minima L∞ 12/16/20 against the required 12); the no-certificate board, assembled from its own encoding, plays out as a genuine no; the full game search runs on 3 of them — under the historical AND the published constants — and agrees with X3C; every free hex within L∞ < 12 of a deployment stub lies in its own element's region (6584 hexes on the corpus; the nearest free hex outside the stub's own vertex box is at L∞ 5, which is why step 5 of Lemma D.4 no longer says nothing lies within that distance) |
| `check_stub.py` | Lemma D.4 step 5, the deployment-stub clause: every used-port set of a vertex box (at most three ports) × every unused stub direction × both row parities, adjacency from the model's own neighbour rule — 64 local configurations | 0 failures: the outer stub hex has exactly one free neighbour in every case |
| `verify_hp_objective.py` | 16 instances (10 yes, 6 no), plus a negative control | relaxation = `mT` iff 3-PARTITION; witness absorbs exactly `mT` |
| `verify_full_model_optima.py` | all 145 empirical instances | every optimum certified over the full action model; the ghost bound also dominates every `(‡)` play (see `paper/companion-empirics.md`) |
| `certify_scores.py` | all 870 scored responses | every score certified likewise, and reproduced exactly by the `(‡)` phase-aware replay |
| `check_defend_policy.py` | all 145 replayed under `(‡)`, phase-aware | all equal the recorded optima; `--legacy-defend` reproduces the 6 round-5 violations (negative control) |
| `exact_arithmetic_crosscheck.py` | the three suites above re-run twice: every damage call evaluated in Python floats AND in the exact rationals of Section 2 of the paper (909638 calls, 347332 with a fractional factor), then with the exact routine installed outright | 202 call-level splits, each a float result one point below the exact one, none on a deciding branch: all 145 optima, their `(‡)` replays and all 870 scores are reproduced exactly under exact arithmetic; positive control (float 62 vs exact 63) detected |
| `test_regressions.py` | 319 regressions: one per error ever caught here, a phase-ordered trace of the capped defended branch, and a doc-consistency battery that re-renders this very table into README.md from its manifest, re-runs the generating suites to pin the manifest's counters (only the two `--full` Theorem 3 tiers excepted — those are swept against the proof document), sweeps the counter prose in the siblings, the paper body and the companion note, and bans 19 retired claims verbatim | all pass |
| engine harness | 49 cases | 46 exact, 3 explained (Section 4.2 of the paper); includes 6 turn-order cases run through the engine's own `battleGetTurnOrder` |
<!-- verification-table:end -->

One remark about the built/skipped split, so that rerunning the code holds no surprises.
The board router for Theorem 3 is a randomized heuristic, and a skip is an honest failure
of the layout search, never a board emitted in violation of the invariants. An earlier
revision explained the skips by the typical non-planarity of random 3-uniform incidence
structures; the per-family classification refutes that. There are 7 router skip events
across the two full corpora —
4 in the `--full --vacate` tier, 3 in the crosscheck corpus — concerning 5 distinct
families (two are skipped in both corpora), and every one of them is a degenerate
no-instance with an uncovered element, whose layout the hill-climb gives up on.
Non-planarity does occur but is not what drives the skips: the corpora contain
exactly 3 non-planar families, all of them also degenerate, and because the embedding
algorithm certifies degeneracy *before* it tests planarity, they surface in the table's
degenerate count ("of which 3 are also non-planar") while the "certified non-planar"
count stays at zero — that zero records the order of the checks, not the absence of
non-planar inputs (an earlier revision misread it exactly that way; the non-planar exit
itself is exercised by a planted control). An earlier revision also cut the router's retries with a per-instance
wall-clock deadline, which made the built/skipped split depend on machine load; review
round 8 caught the counts drifting between runs; the deadline is now gone (retries are
capped by attempt count only), and the split is a deterministic function of the fixed seeds,
so the numbers above reproduce exactly. What the suite asserts was never affected either way:
every board it builds satisfies the invariants, every instance it builds agrees with the
source problem, and on every yes-instance the unique winning allocation is the canonical one.
A final transparency note: the corpus families are drawn by seeded random generators, and
nothing here claims they are pairwise non-isomorphic — the instance counts measure runs of
the pipeline, not distinct combinatorial structures.

## VCMI provenance

Every rule in `MODEL.md` and every engine number in `engine-check/` cites a
[VCMI](https://github.com/vcmi/vcmi) source location (GPLv2). Two commit
hashes appear in this artifact:

- **`deeab240c8d6db193101669a7702bfc0e4f4e872`** — the public anchor: a
  merge commit on `vcmi/vcmi` `develop` (2026-06-19). Check citations against
  this commit.
- **`b5cee705b`** — the working checkout the harness was actually built
  from: a fork merge whose sole difference from `deeab240` across `lib/`,
  `config/`, `server/` and `test/` is 18 lines in
  `lib/callback/AIFactory.cpp`, a file nothing here cites. Every cited path
  is byte-identical between the two commits.

Scripts that read a VCMI checkout honour the `VCMI_CHECKOUT` environment
variable (default: the author's local path).

## Licenses

- Code (`scripts/`, `empirics/scripts/`, `verification_manifest.json`): MIT (see `LICENSE`).
- Text (`paper/`, `MODEL.md`, `proofs/`, reports and notes): CC BY 4.0.
- `engine-check/` (builds against VCMI classes): GPL-2.0-or-later, matching VCMI (see `engine-check/LICENSE-note.md`).

## Provenance

Most of this artifact was produced with substantial AI assistance under the
author's direction, and went through eleven adversarial review rounds
(multiple independent model families plus the author's own runs) before
publication; the paper's Acknowledgements and Section 4 describe the process
and the paper trail. The review-round documents themselves live in the
project's private working repository; this artifact is the verified result.
