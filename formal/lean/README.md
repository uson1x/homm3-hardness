# formal/lean — Lean 4 formalization of the HoMM3 hardness paper

The Lean 4 development the paper's Section 4.5 describes; it ships inside the artifact, and the
paths below are relative to this directory (the paper is `../../paper/main.md`, the model
`../../MODEL.md`). Formalization of `paper/main.md` against the model of `MODEL.md`:
Theorem 1, Proposition 1.1 in the paper's generality (Definition E.8, Lemmas E.9–E.10), the
Appendix E lemmas they rest on, Lemma 2.1 in certificate form, the engine's health
representation, and an executable, verified decision procedure cross-checked against the
Python reference scripts.
Tier B adds Theorem 2 (3-PARTITION, Lemmas E.11–E.14), Theorem 4 on the featureless board
(Lemmas E.15–E.22, including E.20 in the R9 order and Lemma E.2 for the family) and
Corollaries 4.1 and 4.2, each with a total reduction.
Session 4 adds Theorem 3 and Corollary 3.1 (X3C, Appendix D) **modulo the embedding**: proved
for every board satisfying (I1)–(I4), with Lemma 3.2 for all `μ ∈ (0,1)`, Lemmas D.1, D.2,
D.3 (the four adapters of Appendix C), D.5–D.9, a total form on certified boards, and a
kernel checker for (I1)–(I4). The checker certifies all 31 boards of `verify_x3c.py`'s default tier
and all 44 literal boards of Lemma D.4's construction (`embed_lemma.py`).
Session 5 proves Lemma D.4 itself, steps 4–6, for **every** valid orthogonal drawing of `G'`
(`lemmaD4`: the board built from the drawing satisfies all of (I1)–(I4)), hence Theorem 3 with the
drawing on the input (`theorem3_drawing`, total form `theorem3_drawing_total`). Steps 0–3
(planarity, degree reduction, packing, Tamassia–Tollis) stay citations. Only step 0's
no-certificates and step 1's sizes are formalized, and those combinatorially. On all 44 corpus
drawings the kernel certifies validity. It also checks that the Lean-built board equals
`build_board_lemma`'s board as data.
Totals at the end of session 5: 35 modules, 12039 library lines, 700 theorems, **0 `sorry`**,
no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, no `native_decide`.
Progress, timings, open `sorry`s and findings: `PROGRESS.md`.

## Versions

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.34.0` (see `lean-toolchain`) |
| Mathlib | tag `v4.34.0` (rev pinned in `lake-manifest.json`) |
| Lake | bundled with the toolchain |

Why not 4.34.1: the Mathlib tag `v4.34.1` sits on a side branch (1 commit ahead of, 208
behind `master` at the time of writing), so `cache.mathlib.org` has no oleans for it and
`lake exe cache get` downloads nothing. Tag `v4.34.0` is on `master` and is fully cached.

## Build

```
export PATH=$HOME/.elan/bin:$PATH
lake exe cache get      # ~8.9k Mathlib oleans, a few GB, once
lake build
```

## Layout

| File | Content |
|---|---|
| `Homm3/Hex.lean` | Stage 1: offset hexes, R1 adjacency, R2 distance, layered BFS reach, Lemma E.3 (metric half) |
| `Homm3/Damage.lean` | Stage 2: R7 damage in exact rationals, monotonicity, the `(★)` and `DEFEND` (E.20) arithmetic |
| `Homm3/Knapsack.lean` | Stage 3: 0-1 knapsack optimum `(K)` and the dynamic program, `dp = OPT` |
| `Homm3/Corridor.lean` | Stage 3: the corridor geometry of `G(a)`, Lemma E.4 |
| `Homm3/Battle.lean` | Stage 4: instances, allocations, `H3-det-melee` round semantics against `(‡)` (relation `Step`), `ArmyAllocation` |
| `Homm3/BattleFacts.lean` | Stage 4: general facts about `Step`; Lemma E.1 in model form (`lemmaE1`, `lemmaE1_once`) |
| `Homm3/CorridorGame.lean` | Stage 4: the corridor family `inst n t v d B W` as a game; value-destroyed formula |
| `Homm3/Prop11.lean` | Stage 4: Proposition 1.1 upper bound (`upper`) |
| `Homm3/Prop11Lower.lean` | Stage 4: Proposition 1.1 lower bound, the witness play (`lower`) |
| `Homm3/Theorem1.lean` | Stage 5: `prop11_opt`, `prop11_decide`, `theorem1` (`PARTITION a ↔ ARMY-ALLOCATION (G a)`), `theorem1_total` |
| `Homm3/HexGraph.lean` | Session 2: Lemma E.3, converse half — R2 distance = graph distance of R1 (`mem_reach_univ_iff`) |
| `Homm3/MatchingReach.lean` | Session 2: Definition E.8 (`PMR`), Lemma E.9 (`lemmaE9`) for any instance, Lemma E.10 (`Corridor.pmr`) |
| `Homm3/Prop11General.lean` | Session 2: Proposition 1.1 in general form (`prop11_general`, `prop11_general_decide`), corridor as special case, preprocessing, array decision |
| `Homm3/Health.lean` | Session 2: engine health `(fullUnits, firstHPleft)` ≃ pool; `count`, `alive`, `applyDamage`, `kills(D)` agree |
| `Homm3/KnapsackArray.lean` | Session 2: the one-row in-place array DP of `dp_single_type.dp` equals `dp` (`dpArray_eq_dp`) |
| `Homm3/Exec.lean` | Session 2: executable semantics (`succs ↔ Step`), termination, verified search, `armyAllocation_iff`, `Decidable (ArmyAllocation I)`, attack-only fragment |
| `Homm3/Certificate.lean` | Session 2: Lemma 2.1 as certificate + checker (`armyAllocation_iff_cert`) |
| `Homm3/ExecExamples.lean` | Session 2: `#guard` regression checks of the executable semantics |
| `Homm3/ThreePartition.lean` | Session 3: the 3-PARTITION promise and family form, counting half, explicit seatings, integer encoding, Bool checkers |
| `Homm3/Accounting.lean` | Session 3: the strike/blow ledger for any instance (`ledger`), the stock-one family `famInst`, no-direction for every layout (`Fam.fam_no`) |
| `Homm3/Theorem2.lean` | Session 3: `G_{3P}`, Lemmas E.11–E.14 (`sep`, `flower`, `lemmaE12`, witness), `Thm2.theorem2`, `theorem2_total` |
| `Homm3/Walk.lean` | Session 3: row walks inside the BFS reach |
| `Homm3/Theorem4.lean` | Session 3: `G_F`, attack-only play, Lemmas E.15–E.19, E.21, E.22, `ThmF.theorem4`, Corollaries 4.1 (`cor41`) and 4.2 (`cor42`), total forms |
| `Homm3/LemmaE20.lean` | Session 3: the R9 order invariant, Lemma E.20 (`ThmF.lemmaE20`), Lemma E.2 for the family, seat capacity ≤ 6 |
| `Homm3/X3C.lean` | Session 4: `X3C`, exact cover, Lemma 3.2 (`lemma32`, abstract `resource`), blow arithmetic at every `Δ < 0` (`blow_resource`), the constants |
| `Homm3/X3CBoard.lean` | Session 4: abstract board with (I1)–(I4) (`Inv`) and the consumed part (`InvCore`), `G3 hpP defQ` / `G3pub`, walks in the BFS reach (`mem_reach_of_rtg`), Lemma D.1 |
| `Homm3/Theorem3.lean` | Session 4: generalized ledger, Lemmas D.5–D.9, witness run, `theorem3`, `theorem3_pub`, `cor31`, `winning_unique` |
| `Homm3/BoardCheck.lean` | Session 4: boards as data (dense and packed), Bool checker with `check_sound`, fixed yes-board `D1`, `theorem3_total`, `cor31_total`, `coverCheck`, verdict package `YesV`/`NoV` |
| `Homm3/Gadgets.lean` | Session 4: translation invariance, Lemma D.2, enemy gadget, Lemma D.3 (four adapters), step-4 separation facts |
| `Homm3/EmbedGeom.lean` | Session 5: step 4 of D.4 — directions, `φ`, (SEP) per unit segment (`sep_pt`, `sep_seg`, `sep_vv`, `sep_rays`, `box_ray`), routes `DEdge` and their scaled points, `corr_iff`, the adapter facts (`arms_*`) |
| `Homm3/Embed.lean` | Session 5: `OrthoDrawing`, `Valid` ((D1)–(D3), `G'` from step 1), `build` (steps 4–6), `prox`, `near_z`, `set_ports`, (I1), connectivity, **`lemmaD4`**, `theorem3_drawing`, `cor31_drawing`, `build_size` |
| `Homm3/EmbedCheck.lean` | Session 5: Bool drawing checker with `check_sound`, `theorem3_drawing_total`, `SameBoard` (board as data) |
| `Homm3/Step0.lean` | Session 5: step 0 of D.4 — no-certificates (`no_mod3`, `no_few`, `no_uncovered`, `step0_sound`), `cover_dedup`, `cover_zero` |
| `Homm3/Step1.lean` | Session 5: step 1 of D.4 combinatorially — `G'` for a cut rotation, `card_V` (`4|C|`), `card_E` (`6|C| − |X|`) |
| `Homm3/Axioms.lean` | `#print axioms` for the headline theorems (only `propext`, `Classical.choice`, `Quot.sound`) |
| `CrossCheck.lean` | Sessions 2–3: instance builders and runners for the cross-check against `brute_force.py` / `dp_single_type.py` / `verify_featureless.py`, and kernel-checked instance verdicts (library `CrossCheck`, not a default target) |
| `CrossCheckRun1.lean`, `CrossCheckRun2.lean`, `CrossCheckThm2.lean`, `CrossCheckThm2Full.lean` | Session 2: cross-check runners (`lake build CrossCheck && lake env lean <file>`); results in `PROGRESS.md` |
| `CrossCheckX3CData.lean`, `CrossCheckX3C.lean` | Session 4: the 31 default-tier boards of `verify_x3c.py` and the negative control, verdicts through `theorem3` in the kernel (`lake build CrossCheckX3C`, about 45 s) |
| `CrossCheckLemmaData.lean`, `CrossCheckLemma.lean` | Session 4: the 44 literal boards of Lemma D.4's construction, verdicts through `theorem3` in the kernel (`lake build CrossCheckLemma`) |
| `CrossCheckDrawingData.lean`, `CrossCheckDrawing*.lean` | Session 5: the 44 corpus drawings; in the kernel each is `Valid`, the Lean board equals the `build_board_lemma` board as data, `G'` is Lean's step 1, and (I1)–(I4) and the verdict follow from `lemmaD4` (`lake build CrossCheckDrawing`, about 80 s) |
| `tools/export_drawing.py` | Session 5: replays steps 0–3 of `build_board_lemma`, asserts the drawing matches the board's features, writes the drawing modules |
| `tools/export_x3c.py`, `tools/export_lemma.py`, `tools/appendix_c.py` | Session 4: generators of the data modules and of the Appendix C literals (read-only imports of `homm3/scripts`) |
| `CrossCheckRun3.lean` | Session 3: `verify_featureless.py` C6 tier on `G_F` (greedy lower bound, proof-level upper bound); the kernel-checked verdicts `t2_c*`, `t4_*` live in `CrossCheck.lean` |
