# PROGRESS — Lean Tier A pilot

Executor: Claude Opus 5.5 (`claude-opus-5-5`), session 2026-09-24/25 (MSK).
Rule: every commit builds (`lake build` green); `sorry` allowed only with a WHY comment.

## Stage 0 — toolchain

- Start 23:51, finish 00:09 (≈18 min).
- `lake init Homm3 math` against Lean 4.34.1 / Mathlib `v4.34.1`: the Mathlib cache
  returned 0 of 8908 files. Cause: Mathlib tag `v4.34.1` (commit `d13f23b`) is *diverged*
  from `master` (ahead 1, behind 208), and the cache is only populated for `master`
  commits. Fix: pin Lean `v4.34.0` + Mathlib tag `v4.34.0` (on `master`): 8906/8908 files
  downloaded, `import Mathlib` builds (the root `Mathlib.olean` is rebuilt locally, 47 s).
- Style linters (`weak.linter.mathlibStandardSet`) switched off: header/copyright noise.

## Stage 1 — hexes and reach

- Start 00:09, finish 00:14. `sorry`: 0.
- Proved (`Homm3/Hex.lean`): `Hex.gauge_eq` (R2 gauge = `max(|a|,|b|,|a−b|)`),
  `Hex.gauge_add` (subadditivity), `Hex.dist_triangle`, `Hex.dist_of_adj` (every R1 step
  has R2 length 1, both parities), `Hex.adj_symm`, `Hex.dist_row`, `start_mem_reach`,
  `reach_mono`, `dist_le_of_mem_reach` (BFS reach in `s` layers ⇒ `dist ≤ s`, for any set
  of free hexes), `strike_radius` (Lemma E.3: strike ⇒ `dist ≤ s+1`).
- Not done: the other half of E.3 (R2 distance = graph distance of the full grid); not
  needed by anything downstream.

## Stage 2 — damage

- Start 00:14, finish 00:17. `sorry`: 0.
- Proved (`Homm3/Damage.lean`): `fAtt_mono`, `fDef_mono`, `fAtt_pos`, `fDef_pos`,
  `one_le_damage` (clamp), `damage_mono` (damage monotone in Δ, i.e. raising defence only
  lowers it), `damage_zero` (Δ = 0 ⇒ damage = c·d, **needs `1 ≤ c·d`** — `damage 0 d 0 = 1`
  by the clamp; the paper states it with `c ≥ 1, d ≥ 1`, so not a finding),
  `damage_le_nominal`, `defendBonus_one` (+1 at def 1), `damage_neg_one`,
  `damage_neg_one_le`, `damage_neg_one_eq_iff` (Δ = −1: damage = nominal **iff** c·d = 1),
  `damage_neg_one_lt` (strict for c·d ≥ 2); cross-check example from MODEL.md §4
  (base 90, Δ = −12 ⇒ 63 in exact arithmetic).

## Stage 3 — corridor geometry and knapsack

- Start 00:17, finish 00:20. `sorry`: 0.
- `Homm3/Knapsack.lean`: `feasible`, `OPT` (display (K)), `dp` (prefix recurrence);
  `le_dp`, `dp_attained`, **`dp_eq_OPT`**, `OPT_attained`, `le_OPT`. The in-place
  one-row array loop of `dp_single_type.dp` is not formalized (the recurrence is; the
  descending-capacity argument is in the module doc only).
- `Homm3/Corridor.lean`: `p j = (5j,0)`, `e j = (5j+1,0)` (0-indexed); `adj_p_e`,
  `dist_p_e` (= |5(j−j')−1|, the E.4 formula), `dist_p_e_self`, `dist_p_e_ne` (≥ 4),
  `dist_backward` (= 4), `dist_forward` (= 6), the width-4 remark (= 3),
  `no_foreign_strike` (E.3 + E.4: a speed-2 stack on `p j` strikes only `e j`).

## Stage 4 — round semantics, Lemma E.1, Proposition 1.1

- Start 00:20, finish 00:45 (semantics 7 min, upper bound 9 min, witness 4 min, explicit
  E.1 statements 2 min, the rest building/fixing). `sorry`: 0.
- `Homm3/Battle.lean` — the model, written against MODEL.md §§3–6, 9 and `homm3_model.py`:
  `CType` (H3-det-melee tuple + value), `Instance` (board, obstacles, deployment hexes,
  army with stocks, enemy stacks, `R`, `W`), `Feasible` (a slot holds one army entry; per
  entry total ≤ stock), `Stack` (health as the pool `avail`, `count = ⌈avail/hp⌉`,
  retaliation charges, `DEFEND` flag), `blow` (R7 with the `DEFEND` bonus on the target),
  `resolveAttack` (move, strike, retaliation iff target alive ∧ attacker alive ∧ charge),
  `normalQueue` / `waitLe` (R9 orders), `free` / `reachOf` (BFS over enterable hexes),
  `Step` (nondeterministic relation: skip dead, `(‡)` WAIT, `(‡)` DEFEND, player
  WAIT / DEFEND / move / WALK_AND_ATTACK, phase switch, round boundary), `Done`,
  `destroyed` (Σ (init − count)·value over enemy stacks), **`ArmyAllocation`**.
- `Homm3/BattleFacts.lean` (any instance): `Step.St` (side/slot/type/init never change),
  `Step.pool_le` (pools never grow), `Step.hex_of_enemy` (the defence never moves),
  `Step.Q_sub` (inside a round the queue-and-bucket only shrinks and stays duplicate-free),
  `Step.hex_of_mem` (a stack not yet terminal has not moved), `Step.pool_cases` (pools change
  only in WALK_AND_ATTACK), **`lemmaE1`** (R = 1: every stack not yet terminal stands on its
  deployment hex), **`lemmaE1_once`** (after its terminal action a stack is never activated
  again in round 1 ⇒ at most one blow), `Q_antitone`.
- `Homm3/CorridorGame.lean`: the Prop 1.1 family `inst n t v d B W` (G(a) with enemy hp
  `t j`, value `v j`, player damage `d`); `init_player`, `init_enemy`, `destroyed_eq`
  (value destroyed = Σ of `v j` over enemies with empty pool).
- `Homm3/Prop11.lean`: `blow_le_nominal` (§2.4 "at most nominal", with or without the DEFEND
  bonus), invariant `UInv` (key clause `t_j ≤ pool(E_j) + [slot j terminal]·c_j·d`),
  `UInv.step`, **`upper`**: every play under every feasible allocation destroys
  `≤ OPT(K)` with `b_j = ⌈t_j/d⌉`.
- `Homm3/Prop11Lower.lean`: witness allocation `αW`, `αW_feasible`, invariants `WN`
  (NORMAL phase) / `WW` (WAIT phase), `WN.step`, `WN.run`, `WW.run`, **`lower`**: for every
  `S` feasible for (K) there is a feasible allocation and a *complete* play (`Done`)
  destroying `≥ Σ_S v`.
- Scope limits (not blockers, choices): Prop 1.1 is proved for the family the reduction
  constructs (corridor, arbitrary `t`, `v`, `d ≥ 1`, `t_j ≥ 1`), not for every instance
  satisfying Definition E.8; the pool representation of health is not proved equivalent
  to the engine's `(fullUnits, firstHPleft)` pair (argued in the module doc); the NORMAL
  queue is sorted once at the round start (the engine recomputes it; keys are static);
  with `R = 0` the model would still play one round (all theorems use `R = 1`); the
  semantics has no executable cross-check against `homm3_model.py` (the relation is not
  executable).

## Stage 5 — Theorem 1

- Start 00:40, finish 00:43. `sorry`: 0.
- `Homm3/Theorem1.lean`: **`prop11_opt`** (optimum over all allocations and plays = `dp` =
  `OPT`, attained by a complete play), **`prop11_decide`** (`ArmyAllocation (inst …) ↔
  W ≤ dp`), `PARTITION` (`∃ S ⊆ [n], 2·Σ_S a = Σ a`), `G a = inst n a a 1 (Σa/2) (Σa/2)`,
  **`theorem1`**: `∀ a, (∀ x ∈ a, 0 < x) → Even (Σ a) → (PARTITION a ↔ ArmyAllocation (G a))`,
  `Gno`, `Gno_no` (the fixed no-instance is a no-instance), `PARTITIONℤ`, `reduction`
  (the Appendix E totality branch on integer lists), **`theorem1_total`**:
  `∀ a : List ℤ, PARTITIONℤ a ↔ ArmyAllocation (reduction a)`.
- Not formalized (outside the pilot by the brief): NP-hardness of PARTITION, NP membership
  (Lemma 2.1), polynomial running time of the map and of the DP.
- `Homm3/Axioms.lean`: every headline theorem depends only on `propext`,
  `Classical.choice`, `Quot.sound`.

## Totals (at the stage-5 commit)

- 11 modules + root `Homm3.lean`, 1845 lines; 70 top-level definitions/structures/instances, 106 theorems,
  4 `example`s; **0 `sorry`**, 0 axioms introduced.
- Wall clock: stage 0 18 min (cache problem), stages 1–5 36 min, total ≈ 55 min.

## Findings

Nothing in the paper's mathematics for Theorem 1 / Proposition 1.1 failed to go through.
What the formalization surfaced:

1. **Brief, not paper — the PARTITION definition.** The brief's `∃ S, Σ_S a = Σ a / 2`
   is wrong with truncating division: for `a = (1, 2)` it accepts `S = {1}`, although no
   partition exists. The Lean file uses `2·Σ_S a = Σ a` (equivalent to the paper's
   "`Σ a = 2B`, `Σ_S a = B`").
2. **Lemma E.2 is not load-bearing for Theorem 1 and Proposition 1.1.** Neither Lean proof
   uses it. Upper bound: only "pools never grow" is needed, so a stack's count stays
   `≤ c_j`. Witness: a player stack is hurt only by retaliation, which comes after its own
   blow, so it is intact when it acts, whatever `hp` and enemy attack are. So E.5(3)'s
   "by Lemma E.2 no player creature dies, so the stack is alive to take its action" is
   correct but stronger than needed. The parts of `(★)` that E.2 consumes (player `def`,
   enemy `att` and damage, player `hp = 5`) are free parameters for these two results; only
   `att(player) ≤ def(enemy)` (for "at most nominal") and `=` (for "exactly nominal") are used.
3. **Initiative order and enemy speed play no role.** The proofs never use the sort
   orders of R9, only that each phase queue is a permutation of the living stacks. This
   matches §2.4 ("regardless of relative speeds") and means the enemy's `spd = 1` in
   `G(a)` is irrelevant.
4. **Artifact discrepancy, `homm3/scripts/dp_single_type.py`.** The docstring of
   `build_corridor` (line 59) says "Theorem 1's corridor verbatim", but line 69 builds the
   enemies with `hp=hp, speed=0, value=val)`. The paper's `G(a)` has enemy `spd = 1`, and
   MODEL.md Definition 3.1 requires `spd ∈ ℤ_{>0}`, so speed 0 is outside the model's
   domain. By finding 3 this cannot change any number the check reports, but "verbatim"
   is inaccurate.
5. **Theorem 1 for `n = 0`.** The equivalence `PARTITION a ↔ ARMY-ALLOCATION (G a)` also
   holds for the empty list (`W = 0`). The paper's rerouting of the empty instance to
   `G((1,1))` is needed only so that `W ∈ ℤ_{>0}`, exactly as the paper says. Consistent,
   recorded for completeness.
6. **Δ = −1 arithmetic** (Lemma E.20's): proved as an *iff* (`damage_neg_one_eq_iff`),
   equality exactly when `c·d = 1`. Consistent with the paper.

## Blockers and friction

- The only real blocker was stage 0 (Mathlib cache empty for tag `v4.34.1`), ≈ 10 min.
- Lean-side friction, each resolved in 1–3 build cycles: `if_pos`/`if_neg` are deprecated
  in this Mathlib (warnings only); `omega` does not see through structure projections
  or nonlinear products (fixed by `generalize` / explicit `have`s); `simp` normal forms of
  `Finset.filter` with a constant-true predicate; naming inaccessible variables after
  `cases` on the `Step` relation.
- Environment friction: the worktree guard rejects compound shell commands whose text
  mentions git-like words (e.g. a `.gitignore` in a heredoc), so files were written with
  the editor tool and builds run through a small script.

## Estimate

- **Tier A complete** (additionally: Proposition 1.1 for every instance with persistent
  matching reach — Definition E.8, Lemma E.9 in general form — the pool ↔
  `(fullUnits, firstHPleft)` equivalence, the other half of Lemma E.3, the array-level DP):
  about **one more session** of this size.
- **Tier B** (Theorems 2 and 4 through Appendix E) is realistic. The semantics and the
  general step facts are reusable as they are. Theorem 2 (three rows, stock-one types,
  3-PARTITION combinatorics, separation 7) is about one session. Theorem 4 is the expensive
  one: the witness (Lemmas E.16–E.19) needs explicit walks through the BFS on a 6-row board
  with row parity, plus a "row 1 stays clear" invariant, and the converse of the reach lemma
  (a free walk of length ≤ s lies in the reach). Estimate 2–3 sessions. Total Tier B:
  **3–4 sessions**.

---

# Session 2 — Tier A completed (2026-09-25, MSK)

Executor: Claude Opus 5.5 (`claude-opus-5-5`). Branch `worktree-policy-wait-defend`, base
`e685fe0`. Every commit builds; **0 `sorry`** at every commit. Headline theorems audited in
`Homm3/Axioms.lean`: all depend only on `propext`, `Classical.choice`, `Quot.sound`
(`Knapsack.dpArray_eq_dp` on `propext`, `Quot.sound` only).

## Model refinement (08:53–08:57), before target 1

- `initUnits` now gives an **empty slot** (`count = 0`) the type `default`, whatever type index
  the allocation names. Before, an empty slot carried the type of the army entry its index
  named. That was harmless, since the stack is dead, but the set of allocations was then not
  finite up to the starting position (any type index), so `ARMY-ALLOCATION` was not
  enumerable. The new form is also closer to `brute_force.assemble`, which creates no stack
  for an empty slot. Session-1 proofs re-checked: `CorridorGame.slotType` got the guard
  `0 < count`, and `init_player` and `WN.init` were adjusted (two new lemmas `slotType_of`,
  `pool_slotType`). Commit `487906c`.

## Target 1 — Definition E.8, Lemma E.9 (general), Lemma E.3 in full, Lemma E.10 (08:57–09:02)

- `sorry`: 0. Modules `Homm3/HexGraph.lean`, `Homm3/MatchingReach.lean`.
- **Lemma E.3, converse half**: `Hex.exists_nbr_closer` (some neighbour is one step closer),
  `mem_reach_univ`, **`mem_reach_univ_iff`** (on the full grid, BFS reach in `s` steps = R2
  ball of radius `s`, i.e. R2 = graph distance of R1), `reach_subset_univ`. The metric half
  (`strike_radius`) is session 1's.
- Instance bookkeeping for an arbitrary `Instance`: `initUnits_player`, `initUnits_enemy`,
  `initUnits_out`, `enemy_index`, `slotType_mem`; `Reach` (positions reachable from an
  allocation's start), `RFrame` / `Reach.frame` (static fields, pools never above the start,
  enemies never move), `Reach.mem_Q` (in round 1 a not-yet-terminal stack was alive at the
  start).
- **Definition E.8**: `CanStrike I us i t` (living enemy with a hex of `i`'s BFS reach adjacent
  to it, the empty walk included), `Matching I σ` (bijection slots `0…k−1` → enemies
  `0…n−1`), **`PMR I σ`** (`R = 1` and, for every feasible allocation, every reachable position
  and every slot `j ∈ s.Q`, `CanStrike j t ↔ t = k + σ j`).
- **Lemma E.9**: `MetricTest I σ` (hypotheses (1) adjacency, (2) separation `> s + 1` for every
  army speed, plus every enemy alive at the start); `MetricTest.contain` (containment, from
  Lemma E.1 + `strike_radius`, in every reachable position), `MetricTest.untouched` (the enemy
  of a slot that has not acted is untouched), **`lemmaE9 : MetricTest I σ → PMR I σ`**.
- **Lemma E.10**: `Corridor.metricTest`, **`Corridor.pmr`** (every corridor instance, hence every
  `G(a)`, has persistent matching reach with `σ = id`).
- Lemma E.3's second half as the brief phrases it ("adjacency ⇒ strike legal when the enemy is
  alive") is the non-emptiness part of `lemmaE9` (approach hex = own hex, `start_mem_reach`).

## Target 2 — Proposition 1.1 in the paper's generality (09:02–09:08)

- `sorry`: 0. Module `Homm3/Prop11General.lean`.
- Hypotheses `Prop11Hyp I C B σ`: `PMR I σ`; `I.army = [(C, B)]`; `1 ≤ C.dmg`; `1 ≤ C.hp`; every
  enemy stack one creature of `hp ≥ 1`; `def(E_j) = att(C)` for every enemy. `Star I` is the
  paper's full `(★)`; `Prop11Hyp.ofStar` derives the damage hypothesis from it.
- Upper bound: `Prop11.key` (invariant `t_{σ j} ≤ pool(E_{σ j}) + [j terminal]·c_j·d`, with
  Definition E.8 applied at every attack step), `Prop11.upper` (≤ `OPT` of `(K)`). Lower bound:
  witness `αW`, invariants `GWN` / `GWW` carrying reachability, `GWN.step` takes the approach
  hex that Definition E.8 provides *in the current position*, `Prop11.lower`. Packaged:
  **`prop11_general`** (optimum over all allocations and plays = `dp`, attained by a complete
  play), **`prop11_general_decide`** (`ArmyAllocation I ↔ W ≤ dp`).
- Special case: `Corridor.prop11Hyp` (via Lemma E.10), **`Corridor.prop11_decide_via_general`**
  re-derives session 1's `prop11_decide` from the general theorem (`Knapsack.dp_congr`).
- Also (target 5): **`prop11_preprocess`**, the preprocessing claim of the proof. With `B ≥ 1`
  the allocation "one creature in slot `j`, nothing else" is feasible, and in its start the
  strikable set is exactly `{E_{σ j}}`, so one BFS per slot recovers `σ`.
  **`prop11_general_decide_array`**: the decision by the array program of `dp_single_type.py`.

## Target 3 — health pool ≡ engine representation (09:08–09:14)

- `sorry`: 0. Module `Homm3/Health.lean`.
- `EHealth` = `(fullUnits, firstHPleft)`, `Valid` (`(0,0)` or `firstHPleft ∈ (0, hp]`),
  `avail`, `count`, `fresh`, `setFromTotal` and `applyDamage` (both branches, the overkill
  clamp, the `firstHPleft = 0 ∧ fullUnits ≥ 1` correction, transcribed literally from
  MODEL.md §3 / `homm3_model.Stack`), `kills` (MODEL.md's formula literally), `ofPool`.
- For `hp ≥ 1`: **`equivPool`** (valid engine states ≃ ℕ via `avail`), `count_ofPool` /
  `count_eq_pool` (R6 = `⌈avail/hp⌉`), `alive_iff`, `avail_fresh` / `count_fresh`,
  `setFromTotal_eq`, **`avail_applyDamage`** (engine damage = truncated subtraction on the
  pool), `ofPool_sub` (commuting square), `poolCount_sub`, **`kills_eq`** (the engine's
  `kills(D)` = drop in `count`, for every valid state and every `D`). Phrased for the model's
  `Stack`: `Stack.count_engine`, `alive_engine`, `hit_engine`, **`kills_engine`**,
  `fresh_engine`. Examples checked by `decide` against hand runs of `apply_damage`, one of them
  through the correction branch.

## Target 4 — execution cross-check (09:14–)

### The verified executable layer (`Homm3/Exec.lean`, `sorry`: 0)

- `reachL` (list BFS, `mem_reachL`), `targets`, `succs` (all successors), **`step_iff_mem_succs`**
  (`Step I s s' ↔ s' ∈ succs I s`, all nine rules, both directions).
- Measure `μ` (rounds left, phase queue and bucket lengths): **`Step.μ_lt`**,
  `done_of_μ_zero`, `not_step_of_done`, `succs_ne_nil` (progress).
- `bestWith I next f s` (fuel-bounded max of `destroyed` over complete plays following `next`),
  generic `le_bestWith` / `bestWith_attained`; `value`, `le_value`, `value_attained`.
- `slotChoices`, `allocs`, `normA`, `initUnits_congr`, **`exists_mem_allocs`** (every feasible
  allocation has the starting position of one in `allocs`), `optimum`,
  **`armyAllocation_iff : ArmyAllocation I ↔ I.W ≤ optimum I`** for every instance, and hence
  `instance : Decidable (ArmyAllocation I)`.
- The attack-only fragment of `brute_force.py`: `succsAO` (a player stack at its activation
  passes, realized as the legal move to its own hex, or `WALK_AND_ATTACK` with any target and
  approach hex; the defence plays `(‡)`), `step_of_mem_succsAO` (a sub-relation of `Step`),
  `valueAO`, **`valueAO_attained`** (attained by a genuine play), `valueAO_le_value`,
  `armyAllocation_of_AO` (an attack-only value `≥ W` certifies a yes-instance).
- `Homm3/ExecExamples.lean`: `#guard`s at every build (`optimum (G [1,1]) = 1`,
  `optimum (G [1,3]) = 1`, the decisions, a Lemma 2.1 certificate for `G(1,1)`). The kernel
  cannot run the decision instance (`decide +kernel` gets stuck: `List.mergeSort` and
  `Finset` do not reduce), so these checks are compiled evaluation, not kernel proofs.

### What was compared (runners `CrossCheck*.lean`, library `CrossCheck`, not a default target)

Python data: `brute_force.py` run unmodified (`PYTHONDONTWRITEBYTECODE=1`, 37.2 s, `ALL
PASS`); per-bijection Theorem 2 values and the `dp_single_type.py` instances from scratch
scripts that import the modules read-only and re-run their seeded generators. Nothing under
`homm3/` was written.

### Theorem 1 tier (`brute_force.py`, 28 PARTITION instances, variant `waitdefend` = `(‡)`)

Lean builds `G a` (session 1's `Corridor.G`, which is `build_partition_instance` field by
field) and computes (a) the attack-only maximum over **all** feasible allocations,
`max_α valueAO`, the same fragment and allocation set as Python's `best_value`; and (b) the
**full-model optimum** `optimum (G a)` (all allocations, all player actions), the exact
answer by `armyAllocation_iff`. The verdict requires AO = full = Python, and `W ≤ value`
exactly for the PARTITION yes-instances. Runner `CrossCheckRun1.lean`, about 90 min CPU on one process under a loaded machine (the full model dominates; `[6, 6, 7, 7]` alone about 23 min).
(`[1, 2, 3]` appears twice in Python's list, once hand-written and once random: 27 distinct
instances.)

| a | B = W | PARTITION | Python best | Lean AO | Lean full | verdict | ms |
|---|---|---|---|---|---|---|---|
| [1, 1] | 1 | Y | 1 | 1 | 1 | agree | 6 |
| [2, 2] | 2 | Y | 2 | 2 | 2 | agree | 8 |
| [1, 3] | 2 | N | 1 | 1 | 1 | agree | 7 |
| [3, 5] | 4 | N | 3 | 3 | 3 | agree | 36 |
| [2, 4, 6] | 6 | Y | 6 | 6 | 6 | agree | 2246 |
| [1, 2, 3] | 3 | Y | 3 | 3 | 3 | agree | 171 |
| [1, 1, 2, 4] | 4 | Y | 4 | 4 | 4 | agree | 4167 |
| [2, 3, 4, 5] | 7 | Y | 7 | 7 | 7 | agree | 77900 |
| [1, 5, 6, 8] | 10 | N | 9 | 9 | 9 | agree | 437124 |
| [3, 3, 3, 3] | 6 | Y | 6 | 6 | 6 | agree | 43918 |
| [2, 2, 3, 7] | 7 | Y | 7 | 7 | 7 | agree | 99571 |
| [1, 2, 3, 6] | 6 | Y | 6 | 6 | 6 | agree | 46337 |
| [1, 4, 6, 9] | 10 | Y | 10 | 10 | 10 | agree | 433802 |
| [2, 5, 5, 8] | 10 | Y | 10 | 10 | 10 | agree | 1175601 |
| [1, 2, 3] | 3 | Y | 3 | 3 | 3 | agree | 175 |
| [3, 8, 9] | 10 | N | 9 | 9 | 9 | agree | 11953 |
| [4, 4, 6] | 7 | N | 6 | 6 | 6 | agree | 3798 |
| [1, 3, 6] | 5 | N | 4 | 4 | 4 | agree | 1086 |
| [3, 6, 7] | 8 | N | 7 | 7 | 7 | agree | 6172 |
| [4, 8, 8] | 10 | N | 8 | 8 | 8 | agree | 13458 |
| [2, 3, 6, 7] | 9 | Y | 9 | 9 | 9 | agree | 260288 |
| [2, 5, 6, 7] | 10 | N | 9 | 9 | 9 | agree | 406067 |
| [2, 2, 4, 6] | 7 | N | 6 | 6 | 6 | agree | 76468 |
| [2, 2, 3, 3] | 5 | Y | 5 | 5 | 5 | agree | 14553 |
| [2, 4, 5, 7] | 9 | Y | 9 | 9 | 9 | agree | 255606 |
| [1, 1, 4, 4] | 5 | Y | 5 | 5 | 5 | agree | 13530 |
| [4, 5, 6, 7] | 11 | Y | 11 | 11 | 11 | agree | 644034 |
| [6, 6, 7, 7] | 13 | Y | 13 | 13 | 13 | agree | 1369393 |

**28 / 28 agree** (27 distinct instances). On every one, Lean's attack-only maximum equals Lean's full-model optimum and Python's `best_value`. `W ≤` value holds exactly for the 18 PARTITION yes-instances, and for none of the 10 no-instances.

### `dp_single_type.py` check [2] — 40 single-creature corridors + the negative control

Instances: seed 20261018, `k ≤ 3`, `B ≤ 6`, enemies `(1, hp ≤ 5, value ≤ 9)`, enemy speed 0,
reproduced by a scratch run of the script's generator. Lean builds them with
`CrossCheck.dpCorridor` and computes the **full-model optimum** (`optimum`, all player
actions, defence `(‡)`), which by `armyAllocation_iff` is the exact value of the Lean
problem. Python's number is `dp` (the script asserts `dp == game`, its game search running
under `hold`; see finding 5). Runner `CrossCheckRun2.lean`, about 15 s in total.

| trial | enemies (hp, value) | B | dp | Lean full optimum | verdict |
|---|---|---|---|---|---|
| 0 | [(1, 8)] | 3 | 8 | 8 | agree |
| 1 | [(1, 4), (1, 5), (3, 3)] | 5 | 12 | 12 | agree |
| 2 | [(5, 1), (2, 3), (1, 2)] | 5 | 5 | 5 | agree |
| 3 | [(5, 4), (5, 9), (1, 2)] | 2 | 2 | 2 | agree |
| 4 | [(4, 1), (1, 9), (1, 3)] | 6 | 13 | 13 | agree |
| 5 | [(5, 1)] | 6 | 1 | 1 | agree |
| 6 | [(3, 9), (1, 5), (1, 1)] | 1 | 5 | 5 | agree |
| 7 | [(4, 9)] | 6 | 9 | 9 | agree |
| 8 | [(4, 8)] | 6 | 8 | 8 | agree |
| 9 | [(5, 4), (1, 8), (5, 4)] | 4 | 8 | 8 | agree |
| 10 | [(1, 3)] | 6 | 3 | 3 | agree |
| 11 | [(3, 7), (2, 1), (1, 6)] | 1 | 6 | 6 | agree |
| 12 | [(4, 4), (1, 2)] | 6 | 6 | 6 | agree |
| 13 | [(2, 4), (5, 2), (5, 6)] | 2 | 4 | 4 | agree |
| 14 | [(2, 7), (5, 7), (2, 8)] | 6 | 15 | 15 | agree |
| 15 | [(5, 5), (4, 8)] | 2 | 0 | 0 | agree |
| 16 | [(1, 4), (2, 1)] | 1 | 4 | 4 | agree |
| 17 | [(5, 6), (2, 5), (4, 1)] | 5 | 6 | 6 | agree |
| 18 | [(4, 9), (4, 7)] | 5 | 9 | 9 | agree |
| 19 | [(3, 2), (5, 8), (2, 3)] | 2 | 3 | 3 | agree |
| 20 | [(4, 4)] | 1 | 0 | 0 | agree |
| 21 | [(5, 1)] | 2 | 0 | 0 | agree |
| 22 | [(5, 7), (2, 5), (5, 5)] | 1 | 0 | 0 | agree |
| 23 | [(3, 7), (3, 9), (5, 7)] | 4 | 9 | 9 | agree |
| 24 | [(1, 3), (5, 6), (5, 5)] | 2 | 3 | 3 | agree |
| 25 | [(5, 6)] | 6 | 6 | 6 | agree |
| 26 | [(4, 4), (2, 3), (2, 6)] | 1 | 0 | 0 | agree |
| 27 | [(1, 3), (3, 5), (3, 5)] | 4 | 8 | 8 | agree |
| 28 | [(3, 9), (5, 1)] | 1 | 0 | 0 | agree |
| 29 | [(5, 1)] | 2 | 0 | 0 | agree |
| 30 | [(1, 1)] | 5 | 1 | 1 | agree |
| 31 | [(5, 5), (3, 3), (1, 7)] | 5 | 10 | 10 | agree |
| 32 | [(4, 3), (2, 4), (5, 7)] | 4 | 4 | 4 | agree |
| 33 | [(5, 3), (5, 3), (5, 1)] | 2 | 0 | 0 | agree |
| 34 | [(4, 1), (1, 6)] | 1 | 6 | 6 | agree |
| 35 | [(1, 6), (5, 5), (2, 2)] | 2 | 6 | 6 | agree |
| 36 | [(1, 8), (4, 1), (4, 4)] | 3 | 8 | 8 | agree |
| 37 | [(3, 2), (5, 3), (3, 6)] | 2 | 0 | 0 | agree |
| 38 | [(1, 3), (2, 1), (1, 7)] | 5 | 11 | 11 | agree |
| 39 | [(1, 3), (3, 3), (5, 8)] | 6 | 11 | 11 | agree |

**40 / 40 agree.** Negative control (two stacks of 6 creatures, `hp 2`, value 1, `B = 6`):
DP `0`, Python game `3`, **Lean full optimum `3`**, so Lean agrees with the game and
disagrees with the DP, as the suite requires.

### Theorem 2 tier (`brute_force.py`, 14 3-PARTITION instances, `m = 2`) — a documented sample

The full tier is out of reach of the unmemoized verified search: one bijection costs about
65 s in the interpreter (about 15,000 attack-only leaves: six stacks with about five options
each), so 14 × 720 bijections would take about 180 CPU-hours. Python finishes the tier in
seconds only because of its memo and its `relaxed_upper_bound` prune. A verified prune would
need exactly the geometric bound Theorem 2 proves (Tier B). What was run instead
(`CrossCheckThm2.lean`, 6 processes, about 7 min wall):

- per instance, the first two bijections in `itertools.permutations` order;
- for every yes-instance, the first bijection on which Python's search reaches `m = 2` kills
  (the witness), unless it is one of the first two.

That is 34 (instance, bijection) pairs. For each, Lean's attack-only value (`valueAO`, on the
Lean semantics under `(‡)`) is compared with Python's `max_destroyed_value(…,
policy_wait_defend)` on the same allocation. All allocations are feasible (`decide`).

| row | case | a | T | bijection π (slot s gets type π s) | Python | Lean AO | verdict |
|---|---|---|---|---|---|---|---|
| 0 | 0 | [9, 9, 7, 9, 7, 7] | 24 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 1 | 0 | [9, 9, 7, 9, 7, 7] | 24 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 2 | 1 | [8, 9, 12, 11, 8, 8] | 28 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 3 | 1 | [8, 9, 12, 11, 8, 8] | 28 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 4 | 1 | [8, 9, 12, 11, 8, 8] | 28 | [0, 1, 3, 2, 4, 5] | 2 | 2 | agree |
| 5 | 2 | [7, 10, 7, 7, 9, 8] | 24 | [0, 1, 2, 3, 4, 5] | 2 | 2 | agree |
| 6 | 2 | [7, 10, 7, 7, 9, 8] | 24 | [0, 1, 2, 3, 5, 4] | 2 | 2 | agree |
| 7 | 3 | [10, 9, 12, 9, 8, 8] | 28 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 8 | 3 | [10, 9, 12, 9, 8, 8] | 28 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 9 | 3 | [10, 9, 12, 9, 8, 8] | 28 | [0, 1, 3, 2, 4, 5] | 2 | 2 | agree |
| 10 | 4 | [6, 7, 6, 8, 6, 7] | 20 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 11 | 4 | [6, 7, 6, 8, 6, 7] | 20 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 12 | 4 | [6, 7, 6, 8, 6, 7] | 20 | [0, 1, 5, 2, 3, 4] | 2 | 2 | agree |
| 13 | 5 | [7, 7, 8, 8, 10, 8] | 24 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 14 | 5 | [7, 7, 8, 8, 10, 8] | 24 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 15 | 5 | [7, 7, 8, 8, 10, 8] | 24 | [0, 1, 4, 2, 3, 5] | 2 | 2 | agree |
| 16 | 6 | [11, 10, 8, 9, 9, 9] | 28 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 17 | 6 | [11, 10, 8, 9, 9, 9] | 28 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 18 | 6 | [11, 10, 8, 9, 9, 9] | 28 | [0, 2, 3, 1, 4, 5] | 2 | 2 | agree |
| 19 | 7 | [6, 6, 8, 6, 6, 8] | 20 | [0, 1, 2, 3, 4, 5] | 2 | 2 | agree |
| 20 | 7 | [6, 6, 8, 6, 6, 8] | 20 | [0, 1, 2, 3, 5, 4] | 2 | 2 | agree |
| 21 | 8 | [7, 7, 10, 10, 7, 7] | 24 | [0, 1, 2, 3, 4, 5] | 2 | 2 | agree |
| 22 | 8 | [7, 7, 10, 10, 7, 7] | 24 | [0, 1, 2, 3, 5, 4] | 2 | 2 | agree |
| 23 | 9 | [11, 8, 13, 8, 8, 8] | 28 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 24 | 9 | [11, 8, 13, 8, 8, 8] | 28 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 25 | 10 | [10, 8, 10, 9, 11, 8] | 28 | [0, 1, 2, 3, 4, 5] | 2 | 2 | agree |
| 26 | 10 | [10, 8, 10, 9, 11, 8] | 28 | [0, 1, 2, 3, 5, 4] | 2 | 2 | agree |
| 27 | 11 | [8, 8, 8, 8, 9, 7] | 24 | [0, 1, 2, 3, 4, 5] | 2 | 2 | agree |
| 28 | 11 | [8, 8, 8, 8, 9, 7] | 24 | [0, 1, 2, 3, 5, 4] | 2 | 2 | agree |
| 29 | 12 | [8, 8, 7, 11, 7, 7] | 24 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 30 | 12 | [8, 8, 7, 11, 7, 7] | 24 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 31 | 13 | [7, 7, 7, 7, 6, 6] | 20 | [0, 1, 2, 3, 4, 5] | 1 | 1 | agree |
| 32 | 13 | [7, 7, 7, 7, 6, 6] | 20 | [0, 1, 2, 3, 5, 4] | 1 | 1 | agree |
| 33 | 13 | [7, 7, 7, 7, 6, 6] | 20 | [0, 1, 4, 2, 3, 5] | 2 | 2 | agree |

**34 / 34 agree.** Every one of the 11 yes-instances has a sampled bijection with value
`2 = W`. By `armyAllocation_of_AO`, a genuine play of the Lean semantics then destroys `W`, so
the 11 yes answers are confirmed on the Lean model (by compiled evaluation, not a kernel
proof). The 3 no-instances (cases 0, 9, 12) agree on every sampled bijection (value 1), but
their global "no" is **not** checked in Lean: that is Theorem 2's upper bound. A complete
720-bijection run of case 0 (`CrossCheckThm2Full.lean`, 8 processes, about 1.5 h wall) was
started and **stopped**, because the shared machine sat at load average about 120 (backup
and other jobs). The runner stays in the repo. Python's per-bijection values for case 0 are
all 1 (720 of 720), from a scratch run of `dump_full0.py`.

## Target 5 (optional) — NP membership and the array DP (09:40–09:47)

- `sorry`: 0. Modules `Homm3/Certificate.lean`, `Homm3/KnapsackArray.lean`.
- **Lemma 2.1** without a complexity framework: `replay` (a certificate step is an index into
  `succs`), `checkCert` (a Bool checker: feasibility, replay, `Done`, `W ≤ destroyed`),
  `replay_sound`, `exists_path` (every play is a path, one index per step, length bounded by
  the drop of `μ`), `μ_init_le`, **`armyAllocation_iff_cert`**: `ArmyAllocation I ↔ ∃ l path,
  l.length = k ∧ path.length ≤ (R + 1)(2N + 2) ∧ checkCert I l path`. Entries of `l` are
  bounded by feasibility; `checkCert`'s running time is not formalized (no cost model).
- **Array DP**: `rowStep` / `dpArray` transcribe `dp_single_type.dp` (one `Array ℕ` row of
  `B + 1`, `setIfInBounds`, descending capacities, items with `b > B` skipped);
  `rowStep_inv` (the in-place invariant: processed caps hold the new row, lower caps still
  the old one), `rowStep_spec`, `outer_inv`, **`dpArray_eq_dp`**, `dpArray_eq_OPT`.

## Findings (session 2)

1. **Lean model, not paper: an empty slot's type** (see "Model refinement" above). The
   session-1 semantics was correct but made the allocation space infinite. It was fixed
   before anything was built on it, and no session-1 statement changed.
2. **Proposition 1.1 consumes less of `(★)` than it states.** The general proof uses only
   `def(E_j) = att(C)` for every enemy: `≤` for "at most nominal" in the upper bound, `≥` for
   "exactly nominal" in the witness. It also uses `d ≥ 1` and `hp(C) ≥ 1` (Definition 3.1).
   Player defence, enemy attack and damage, and all speeds are free parameters once Definition
   E.8 holds. This extends session-1 finding 2 from the corridor to the general statement.
   Consistent with the paper, which proves only what it needs; the statement could say
   "`def(E_j) = att(C)`" instead of "`(★)`".
3. **Lemma E.9, two implicit hypotheses made explicit.** (a) Hypothesis (2) speaks of "the
   speeds `s_1, …, s_k`" of the slots. In a general instance a slot's speed depends on the type
   allocated to it, so `MetricTest.sep` quantifies over every army type. With one type, as in
   Proposition 1.1, this is exactly the paper's hypothesis. (b) The non-emptiness half ("so
   `E_j` is alive") needs every enemy stack alive at the start. That holds by Definitions
   3.1–3.2 (`c, hp ∈ ℤ_{>0}`) but is a hypothesis of the lemma (`MetricTest.alive`). Neither is
   an error.
4. **Proposition 1.1's upper bound does not need Lemma E.1's "from the deployment hex".** In
   the general proof, Definition E.8 is applied at the attack step itself: the attacker is still
   in the queue, so `CanStrike` applies in that position. Lemma E.1 contributes only "one
   terminal action, after which the stack never acts again this round". The deployment-hex
   half is used inside Lemma E.9 (containment), where the paper also uses it.
5. **`dp_single_type.py` check [2] runs the `hold` defence, not `(‡)`.** It calls
   `max_destroyed_value(build(alloc), 1)` with the default `policy_hold` and enemy speed 0; its
   docstring says "hold policy". The paper's sentence "Proposition 1.1 is machine-checked … against
   exhaustive play of built corridor instances in the game model itself" does not name the
   policy, while Proposition 1.1 is stated for `(‡)`. **Closed by the Lean cross-check**: under
   `(‡)`, over the full action set (`WAIT`, `DEFEND`, move, `WALK_AND_ATTACK`), the optimum equals
   the DP on all 40 instances and is 3 on the negative control. No number moves. This is a
   documentation gap in the artifact, not an error. Recorded here only; `homm3/` is byte-pinned.
6. **The attack-only fragment loses nothing on the Theorem 1 tier.** Lean's full-model optimum
   equals the attack-only optimum and Python's `best_value` on every Theorem 1 instance run in
   the full model (table above). This is an execution-level instance of what
   `prop11_general_decide` proves for the whole family.
7. **No disagreement between the Lean semantics and the Python reference** on any compared
   instance: 28 + 34 + 40 + 1 comparisons. The two schedulers differ in form but agree on these
   plays. Python fixes the `WAIT` list of enemies at the start of the round, while Lean
   buckets an enemy at its `NORMAL` activation and never buckets a dead one. Both skip dead
   stacks, so the order of living waiters is the same.
8. **Kernel evaluation is blocked.** `decide +kernel` cannot run `Decidable (ArmyAllocation I)`,
   even on `G(1,1)`, because `List.mergeSort` (well-founded recursion) and `Finset` sums do not
   reduce. The regression checks are therefore `#guard`s (compiled evaluation). A kernel-checked
   instance would need structurally recursive re-implementations of the sort and the sums.

## Blockers and friction (session 2)

- The worktree guard rejects long heredocs and compound commands that mention git words or
  change directory. Edits were made with the editor tool or small Python patch scripts in the
  scratch directory.
- `Nat.succ_mul` rewrites `2 * N` (as `succ 1 * N`) before the intended product. Fixed with
  explicit `show … from Nat.succ_mul _ _`.
- The interpreter speed (about 6·10⁶ basic operations per second) is what limits the Theorem 2
  tier. Natively compiling a `lean_exe` would mean compiling every imported Mathlib module to C
  (the cache ships only `.olean`s), which is not practical here.

## Totals (end of session 2)

- 19 modules + root, **4034** library lines (session 1: 1845). Also `CrossCheck.lean` and 4
  runners (313 lines).
- Top-level declarations (grep): 100 `def`, 17 `structure`, 8 `instance`, 3 `inductive`,
  1 `abbrev`; **231 theorems** (session 1: 106), 6 `example`s, 6 `#guard`s. **0 `sorry`**,
  0 axioms introduced.
- New modules: HexGraph 145 lines / 12 theorems, MatchingReach 281 / 21, Prop11General 625 /
  30, Health 281 / 21, KnapsackArray 150 / 6, Exec 527 / 32, Certificate 107 / 5,
  ExecExamples 26 / 0.
- Wall clock: reading 8 min; targets 1–3 about 21 min; target 4 verified layer about 25 min, runs
  about 30 min in the background; target 5 about 7 min; write-up about 20 min.

## Estimate for Tier B (Theorems 2 and 4 through Appendix E)

Reusable from Tier A as is:

- The semantics, `BattleFacts`, and all of `MatchingReach`'s bookkeeping for arbitrary instances:
  `initUnits_*`, `Reach`, `RFrame`, `Reach.mem_Q`, `CanStrike`. Also the containment pattern of
  `MetricTest.contain` / `untouched`, which is Lemma E.11's shape for the 3-row flower: a strike
  radius bound against separation 7.
- The invariant-plus-witness architecture of `Prop11General`: a key clause per enemy, and a
  witness run carrying reachability so that per-position hypotheses can be used.
- `Health` (Theorem 4's multi-creature bookkeeping, if needed), `HexGraph` (the converse
  E.3). Theorem 4's witness also needs a "free walk of length ≤ s ⇒ in the BFS reach" lemma for a
  given free set; that is a small extension of `mem_reach_univ`.
- `Exec` (`armyAllocation_iff`, `valueAO`) as an instance-level sanity check. For Theorem 2's
  no-instances it is too slow without a verified memo or prune (about half a session, if
  wanted).

Estimate, unchanged in total and firmer in parts: **Theorem 2 about 1 session**. That covers
the flower geometry on 3 rows, containment by separation 7 via the `MetricTest` pattern,
disjoint striker triples, and the 3-PARTITION combinatorics `T/4 < a_i < T/2 ⇒` exactly three
per group. **Theorem 4 2–3 sessions**: explicit walks on a 6-row board with row parity, the
"row 1 stays clear" invariant, and the E.16–E.19 witness. **Tier B total: 3–4 sessions.**

## Commits (session 2)

- `d887816` formal/lean: PROGRESS/README — сессия 2: цели 1–5, таблицы сверки (dp_single_type 40/40 + контроль, Теорема 2 выборка 34/34), находки, оценка яруса B; таблица Теоремы 1 — после прогона
- `b176952` formal/lean: сессия 2, цель 5 — массивный DP dp_single_type.dp (одна строка, убывающий порядок) = dp = OPT; препроцессинг Предложения 1.1 (один BFS на слот находит σ) и решение через dpArray; раннер полного яруса биекций Теоремы 2
- `1451464` formal/lean: сессия 2, цели 4–5 — исполнимая семантика (succs ↔ Step, мера завершения, перебор с доказанной корректностью, ArmyAllocation ↔ W ≤ optimum, Decidable), фрагмент attack-only как подотношение, сертификат Леммы 2.1; CrossCheck + раннеры; 0 sorry
- `458e58e` formal/lean: сессия 2, цель 3 — представление движка (fullUnits, firstHPleft): биекция с пулом, count/alive/applyDamage/kills(D) совпадают с моделью; 0 sorry
- `cb08d29` formal/lean: сессия 2, цель 2 — Предложение 1.1 в общности статьи (PMR + один тип + одно существо на стек + att=def): prop11_general, prop11_general_decide; коридор выведен как частный случай; аудит аксиом; 0 sorry
- `89ef52f` formal/lean: сессия 2, цель 1 — вторая половина E.3 (R2 = графовое расстояние), Определение E.8 (PMR) и Лемма E.9 для произвольного инстанса, Лемма E.10 для коридора; 0 sorry
- `487906c` formal/lean: пустой слот без типа (как brute_force.assemble) — нужно для перечисления размещений; правки init_player/WN.init
- (this write-up: the commit that adds this section)


# Session 3 — Tier B: Theorems 2 and 4, Corollaries 4.1 and 4.2 (2026-09-25, MSK)

Model: `claude-opus-5-5`. Base `b33b62c`, branch `worktree-policy-wait-defend`. Every target
closed with **0 `sorry`**. All headline theorems are in `Homm3/Axioms.lean`, and each prints
only `propext`, `Classical.choice`, `Quot.sound`.

## Shared layer (`Homm3/ThreePartition.lean`, `Homm3/Accounting.lean`)

- `Promise3P a T` is the promise: `3 ∣ |a|`, `Σ a = (|a|/3)·T`, and `T/4 < a_i < T/2`.
  `THREE_PARTITION a T` is the family form: sets `S_g ⊆ [0, |a|)` of size 3 with sum `T`,
  pairwise disjoint, covering. `ThreeP.of_disjoint` is the counting half, and `Parts` / `pick`
  turn a 3-partition into an explicit seating. `THREE_PARTITIONℤ` with `toNat_iff` is the
  integer encoding used for totality.
- `Accounting.lean` holds the **ledger** (`ledger`, `Ledger.disjoint`, `Ledger.absorbed`,
  `Ledger.dead`). It is an existential strike record, blow record and phase record, kept by
  induction over `Reach`. It gives Lemma E.12's "every stack strikes at most once, at one enemy"
  and E.14's accounting for **any** instance satisfying `AcctHyp`.
- The stock-one family `famInst L a T` fixes stats (player `⟨1,1,a_i,5,spd,0⟩`, enemy
  `⟨1,1,1,T,1,1⟩`, `R = 1`, `W = m`) and leaves the geometry to a `Layout`. **`Fam.fam_no`**
  proves the no-direction (`ArmyAllocation → THREE_PARTITION`) once, for every layout.
  `Fam.destroyed_mul_le` gives `destroyed · T ≤ Σ nominal` for every reachable position.

## Target 1 — Theorem 2 (12:38–13:01, `sorry`: 0)

`Homm3/Theorem2.lean`: `G3P a T = famInst (Thm2.layout m) a T` on the `(8m+2) × 3` board, with
enemy `g` at `(8g+1, 1)` and seats `(8g, 1)`, `(8g+1, 0)`, `(8g+1, 2)`.

- Lemma E.11: `seat_adj`, `seat_inj`, `seat_ne_ehex`, `sep` (separation ≥ 7), `sep_tight` (7 is
  attained), `contain`, `flower` (in every position of the round, a player stack can strike
  only its own group's enemy).
- Lemma E.12: `lemmaE12` (the strike register via the ledger). Lemma E.13: the witness `αP`,
  `αP_feasible`, invariant `WN` (`init`/`step`/`run`), `Thm2.yes`. Lemma E.14: `Fam.fam_no`.
- **`Thm2.theorem2`**: `Promise3P a T → (THREE_PARTITION a T ↔ ArmyAllocation (G3P a T))`.
- **`theorem2_total`**: a total map `reduction3P` on all integer inputs, correct on the promise
  (`reduction3P_iff`). Off the promise it outputs the fixed no-instance `Corridor.Gno`.

## Target 2 — Theorem 4 (13:02–13:14 core, 13:15–13:27 E.20; `sorry`: 0)

`Homm3/Walk.lean` (row walks inside the BFS reach) and `Homm3/Theorem4.lean`: `GF a T` on the
featureless `(4m+2) × 6` board. Deployment is along row 0, enemy `g` sits at `(4g+2, 3)` with
seats `(4g+1, 2)`, `(4g+2, 2)`, `(4g+3, 3)`, and player speed is `4m+8`.

- Attack-only play (`AOReach`, `succsAO_cases`, `exists_doneAO`) and the end-of-round freeze
  (`Frozen`, `Frozen.run`).
- E.15 (the list `(N)` and the seats: `nbrs_ehex`, `seat_mem_nbrs`, `seat_inj`). E.16
  (`lemmaE16`: row 1 stays free). E.17 (`route`: an explicit path through row 1, `≤ w + 2`
  steps). E.18 (`lemmaE18`: full reachability for any placement).
- **`lemmaE19`**: for **any** full injective allocation and **any** seating "three per enemy",
  the three-per-enemy play is realized simultaneously. E.21 (`lemmaE21`) and E.22 (`lemmaE22` =
  `Fam.fam_no`).
- **`ThmF.theorem4`**: `Promise3P a T → (THREE_PARTITION a T ↔ ArmyAllocation (GF a T))`, and
  **`theorem4_total`**.
- `Homm3/LemmaE20.lean` (13:15–13:27): **`orderInv`**, the R9 order in round 1. An enemy stays
  undefended through NORMAL, and the WAIT queue is sorted by `waitLe`. **`wait_attack_defended`**
  says a waiting blow meets the delayed DEFEND. **`Fam.lemmaE2`** is Lemma E.2 for the family: a
  player in the queue has pool 5, and afterwards 4 or 5. **`ThmF.lemmaE20`** proves a
  non-waiting blow does exactly the nominal damage. A waiting blow does `damage 1 a_i (−1)`,
  which is **at most nominal, with equality exactly when `a_i = 1`**. If nobody waited and the
  sum reaches `T`, the enemy is dead. Also **`ThmF.distinct_hexes`** and
  **`ThmF.seat_capacity`** (at most 6 strikers per enemy).

## Target 3 — Corollaries 4.1 and 4.2 (13:02–13:14, with the core of Theorem 4; `sorry`: 0)

- `BattlePlay I α` (the given placement is `αId`). **`ThmF.cor41`**:
  `THREE_PARTITION ↔ BattlePlay (GF a T) αId`, and **`cor41_total`**.
- `absorbed I s` is the sum over enemies of `(initial pool − current pool)`. `HpAllocation I H`
  says some allocation and play absorb `≥ H`. **`ThmF.Fam.hp_no`** is the no-direction for
  every layout: absorbing `mT` forces every enemy to take exactly `T`, hence a 3-partition.
  **`ThmF.cor42`**: `THREE_PARTITION ↔ HpAllocation (GF a T) (mT)`, both for any allocation and
  for `αId`. Also **`cor42_total`**.

## Target 4 — bounded cross-check (13:28–14:05, `sorry`: 0)

Library `CrossCheck` additions (not a default target):

- `threePart_eq6` says session 2's `threePart` **is** `G3P` on every six-entry list. Session
  2's 34 sampled runs are therefore runs of the instance Theorem 2 is about.
- `succsR` / `valueR` is a restricted attack-only search (first approach hex per target).
  `succsG` / `valueG` is a single greedy line (the last listed successor). Both are
  subrelations of `succsAO`, so `valueR_attained` / `valueG_attained` give a genuine play of
  the Lean semantics reaching the value: a verified **lower** bound.
- `gf_value_le` is the verified **upper** bound, `destroyed · T ≤ Σ nominal`, per allocation.
- `ThreeP.checkSeating` / `of_seating` and `checkNoTriple` / `not_of_checkNoTriple` are Bool
  checkers with correctness lemmas. `g3p_yes`, `g3p_no`, `gf_yes`, `gf_no` turn them into
  kernel-checked verdicts through Theorems 2, 4 and the corollaries.

### Theorem 2 tier (`brute_force.py`, 14 instances, `m = 2`) — now proof-level

Each row is a Lean theorem (`CrossCheck.t2_c0 … t2_c13`), checked by the kernel with
`decide`/`rfl`, **not** by running the game search. A yes-row is a seating verified by
`checkSeating` and pushed through `Thm2.theorem2`. A no-row is "no three distinct entries sum
to `T`", verified by `checkNoTriple` and pushed through `Thm2.theorem2`. The Python column is
`three_partition_answer` and the game verdict of `thm2Cases` (scratch
`py_crosscheck.py`, read-only import of `homm3/scripts`).

| case | a | T | Python 3P / game | seating (triples) | Lean theorem | verdict |
|---|---|---|---|---|---|---|
| 0 | [9, 9, 7, 9, 7, 7] | 24 | N / 1 | — (no triple) | `t2_c0 : ¬ ArmyAllocation` | agree |
| 1 | [8, 9, 12, 11, 8, 8] | 28 | Y / 2 | [0,1,3 / 2,4,5] | `t2_c1 : ArmyAllocation` | agree |
| 2 | [7, 10, 7, 7, 9, 8] | 24 | Y / 2 | [0,1,2 / 3,4,5] | `t2_c2` | agree |
| 3 | [10, 9, 12, 9, 8, 8] | 28 | Y / 2 | [0,1,3 / 2,4,5] | `t2_c3` | agree |
| 4 | [6, 7, 6, 8, 6, 7] | 20 | Y / 2 | [0,1,5 / 2,3,4] | `t2_c4` | agree |
| 5 | [7, 7, 8, 8, 10, 8] | 24 | Y / 2 | [0,1,4 / 2,3,5] | `t2_c5` | agree |
| 6 | [11, 10, 8, 9, 9, 9] | 28 | Y / 2 | [0,2,3 / 1,4,5] | `t2_c6` | agree |
| 7 | [6, 6, 8, 6, 6, 8] | 20 | Y / 2 | [0,1,2 / 3,4,5] | `t2_c7` | agree |
| 8 | [7, 7, 10, 10, 7, 7] | 24 | Y / 2 | [0,1,2 / 3,4,5] | `t2_c8` | agree |
| 9 | [11, 8, 13, 8, 8, 8] | 28 | N / 1 | — (no triple) | `t2_c9 : ¬ ArmyAllocation` | agree |
| 10 | [10, 8, 10, 9, 11, 8] | 28 | Y / 2 | [0,1,2 / 3,4,5] | `t2_c10` | agree |
| 11 | [8, 8, 8, 8, 9, 7] | 24 | Y / 2 | [0,1,2 / 3,4,5] | `t2_c11` | agree |
| 12 | [8, 8, 7, 11, 7, 7] | 24 | N / 1 | — (no triple) | `t2_c12 : ¬ ArmyAllocation` | agree |
| 13 | [7, 7, 7, 7, 6, 6] | 20 | Y / 2 | [0,1,4 / 2,3,5] | `t2_c13` | agree |

**14 / 14 agree, kernel-checked.** The three no-instances left open in session 2 (cases 0, 9,
12) are now settled on the Lean model: `¬ ArmyAllocation`, so every allocation's optimum is
`≤ 1`. Session 2's sampled bijections reached 1, and a single strike line always kills one
enemy here (`Σ` of any group's three `≥ T`), so the exact optimum is 1. That matches Python's 1
on all 720 bijections of case 0 (session 2) and its game verdict on cases 9 and 12.

### Theorem 4 tier (`verify_featureless.py` C6 default: `T = 13`, yes and no, 3 allocations each)

Proof level (`CrossCheck.t4_yes13`, `t4_no13`, kernel-checked):

- `[4,4,4,4,5,5]`, `T = 13` (Python: yes, seating `[0,1,4 / 2,3,5]`): `ArmyAllocation`,
  `BattlePlay … αId` (Cor 4.1), `HpAllocation … 26` (Cor 4.2). All agree.
- `[4,4,4,4,4,6]`, `T = 13` (Python: no, no triple sums to 13): `¬ ArmyAllocation`,
  `¬ BattlePlay … αId`, `¬ HpAllocation … 26`. All agree. Python's `hp_relaxation` is 25 < 26,
  consistent with `¬ HpAllocation 26`.

Per allocation (runner `CrossCheckRun3.lean`). "Lean lower" is `valueG`, a genuine play.
"Lean upper" is `min(m, ⌊Σ nominal / T⌋)` from `gf_value_le`. Python's "best" is
`best_play_for_allocation` (its exact search).

| a | T | allocation (slot j gets type) | Python best | Lean lower | Σ nominal | Lean upper | Lean exact | verdict | ms |
|---|---|---|---|---|---|---|---|---|---|
| [4,4,4,4,5,5] | 13 | [0,1,2,3,4,5] | 2 | 1 | 26 | 2 | **2** (`t4_yes13_id`) | agree | 14173 |
| [4,4,4,4,5,5] | 13 | [–,2,1,–,3,0] | 1 | 1 | 16 | 1 | 1 | agree | 1919 |
| [4,4,4,4,5,5] | 13 | [5,0,1,4,–,3] | 1 | 1 | 22 | 1 | 1 | agree | 5487 |
| [4,4,4,4,4,6] | 13 | [0,1,2,3,4,5] | 1 | 1 | 26 | 2 | **1** (`t4_no13_id`) | agree | 14039 |
| [4,4,4,4,4,6] | 13 | [–,1,3,5,4,–] | 1 | 1 | 18 | 1 | 1 | agree | 1926 |
| [4,4,4,4,4,6] | 13 | [4,–,2,0,1,5] | 1 | 1 | 22 | 1 | 1 | agree | 5194 |

**6 / 6 agree, every value exact on the Lean side.** On four rows the executable lower bound
meets the proof-level upper bound. The two identity rows have a gap (the greedy line strikes
the highest-index enemy first and wastes a kill on the yes-instance, and Σ nominal = mT on the
no-instance). Corollary 4.1 closes both at proof level:

- `t4_yes13_id` shows a play destroys both enemies.
- `t4_no13_id` shows none does.

`battlePlay_congr` / `pyId6_norm` identify Python's identity list with `αId`. The runner takes
about 49 s. It also prints the axioms of `t2_c0`, `t2_c1`, `t4_yes13_id`, `t4_no13_id`,
`valueG_attained` and `gf_value_le`: only `propext`, `Classical.choice`, `Quot.sound`. In
particular there is no `Lean.ofReduceBool`, because the verdicts use kernel `decide`/`rfl`,
not `native_decide`.

No disagreement anywhere, so nothing to escalate about the paper or the scripts.

## Findings (session 3)

1. **The no-directions are geometry-free.** E.14, E.22 and Cor 4.2's no-direction are proven
   once for every layout of the stock-one family (`Fam.fam_no`, `ThmF.Fam.hp_no`). They use
   only the ledger, E.1 and the damage arithmetic. Lemma E.11's separation and E.12's
   `|S_g| ≤ 3` do **not** carry Theorem 2's equivalence. Separation serves the reading "the play
   is forced" (`Thm2.flower`), which the paper uses as intuition, not as a step of the proof.
2. **Which promise inequality is used where.** The counting argument uses only `2a_i < T` and
   `Σ a = mT`. The lower promise `T/4 < a_i` is used only to get `a_i ≥ 1`, which the model
   needs for `dmg ≥ 1`. The E.19 witness needs `a_i ≥ 1` and `2a_i < T`. E.21 needs positivity.
3. **E.19 is stronger than stated.** The simultaneous realization holds for **any** full
   injective allocation and **any** three-per-enemy seating, not just the lemma's.
4. **E.20 matches the paper's current wording.** Through the R9 order argument, a waiting blow
   meets the delayed DEFEND and does `damage 1 a_i (−1)`. That is at most nominal, with equality
   exactly when `a_i = 1`. "Strictly less" would be false at `a_i = 1`, and the Lean statement
   rules it out.
5. **Seat capacity ≤ 6** needs E.2 (pools 4..5, so a player stack never dies in round 1) plus a
   distinct-hexes invariant for living stacks. Neither is spelled out in Appendix E.
6. **Cor 4.2's objective.** `absorbed` is the sum over enemies of (initial pool − final pool),
   which equals Σ min(delivered, pool). The formal statement fixes this reading, and Python's
   `hp_relaxation` agrees with it on C6.
7. **`m = 0`.** Theorems 2 and 4 hold as equivalences for `m = 0` too (`THREE_PARTITION [] T`
   and `ArmyAllocation` both hold). The totality wrappers reroute only because the model
   requires `W > 0`.
8. **Session 2's open no-instances are closed.** Theorem 2 cases 0, 9, 12 are now
   kernel-checked `¬ ArmyAllocation`, without the 180-CPU-hour bijection sweep.

## Blockers and friction (session 3)

- No mathematical blocker. Every target closed inside its time box.
- One python patch used an empty `old` string and blew `Theorem2.lean` up. The file was
  rewritten, and patches now assert match counts.
- Decidability-instance mismatches after `simp only [sAttack]` blocked `rw`. The fix is to
  write successors as explicit `{ s with … }` literals and derive steps with
  `step_of_mem_succsAO`.
- `rename_i` picked wrong binders in `Step` cases. The fix is explicit `@constructor` patterns.
- `threePart` uses `⟨8 * g, 1⟩` with `g : ℕ` (a cast of the product), `G3P` uses
  `8 * (g : ℤ)`. The two agree definitionally only after `norm_num`, so the equality is proven
  for six-entry lists (`threePart_eq6`), which covers the whole tier.
- The interpreter again limits execution. The restricted search `valueR` on one C6 allocation
  ran over 10 minutes and was stopped. BFS at speed `4m + 8 = 16` over the 10 × 6 board
  dominates. The greedy line plus the proof-level bounds replaced it at about 49 s total.

## Totals (end of session 3)

- 25 modules + root, **7249** library lines (session 2: 4034). Also `CrossCheck.lean` and 5
  runners (about 500 lines).
- Theorems: **404** by `grep -cE '^(@\[[^]]*\] )?(private |protected )?theorem '` over
  `Homm3/`. The new modules contribute 169: ThreePartition 25, Accounting 30, Theorem2 33,
  Walk 4, Theorem4 59, LemmaE20 18. **0 `sorry`**, 0 axioms introduced.
- New module sizes (lines): ThreePartition 431, Accounting 508, Theorem2 515, Walk 45,
  Theorem4 991, LemmaE20 684.
- Wall clock: target 1 23 min, targets 2–3 core 12 min, E.20 / E.2 / capacity 12 min,
  target 4 about 35 min (including the stopped `valueR` run), write-up about 10 min. The Tier B
  estimate of 3–4 sessions landed in one session.

## What remains

- Tier B is complete: Theorems 2 and 4, Corollaries 4.1 and 4.2, E.11–E.22, all totality
  forms.
- Optional: the "play is forced" reading of E.11 as a statement about **every** optimal play
  (`flower` gives the per-position fact).
- Optional: a verified memo or prune for the executable layer, to run full per-allocation
  optima on C6/C9 instead of bound-sandwiching.
- **Theorem 3** (PLANAR-X3C gadgets, Appendix D) is the one headline result not formalized.

### Note on Theorem 3

- **Carries over as is:** the semantics, E.1, the ledger (`ledger`, `Ledger.dead` /
  `absorbed`) for any instance satisfying `AcctHyp`, the stock-one family pattern, and
  attack-only play with `Frozen`.
- **Partly reusable:** the reach apparatus (`reach_row`, `route`, the `Clear` invariant). The
  gadgets need walks in more general free regions, so a generic "free path of length ≤ s ⇒ in
  the BFS reach" lemma (a `HexGraph` extension) is worth writing first.
- **New work:** the gadget geometry (variable, clause and wire gadgets), their local
  containment lemmas, and the global layout.
- **Would a PLANAR-X3C variant with a given embedding help?** Yes, substantially. With the
  embedding as part of the input (PLANAR-X3C together with a rectilinear grid drawing of its
  incidence graph, which is what the paper's Lemma D.4 produces), the reduction becomes a direct
  placement of gadgets at given coordinates. The paper's source problem is PLANAR-X3C
  (Dyer–Frieze), not planar 3-SAT; an earlier draft of this note misnamed it. Nothing about planarity needs proving in Lean: no planar-graph
  or Tutte-embedding theory, only the finite geometry of the given drawing. Its NP-hardness
  would be taken as the source problem, as 3-PARTITION is here.
- **Estimate for Theorem 3 in that form:** 2–3 sessions. The gadget containment lemmas follow
  the E.11 `contain`/`flower` pattern. The "no-direction" should again reduce to accounting
  plus a per-gadget local argument.

## Commits (session 3)

- `c9fb09b` formal/lean: сессия 3, цель 4 — сверка яруса B (Теорема 2 14/14 в ядре, C6 Теоремы 4 6/6, значения точны)
- `fcccbe1` formal/lean: сессия 3, цель 2 (продолжение) — Лемма E.20 целиком, Лемма E.2 для семейства, различные клетки, ёмкость мест
- `ea92520` formal/lean: сессия 3, цели 2–3 — Теорема 4, E.15–E.19, E.21, E.22, следствия 4.1 и 4.2, тотальные формы
- `897f258` formal/lean: сессия 3, цель 1 — Теорема 2, E.11–E.14, тотальная редукция
- (this write-up: the commit that adds this section)

# Session 4 — Theorem 3 and Corollary 3.1 (2026-09-25, MSK)

Model: `claude-opus-5-5`. Base `aa19654`, branch `worktree-policy-wait-defend`, start 15:44.
Targets 1–4 are closed with **0 `sorry`**. Target 5 (Lemma D.4) is closed on the literal
corpus, and the universal lemma comes with a plan and an estimate. All new headline theorems
are in `Homm3/Axioms.lean`, and each prints only a subset of `propext`, `Classical.choice`,
`Quot.sound`. No `native_decide` anywhere; every concrete fact is `decide` / `decide +kernel` /
`rfl`.

## Design: Theorem 3 modulo the embedding

`X3CBoard` is an abstract board: dimensions, impassable hexes, deployment hexes `p e`, enemy
hexes `z g`, dockings `d g e`, regions `R e`, speed `σ`. `B.Inv P` states (I1)–(I4) as
hypotheses (15 fields), and every correctness statement is proved for **every** board that
satisfies them. Planarity never enters the formal problem. It enters the paper only through
Lemma D.4, which produces such a board. The boards the artifact actually builds are checked
against `Inv` in the kernel (targets 4 and 5).

`InvCore` is the part of `Inv` that the proof consumes (9 fields). `theorem3_core` and
`cor31_core` take `InvCore`, and `theorem3` / `cor31` are derived through `Inv.core`. See
Finding 1.

## Target 1 — `X3C`, the board, `G_3`, Lemma 3.2, Lemmas D.5 and D.6 (15:44–16:12, `sorry`: 0)

`Homm3/X3C.lean`, `Homm3/X3CBoard.lean`, first half of `Homm3/Theorem3.lean`.

- `X3C` has `q`, a list `C` of members, and `WF` (every member is a 3-subset of `[0, 3q)`).
  `ExactCover` asks for pairwise disjoint members covering `[0, 3q)`, and `card_cover` shows
  such a cover has `q` members.
- **Lemma 3.2** (`lemma32`) holds for every `μ ∈ (0, 1)` in `ℚ` with `D(c) = max(1, ⌊μc⌋)`,
  as an `↔` in the paper's form. Its abstract core `resource` uses only `b ≤ c` and
  `b = c → c = 1`. `blow_resource` applies it to the engine blow at every `Δ < 0`. That covers
  both published branches (`μ = 0.35` undefended, `0.3` defended at `def 27`) and the
  historical constants (`def 41`: `0.3` on both).
- `G3 hpP defQ P B` is `G_3(X, C)` with the player's hit points and the enemy's defence as
  parameters. `G3pub = G3 4 27` is the paper's instance; `verify_x3c.py` uses `hp 5`, `def 41`.
- **Lemma D.5** (`lemmaD5`) needs `hp(P) ≥ 2`. No player creature dies, and every stack keeps
  its count all round.
- **Lemma D.6** (`lemmaD6`) needs `def(Q) ≥ 2` and no geometry. It gives `t ≤ q`, and at
  `t = q` every slot holds one creature, strikes a dead enemy, and every dead enemy has exactly
  three strikers. It uses the **generalized ledger** `LedgerB`, session 3's ledger with a
  predicate on the *actual* blow and an attack hypothesis that may read the current ledger.

## Target 2 — Lemmas D.1, D.7–D.9, `theorem3`, total form, `cor31` (15:44–16:20, `sorry`: 0)

- `mem_reach_of_rtg`: a walk inside a finite free set `A` from the mover's hex ends in the
  BFS reach within `|A|` layers. This is the generic "free path ⇒ in the reach" lemma that
  session 3's note asked for.
- **Lemma D.1** (`lemmaD1`): while every `E_S` with `S ∋ e` lives and `R_e` holds no other
  living stack, slot `e` strikes exactly the `E_S` with `S ∋ e`, and only from `d_S^e`.
  Its confinement half (`reach_sub_region`) needs neither the "alone" hypothesis nor (I4).
- **Lemma D.7** (`confinedLedger`, `lemmaD7`) holds for **every** allocation with at most one
  creature per slot. In every position of round 1, every strike so far was by slot `e` on an
  `E_S` with `S ∋ e`. While slot `e` has not acted, every `E_S` with `S ∋ e` is alive. The
  induction runs along the play. A dead `E_S` has at least 3 recorded strikers, all in `S` by
  the invariant, hence exactly the three slots of `S`, so slot `e ∈ S` has already acted.
- **Lemma D.8** (`lemmaD8`) goes through a general witness run `witness`. Slots strike their
  planned targets from their dockings in the `NORMAL` phase, for any plan of counts and
  targets whose blows add up. The negative control reuses it.
- **Lemma D.9** (`lemmaD9`) and `winning_unique`: every winning allocation is all-ones.
- Headline statements (`Homm3/Theorem3.lean`):

```lean
theorem theorem3 (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.Inv P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) :
    P.ExactCover ↔ ArmyAllocation (G3 hpP defQ P B)

theorem theorem3_pub (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.Inv P) :
    P.ExactCover ↔ ArmyAllocation (G3pub P B)

theorem cor31 (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.Inv P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ) :
    P.ExactCover ↔ ThmF.BattlePlay (G3 hpP defQ P B) α1
```

- Total form (`Homm3/BoardCheck.lean`). A board is shipped as `BoardData`: a big number
  `lab` with one label byte per hex, and a big number `dist` with a 16-bit BFS certificate per
  hex. `check` is a Bool checker, local per hex, and **`check_sound`** proves
  `D.check q CL = true → D.toBoard.Inv (toX3C q CL)`. The source problem of the total map is
  "`X3C` with a certified board", which is what Lemma D.4 outputs:

```lean
def X3CB (q : ℕ) (CL : List (List ℕ)) (D : BoardData) : Prop :=
  D.check q CL = true ∧ (toX3C q CL).ExactCover

theorem theorem3_total (q : ℕ) (CL : List (List ℕ)) (D : BoardData) :
    X3CB q CL D ↔ ArmyAllocation (reduction3 q CL D)

theorem cor31_total (q : ℕ) (CL : List (List ℕ)) (D : BoardData) :
    X3CB q CL D ↔ ThmF.BattlePlay (reduction31 q CL D).1 (reduction31 q CL D).2
```

  `reduction3` sends a passing board to `G3pub`, `q = 0` to the fixed 5 × 5 yes-board `D1`
  (its check is `decide +kernel`), and everything else to `Corridor.Gno`.
  `exactCover_iff_check` decides exact cover by `coverCheck`.

## Target 3 — machine facts of Appendix D (16:29–16:38, `sorry`: 0)

`Homm3/Gadgets.lean`, all `decide +kernel` or short proofs over it.

- `adj_shift`: shifts by `(a, 2b)` preserve adjacency (the parity step of D.4 step 5).
- **Lemma D.2** (`lemmaD2`): for **every** hex, of the 20 triples of its neighbours exactly
  the two alternating ones, `{0, 3, 5}` and `{1, 2, 4}`, are pairwise non-adjacent. The proof
  is `decide` on the two base parities plus translation. `enemy_gadget`: the gadget's three
  dockings are the triple `{1, 2, 4}`.
- **Lemma D.3** (`lemmaD3`): the four 9 × 9 adapters of Appendix C, transcribed from
  `main.md` by `tools/appendix_c.py` (which also asserts they equal `verify_x3c.ADAPTERS`),
  pass `adapterOK`. That checks the three arms from the used ports, their disjointness and
  non-touching, the unused port closed, the free hexes exactly `Z` and the arms, and the arms
  matched to the dockings in cyclic order. The checker has teeth: a wrong unused port,
  a picture that is not the arms', and a fourth arm are rejected.
- Step 4: `adj_linf` (adjacency ⇒ `L∞ = 1`), `sep_ineq` and `sep_constants`
  (`λ − 2ρ = 20 − 8 = 12 ≥ 2`), `square_in_hex` (the square grid lies inside hex adjacency in
  both parities), `old_draft_touch` (at the earlier draft's `λ = 9`, hexes of two features can touch), `offset_constants`
  (`ω = 6` works, `ω = 2` does not).

## Target 4 — cross-check against `verify_x3c.py` (16:12–16:29, fast path 16:42–16:49, `sorry`: 0)

`tools/export_x3c.py` imports `verify_x3c` read-only and replays its default suite bit for bit.
Suite [4] is seed 101 on the q = 1 family. Suite [5] is seed 202 on planted(2, 2, 10, seed 3)
+ random(2, 3, 10, seed 5) + random(2, 4, 10, seed 41). The negative control's board is
rebuilt the way `check_negative_control` builds it. For each board the tool records Python's
verdicts (`x3c_is_yes`, and `winning_allocations` at `hp 5`, `def 41`, policy `hold`) and
writes `CrossCheckX3CData.lean`. Python run: 10.4 s.

`CrossCheckX3C.lean`, per board, all in the kernel:

- `ckNN : bNN.check qNN CNN = true` by `decide +kernel`, hence (I1)–(I4) by `check_sound`.
- `cvNN : coverCheck qNN CNN = true/false` by `decide +kernel`.
- `yesNN : YesV …` or `noNN : NoV …` by `yes_of` / `no_of`. That covers (I1)–(I4), the X3C
  answer, and the game answer **through `theorem3`** at `hp 5, def 41` and at `G3pub`
  (`hp 4, def 27`). It also covers Corollary 3.1 (`BATTLE-PLAY` with all-ones) and, on yes-boards,
  `winning_unique`. No game tree is searched in Lean.
- `negctl`: at `def(Q) = att(P) = 1` the no-instance `{{0,1,2}, {0,1,3}}` becomes a game
  yes-instance, while at `def 41` it stays a no. The witness is slots 2 and 3 with three
  creatures each, each killing an enemy alone (`D(3) = 3`, Lemma 3.2 broken), through
  `T3.witness`. This is Python's winner `[0,0,3,3,0,0]`, one of its 38.

| Board | q | \|C\| | Size | Free | (I1)–(I4) in the kernel | Python: X3C / game (winners) | Lean via `theorem3` (hp 5/def 41 and hp 4/def 27) | Time, s |
|---|---|---|---|---|---|---|---|---|
| `b00` | 1 | 1 | 32x32 | 29 | ✓ | Y / Y (1) | yes, all-ones unique | 0.7 |
| `b01` | 2 | 4 | 48x48 | 178 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b02` | 2 | 4 | 48x48 | 180 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b03` | 2 | 4 | 48x48 | 173 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b04` | 2 | 4 | 48x48 | 161 | ✓ | Y / Y (1) | yes, all-ones unique | 1.8 |
| `b05` | 2 | 4 | 48x48 | 201 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b06` | 2 | 4 | 48x48 | 145 | ✓ | Y / Y (1) | yes, all-ones unique | 1.7 |
| `b07` | 2 | 4 | 48x48 | 198 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b08` | 2 | 4 | 48x48 | 205 | ✓ | Y / Y (1) | yes, all-ones unique | 2.0 |
| `b09` | 2 | 4 | 48x48 | 208 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b10` | 2 | 4 | 48x48 | 244 | ✓ | Y / Y (1) | yes, all-ones unique | 2.1 |
| `b11` | 2 | 3 | 40x40 | 197 | ✓ | Y / Y (1) | yes, all-ones unique | 1.6 |
| `b12` | 2 | 3 | 40x40 | 170 | ✓ | N / N (0) | no | 1.3 |
| `b13` | 2 | 3 | 40x40 | 157 | ✓ | N / N (0) | no | 1.4 |
| `b14` | 2 | 3 | 40x40 | 108 | ✓ | N / N (0) | no | 1.1 |
| `b15` | 2 | 3 | 40x40 | 163 | ✓ | N / N (0) | no | 1.4 |
| `b16` | 2 | 3 | 40x40 | 192 | ✓ | Y / Y (1) | yes, all-ones unique | 1.5 |
| `b17` | 2 | 3 | 40x40 | 170 | ✓ | N / N (0) | no | 1.3 |
| `b18` | 2 | 3 | 40x40 | 140 | ✓ | N / N (0) | no | 1.3 |
| `b19` | 2 | 3 | 40x40 | 197 | ✓ | N / N (0) | no | 1.6 |
| `b20` | 2 | 3 | 40x40 | 111 | ✓ | N / N (0) | no | 1.1 |
| `b21` | 2 | 4 | 48x48 | 189 | ✓ | Y / Y (1) | yes, all-ones unique | 1.9 |
| `b22` | 2 | 4 | 48x48 | 160 | ✓ | Y / Y (1) | yes, all-ones unique | 1.8 |
| `b23` | 2 | 4 | 48x48 | 198 | ✓ | N / N (0) | no | 1.9 |
| `b24` | 2 | 4 | 48x48 | 207 | ✓ | N / N (0) | no | 1.9 |
| `b25` | 2 | 4 | 48x48 | 157 | ✓ | N / N (0) | no | 1.7 |
| `b26` | 2 | 4 | 48x48 | 144 | ✓ | N / N (0) | no | 1.8 |
| `b27` | 2 | 4 | 48x48 | 193 | ✓ | N / N (0) | no | 2.0 |
| `b28` | 2 | 4 | 48x48 | 138 | ✓ | Y / Y (1) | yes, all-ones unique | 1.7 |
| `b29` | 2 | 4 | 48x48 | 166 | ✓ | N / N (0) | no | 1.8 |
| `b30` | 2 | 4 | 48x48 | 195 | ✓ | Y / Y (1) | yes, all-ones unique | 1.8 |
| `bNeg` | 2 | 2 | 40x40 | 97 | ✓ | N / N; at def 1: Y (38 winners) | no (def 41); **yes** at def 1 (`negctl`) | 1.1 |

Totals: 31 boards, 17 yes and 14 no. All 31 pass (I1)–(I4) in the kernel, and all 31 Lean
verdicts agree with Python at both constant sets. On the 17 yes-boards, Python's single
winner is the all-ones vector, which `winning_unique` proves is the only one. The whole
library builds in 45 s after the fast path (84 s before). Times are per-board differences of
the profiler's running totals, before the fast path.

## Target 5 (stretch) — Lemma D.4 (16:49–17:18, literal part closed; universal lemma: plan)

### The literal boards (`CrossCheckLemma*.lean`, `sorry`: 0)

`tools/export_lemma.py` runs `embed_lemma.build_board_lemma` over `verify_embedding.corpus()`
(61 families, every published suite, deduplicated) with read-only imports. 44 families yield
a board and 17 yield `G_no`. All 17 are "an element lies in no set", and each is an X3C
no-instance by the exporter's assertion. Every board also passes `verify_x3c.check_geometry`
on the Python side. Each board is shipped with `BoardData.ofPacked` and checked in the kernel,
with the same `ck` / `cv` / `yes` / `no` package as target 4.

| Board | Family | q | \|C\| | Size | Free | (I1)–(I4) in the kernel | Python: X3C | Lean via `theorem3` (both constant sets) | Time, s |
|---|---|---|---|---|---|---|---|---|---|
| `l00` | 0 | 1 | 1 | 53x73 | 169 | ✓ | Y | yes, all-ones unique | 1.1 |
| `l01` | 1 | 2 | 4 | 93x313 | 1152 | ✓ | Y | yes, all-ones unique | 9.4 |
| `l02` | 2 | 2 | 4 | 113x313 | 1532 | ✓ | Y | yes, all-ones unique | 12.3 |
| `l03` | 3 | 2 | 4 | 73x313 | 992 | ✓ | Y | yes, all-ones unique | 7.9 |
| `l04` | 4 | 2 | 4 | 153x313 | 1654 | ✓ | Y | yes, all-ones unique | 16.4 |
| `l05` | 5 | 2 | 4 | 113x313 | 1612 | ✓ | Y | yes, all-ones unique | 13.2 |
| `l06` | 6 | 2 | 4 | 73x313 | 1132 | ✓ | Y | yes, all-ones unique | 8.8 |
| `l07` | 7 | 2 | 4 | 73x313 | 1152 | ✓ | Y | yes, all-ones unique | 8.5 |
| `l08` | 8 | 2 | 4 | 93x313 | 1252 | ✓ | Y | yes, all-ones unique | 10.1 |
| `l09` | 9 | 2 | 4 | 73x313 | 992 | ✓ | Y | yes, all-ones unique | 7.9 |
| `l10` | 10 | 2 | 4 | 153x313 | 1734 | ✓ | Y | yes, all-ones unique | 17.4 |
| `l11` | 11 | 2 | 3 | 133x233 | 1154 | ✓ | Y | yes, all-ones unique | 10.0 |
| `l12` | 12 | 2 | 3 | 133x233 | 994 | ✓ | N | no | 9.0 |
| `l13` | 16 | 2 | 3 | 133x233 | 1094 | ✓ | Y | yes, all-ones unique | 9.0 |
| `l14` | 17 | 2 | 3 | 133x233 | 1034 | ✓ | N | no | 9.0 |
| `l15` | 20 | 2 | 3 | 73x233 | 834 | ✓ | N | no | 6.0 |
| `l16` | 21 | 2 | 4 | 73x313 | 1052 | ✓ | Y | yes, all-ones unique | 8.0 |
| `l17` | 22 | 2 | 4 | 93x313 | 1192 | ✓ | Y | yes, all-ones unique | 10.0 |
| `l18` | 23 | 2 | 4 | 93x313 | 1192 | ✓ | N | no | 10.0 |
| `l19` | 24 | 2 | 4 | 133x313 | 1514 | ✓ | N | no | 14.0 |
| `l20` | 26 | 2 | 4 | 93x313 | 1232 | ✓ | N | no | 10.0 |
| `l21` | 27 | 2 | 4 | 73x313 | 1112 | ✓ | N | no | 9.0 |
| `l22` | 28 | 2 | 4 | 113x313 | 1492 | ✓ | Y | yes, all-ones unique | 12.0 |
| `l23` | 29 | 2 | 4 | 93x313 | 1292 | ✓ | N | no | 10.0 |
| `l24` | 30 | 2 | 4 | 93x313 | 1252 | ✓ | Y | yes, all-ones unique | 10.0 |
| `l25` | 31 | 3 | 5 | 173x393 | 2621 | ✓ | Y | yes, all-ones unique | 25.0 |
| `l26` | 32 | 3 | 5 | 173x393 | 2219 | ✓ | Y | yes, all-ones unique | 24.0 |
| `l27` | 33 | 3 | 5 | 253x393 | 3599 | ✓ | Y | yes, all-ones unique | 39.0 |
| `l28` | 34 | 3 | 5 | 213x393 | 2739 | ✓ | Y | yes, all-ones unique | 30.0 |
| `l29` | 35 | 3 | 5 | 173x393 | 2639 | ✓ | Y | yes, all-ones unique | 29.0 |
| `l30` | 36 | 3 | 5 | 73x393 | 1299 | ✓ | Y | yes, all-ones unique | 11.0 |
| `l31` | 37 | 3 | 5 | 213x393 | 2839 | ✓ | Y | yes, all-ones unique | 31.0 |
| `l32` | 38 | 3 | 5 | 153x393 | 2059 | ✓ | Y | yes, all-ones unique | 22.0 |
| `l33` | 39 | 3 | 5 | 133x393 | 1659 | ✓ | Y | yes, all-ones unique | 18.0 |
| `l34` | 40 | 3 | 5 | 133x393 | 1639 | ✓ | Y | yes, all-ones unique | 20.0 |
| `l35` | 44 | 3 | 6 | 133x473 | 2457 | ✓ | N | no | 25.0 |
| `l36` | 47 | 3 | 6 | 193x473 | 3017 | ✓ | N | no | 33.0 |
| `l37` | 48 | 3 | 6 | 113x473 | 2179 | ✓ | N | no | 23.0 |
| `l38` | 50 | 3 | 6 | 133x473 | 2637 | ✓ | N | no | 26.0 |
| `l39` | 51 | 4 | 6 | 333x393 | 3190 | ✓ | Y | yes, all-ones unique | 44.0 |
| `l40` | 52 | 4 | 6 | 233x393 | 1728 | ✓ | Y | yes, all-ones unique | 25.0 |
| `l41` | 53 | 4 | 6 | 213x473 | 3388 | ✓ | Y | yes, all-ones unique | 40.0 |
| `l42` | 54 | 4 | 6 | 313x393 | 3650 | ✓ | Y | yes, all-ones unique | 46.0 |
| `l43` | 55 | 4 | 6 | 233x473 | 2286 | ✓ | Y | yes, all-ones unique | 33.0 |

Totals: 44 boards, 32 yes and 12 no, with q from 1 to 4 and sizes up to 333 × 393 (130,869 hexes,
up to 3650 free). All 44 pass (I1)–(I4) in the kernel, and every verdict agrees with
`x3c_is_yes`. The 12 no-boards are ordinary boards whose game answer is no, which is the "only
when, not exactly when" of `main.md:1420–1424`. Times are per-board differences of the
profiler's running totals in a single-module build (803 s). The cost is about linear in the
board area, because the checker visits every hex. Split into four modules
(`CrossCheckLemmaA`–`D`, balanced by area), `lake build CrossCheckLemma` takes 351 s wall. The
Python export takes 2.3 s.

### The universal lemma: plan and estimate

What is formalized already is everything D.4 has to deliver *to* Theorem 3. That means the
target (`InvCore`, with `Inv` as the paper's form), a sound per-board certificate
(`check_sound`), and the local geometry (Lemma D.2, the adapters of Lemma D.3,
`adj_shift`, the step-4 separation facts). What remains is the claim that the algorithm
succeeds on every planar instance. A route in the spirit of session 3's note:

1. **Take the drawing as input.** Use PLANAR-X3C together with an orthogonal grid drawing of
   `G'` (degree ≤ 3, vertices at distinct grid points, edges as axis-parallel polylines,
   non-incident features disjoint). This is the output of steps 1–3 (`main.md:1445–1498`). The
   drawing literature and planarity testing stay outside Lean, as NP-hardness of the source
   problem does. About ½ session: the structure, its validity predicate, and a Bool checker
   with a soundness proof, reusing the `BoardData` pattern.
2. **Scaling and features** (step 4, `main.md:1499`). `φ(i, j) = (λi + ω, λj + ω)`, boxes of radius `ρ`,
   corridor hexes, and the owner map as a function from hexes. The separation lemma (SEP′)
   says non-incident features are at `L∞ ≥ λ − 2ρ = 12`, hence non-adjacent (`adj_linf` and
   `sep_ineq` are done). About ½–1 session. The work is the case analysis over the three
   feature classes (box/box, box/corridor, corridor/corridor).
3. **Boxes** (step 5, `main.md:1542`). Set boxes use the adapters (`lemmaD3`, translated by `adj_shift`, with
   even rows guaranteed by even `λ` and `ω`). Element boxes are pluses, plus the stub, where
   only `p_e ∈ R_e` is needed (Finding 6). About ½ session.
4. **(I2)–(I4) globally** (step 6, `main.md:1581–1593`). Regions are unions of `e`'s pluses, corridors and arms. They are
   closed (step 2 and the adapters), connected (a path along the drawing's path for `e`),
   and their enemy-adjacent hexes are the dockings. (I4) is immediate since `σ` is the hex
   count. Polynomial size follows from the drawing's grid bounds. About ½–1 session.

**Estimate: 2–3 sessions** for D.4 with the drawing as input, which matches session 3's
estimate. The literal check above de-risks it: the construction is known to meet
`InvCore` (in fact `Inv`) on every board of the corpus, so the proof has no hidden
counterexample to find.

## Findings (session 4)

1. **The proof consumes only part of (I1)–(I4)** (`main.md:562–570`, "Four invariants carry
   the whole correctness argument"). `theorem3_core` needs only `InvCore`. It drops (I1)
   entirely, the "adjacent to `z_S` alone" clause of (I3), the covering half of (I2) (every
   free non-enemy hex lies in some region), and the openness and injectivity of the enemy
   hexes. (I1) is not wrong. It is a consequence of the geometry, as `main.md:572` and
   `main.md:1371` say. The formal D.7 counts strikers instead of hexes, which is the route
   `main.md:1682–1687` describes, so the three-free-neighbours fact never enters.
2. **Lemma D.7 is stronger than stated** (`main.md:1642`, "In the situation of Lemma D.6 with
   `t = q`"). It holds for **every** allocation with at most one creature per slot, in every
   position of round 1. The formal proof reads only the ledger of the current position: a dead
   `E_S` has at least 3 recorded strikers so far. The paper's proof (`main.md:1658–1660`)
   appeals to "struck by exactly three stacks over the round", an end-of-round fact of D.6
   used mid-round. The formal induction does not need it.
3. **Theorem 3 needs only `hp(P) ≥ 1`** (`main.md:1322`, `hp = 4`; `main.md:1600–1609`).
   Lemma D.5 needs `hp ≥ 2` and is proved (`lemmaD5`), but no correctness proof uses it, as
   `main.md:1682` already says. So the paper's `hp 4` and the script's `hp 5` are both covered,
   and so is `hp 1`.
4. **Corollary 3.1 needs no part of Lemma 3.2** (`main.md:1722–1731`). `cor31` holds for
   every `def(Q) ≥ att(P)`, including the negative control's `def = att = 1`, under which
   Theorem 3 itself fails (`negctl`). The paper says the corollary avoids the lemma's equality
   case (`main.md:1729–1730`). In fact, with one creature per slot, every blow at `Δ ≤ 0` is
   exactly 1 (`damage_le_one_eq`), and nothing else is needed.
5. **Confirmation, not a gap: any `def(Q) > att(P)` works** (`main.md:1336–1345`).
   `theorem3` assumes `2 ≤ defQ`. `blow_resource` covers every `Δ < 0` on both branches, so the
   published (`0.35` / `0.3`) and historical (`0.3` / `0.3`) arithmetic fall under one lemma.
6. **The deployment stub is not used by correctness** (`main.md:1559–1579`). Theorem 3 needs
   only `p_e ∈ R_e`. The stub's leaf property matters only to D.4's own bookkeeping, where
   it shows that the stub creates no new adjacency.
7. **The constants gap is documented** (`main.md:842`, `main.md:1760`). `verify_x3c.py`
   defaults to `hp 5`, `def 41`, policy `hold`, and the paper publishes `hp 4`, `def 27`. The
   Lean verdicts on all 31 boards hold at both constant sets, and they quantify over **all**
   plays under `(‡)` (WAIT, DEFEND, moves), which is stronger than the script's attack-only
   search. Every number agrees.
8. **Appendix C is exactly `verify_x3c.ADAPTERS`** (`main.md:1233`). `tools/appendix_c.py`
   parses the four printed pictures and asserts equality before emitting the Lean literals.
9. **Lemma D.4's literal boards get full game verdicts** (`main.md:1752–1765`). The artifact
   plays the game end-to-end only on the smallest lemma boards, and in the default run that
   means 3 families. Here all 44 boards that `build_board_lemma` builds from the 61-family
   corpus pass (I1)–(I4) in the kernel. Each gets its game verdict through `theorem3` at both
   constant sets, with Corollary 3.1 and all-ones uniqueness on the yes-boards. The other 17
   families go to `G_no`, all for "an element lies in no set", and all are X3C no-instances.

## Blockers and friction (session 4)

- No mathematical blocker. Targets 1–4 closed inside their time boxes.
- The worktree guard rejects compound shell commands (heredocs with `cd`, `time VAR=…`). Files
  are written with the Write tool and run through small wrapper scripts.
- `Decidable` synthesis fails on `∀ … , (… ↔ (∧) ∨ (∧))` under bounded quantifiers. The fix
  for Lemma D.2 is an explicit predicate (`Indep`) with its own instance and a split of the
  base case by row parity.
- `theorem3` inferred the implicit `defQ` wrongly through `Inv.core`. It is now passed
  explicitly.
- The negative-control board first came out with `def 41` baked in, because
  `verify_x3c.build_instance` fixes creature types at build time. `export_x3c.py` now builds
  it under `ENEMY_DEF = PLAYER_ATT`, as `check_negative_control` does, and asserts that the
  board itself does not depend on the constant.
- The `profiler` "cumulative" times are not wall-clock under async elaboration, so the
  per-board times below are the per-declaration "type checking took" lines.
- The lemma boards run up to 131k cells. Dense literals would be about 1 MB per board. The
  packed format (`ofPacked`, one 44-bit record per free cell, decoded by the kernel with
  logarithmic recursion depth) and the checker's skip of impassable cells by one label byte
  (`labIdx`) make them feasible. The same fast path cut the 32-board cross-check from 84 s
  to 45 s.

## Totals (end of session 4)

- 30 modules + root, **9757** library lines (session 3: 7249). There are also
  `CrossCheckX3C.lean`, `CrossCheckLemma*.lean` (5 files) and generated data (about 0.3 MB and
  0.85 MB), plus 3 tools in `tools/` (about 380 lines).
- Theorems: **541** by `grep -cE '^(@\[[^]]*\] )?(private |protected )?theorem '` over
  `Homm3/` (session 3: 404). New modules: X3C 20, X3CBoard 29, Theorem3 37,
  BoardCheck 30, Gadgets 21. **0 `sorry`**, 0 axioms introduced, no `native_decide`.
- New module sizes (lines): X3C 214, X3CBoard 409, Theorem3 897,
  BoardCheck 635, Gadgets 312.
- Wall clock: targets 1–2 28 min (15:44–16:12), total form and base of target 4 8 min, target
  4 cross-check 9 min, target 3 9 min, `InvCore` 4 min, checker fast path 7 min, target 5
  29 min (16:49–17:18, of which about 20 min kernel builds), write-up about 15 min.

## What remains

- **Lemma D.4, universal form:** the plan above, 2–3 sessions.
- Optional: Lemma D.5's "every stack gets its action" as a statement about the R9 order. The
  formal D.5 gives counts, and the order part is not needed by any proof.
- Optional: the `G_no` branch of `build_board_lemma` in Lean. `reduction3` already sends
  every failing input to `Corridor.Gno`, so a Lean mirror of step 0 (`|X| mod 3`, `|C| < q`,
  an uncovered element) would make the total map's no-branch match the paper's word for word.
- With this session every headline result of the paper is formalized. Theorem 3 holds modulo
  Lemma D.4, which is checked on the whole published corpus.

## Commits (session 4)

- `3f69848` formal/lean: сессия 4 — проход по докстрингам и Axioms.lean (exactCover_iff_check, yes_of, no_of)
- `ea01a14` formal/lean: сессия 4, цель 5 — Лемма D.4 на всём корпусе: 44 буквальные доски в ядре, ofPacked, export_lemma.py
- `43c5adf` formal/lean: сессия 4, цель 4 — быстрый путь чекера (labIdx), YesV/NoV в библиотеке, 84 → 45 c
- `8d813db` formal/lean: сессия 4 — InvCore: часть (I1)–(I4), которую потребляет доказательство; theorem3_core, cor31_core
- `5d8032e` formal/lean: сессия 4, цель 3 — Лемма D.2, Лемма D.3 (четыре адаптера), факты шага 4
- `3e8a24b` formal/lean: сессия 4, цель 4 — сверка с verify_x3c.py: 31 доска + негативный контроль в ядре
- `10fb472` formal/lean: сессия 4, цели 2 и 4 (основа) — BoardData, check_sound, доска D1, theorem3_total, cor31_total
- `399bac4` formal/lean: сессия 4, цели 1–2 — Теорема 3 по модулю вложения, Лемма 3.2, D.1, D.5–D.9, theorem3, cor31
- (this write-up: the commit that adds this section)

# Session 5 — Lemma D.4, universal, with the drawing on the input (2026-09-28, MSK)

Model: `claude-opus-5-5`. Base `cf488bd`, branch `worktree-policy-wait-defend`, start about 22:55.
Targets 1–5 are closed with **0 `sorry`**, and the stretch target 6 is closed for steps 0 and 1
(sizes). Lemma D.4 now holds in Lean for **every** valid orthogonal drawing of `G'`: the board that
steps 4–6 build satisfies all of (I1)–(I4), and Theorem 3 holds with the drawing on the input and
no embedding hypothesis left. New headline theorems are in `Homm3/Axioms.lean`; each prints a
subset of `propext`, `Classical.choice`, `Quot.sound`. No `native_decide`.

## Design: the drawing is input

Planarity testing, the rotation-preserving degree reduction (its embedding half), the packing of
components and the Tamassia–Tollis drawing theorem stay citations, as the NP-hardness of the
source problem does. Lean proves steps 4–6 for any drawing that satisfies a validity predicate.

- `OrthoDrawing` (`Homm3/Embed.lean`): vertex kinds of `G'` (`.set g`, `.elem e i` for
  `v_e^{i+1}`), vertex grid points, edges `u → v` with the source an element-path vertex (the
  orientation `embed_lemma.py` uses), each route a list of grid points in unit steps, and the grid
  bounding box `gw × gh`.
- `OrthoDrawing.Valid P` (22 fields):
  - `G'` from step 1: `P.WF`; kinds without repeats and in range; one set vertex per member;
    `v_e^1` present for every `e < 3q`; `elem e (i+1)` has a path edge from `elem e i`; every
    edge leaves an element vertex of some `e` and ends at an element vertex of the same `e` or at
    the set vertex of a member containing `e`; at a set vertex the incoming edges have distinct
    elements, and every element of the member has one.
  - (D1): distinct vertex points.
  - (D2): each route is a grid path of unit steps from `pos u` to `pos v` without repeated points.
    Each (vertex, direction) pair is used by at most one route.
  - (D3): a route meets a vertex point only at its own ends, and two routes share only the
    point of a common end.
  - (D4), made explicit: every point lies in `[0, gw) × [0, gh)`.

  The formulations follow `main.md:1481–1487` and `planar_embed.validate_drawing`.
  Findings 1 and 6 say what is implicit and what is unused.
- `build P Dr : X3CBoard`: steps 4–6 literally. `φ(i, j) = (20i + 6, 20j + 6)` (the box starts at
  the origin). The corridor of an edge is its scaled route at parameters `5 ≤ s ≤ 20k − 5`
  (`corr_iff`: exactly the route hexes at `L∞ > ρ` from both end images). A set box holds the
  Lemma D.3 adapter for its missing direction, each arm owned by the element of the edge at its
  port. An element box holds the plus, the centre and runs of length `ρ` to the used ports. The
  stub sits at `v_e^1` in the first unused direction of right, down, left, up. `z_g` is the set
  box's centre, `d_g^e` the last cell of `e`'s arm. `R_e` is the union of these features, every
  other hex is impassable, and `σ` is the hex count.

```lean
theorem lemmaD4 {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) : (build P Dr).Inv P

theorem theorem3_drawing {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) :
    P.ExactCover ↔ ArmyAllocation (G3pub P (build P Dr))

theorem theorem3_drawing' {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) :
    P.ExactCover ↔ ArmyAllocation (G3 hpP defQ P (build P Dr))

theorem cor31_drawing {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) :
    P.ExactCover ↔ ThmF.BattlePlay (G3pub P (build P Dr)) T3.α1

theorem build_size (P : X3C) (Dr : OrthoDrawing) :
    (build P Dr).width = 20 * Dr.gw - 7 ∧ (build P Dr).height = 20 * Dr.gh - 7 ∧
    (build P Dr).σ = (build P Dr).width * (build P Dr).height ∧
    (build P Dr).σ ≤ 400 * (Dr.gw * Dr.gh)

-- Homm3/EmbedCheck.lean
theorem OrthoDrawing.check_sound {q : ℕ} {CL : List (List ℕ)} (hc : Dr.check q CL = true) :
    Dr.Valid (toX3C q CL)

def X3CD (q : ℕ) (CL : List (List ℕ)) (Dr : OrthoDrawing) : Prop :=
  Dr.check q CL = true ∧ (toX3C q CL).ExactCover

theorem theorem3_drawing_total (q : ℕ) (CL : List (List ℕ)) (Dr : OrthoDrawing) :
    X3CD q CL Dr ↔ ArmyAllocation (reductionD q CL Dr)
```

`lemmaD4` gives the full `Inv`, all 15 fields, not only `InvCore`. `reductionD` sends a passing
drawing to `G3pub` on `build`, `q = 0` to the fixed yes-board `D1`, and anything else to
`Corridor.Gno`, as `reduction3` does. Unlike `theorem3_total`, its source problem carries a
drawing instead of a board, so nothing about (I1)–(I4) is assumed.

## Target 2 — step 4: scaling and separation (`Homm3/EmbedGeom.lean`, `sorry`: 0)

- (SEP) is proved **per unit segment**, not per feature. `sep_pt` says a point of a scaled unit
  segment is `≥ 20` from the image of any grid point other than the segment's ends. `sep_seg`
  says points of two scaled unit segments without a common end are `≥ 20` apart. `sep_vv` says
  distinct grid points map `≥ 20` apart. Each is one `omega` call per pair of directions (16
  cases).
- `sep_rays` covers two runs from one centre in different directions at parameters `≥ 5`: they
  are `≥ 5` apart. This is the paper's `max(t, t′)` or `t + t′` (`main.md:1532–1541`).
- `box_ray`: a hex of a radius-4 box within `L∞ 1` of a run point at parameter `≥ 5` has
  coordinate exactly `4` along the run.
- The route layer is `DEdge.pt s` for `s ∈ [0, 20k]`, with `pt_seg`, `pt_first`, `pt_last`,
  `pt_adj` (consecutive points adjacent, through `square_in_hex`), `near_u`/`near_v` (a segment
  touching an end's point is the first or last one, using simplicity), `linf_u`/`linf_v`, and
  `corr_iff`.
- Adapter facts in the kernel, for each missing direction: `arms_ports`, `arms_head`,
  `arms_chain`, `arms_cells`, `arms_zadj`, `arms_last`, `arms_docks`, `arms_apart`, and
  `arms_side`. The last one says a cell on side `p` of the box belongs to the arm of port `p`
  (Finding 2).

## Targets 3–4 — steps 5–6: boxes, regions, (I1)–(I4) (`Homm3/Embed.lean`, `sorry`: 0)

- **Separation of regions** (`prox`): hexes of `R_e` and `R_{e'}` that coincide or are adjacent
  have `e = e'`. The proof classifies each region hex as element box, corridor, or arm (`feat`)
  and handles the six pairs:
  - two boxes are `≥ 12` apart unless they are the same box;
  - a box and a corridor meet only at a port of an incident edge, and both have owner `e`, or
    the arm on that side (`arms_side`) has owner `e` by (D2);
  - two corridors of different edges meet only near a common end, where the ports differ by (D2)
    and `sep_rays` applies, or else they are `≥ 20` apart by `sep_seg`;
  - two arms of one adapter do not touch (`arms_apart`, carried over by `adj_shift`).
- **Enemy hexes** (`near_z`): a hex of `R_e` equal or adjacent to `z_g` is not `z_g`, has
  `e ∈ S_g`, and equals `d_g^e`.
- **Set vertices** (`set_ports`): exactly the three ports other than the missing one are used.
  This is a counting argument: three edges, one from each element of `S_g`, with pairwise
  different directions by (D2), and every edge into `z_g`'s vertex is one of them (Finding 3).
  Consequences: `arm_edge`, `arm_of_elem`, `arm_owner_inj`, `dHex_spec`.
- **(I1)** (`freeNbrs_z`): the free neighbours of `z_g` are exactly the three translated
  dockings of the adapter frame. Their card is 3 and they are pairwise non-adjacent (kernel).
- **Board and free hexes**: every free hex lies in the `(20gw − 7) × (20gh − 7)` rectangle
  (`region_in`, `free_in`), and `open_iff` says open means free.
- **(I2), connectivity** (`lnk_center`): every hex of `R_e` is linked inside `R_e` to the centre
  of `v_e^1`.
  - Plus hexes walk back to their centre.
  - Path vertices reach `v_e^1` by induction along the path edges; each path edge's whole scaled
    route lies in `R_e`.
  - Corridor hexes walk back along the route to the element end.
  - Arm hexes walk to their port cell. That cell is adjacent to the corridor hex at `20k − 5`.
  - The stub runs back to the centre.

## Target 1 — the drawing as data, the checker (`Homm3/EmbedCheck.lean`, `tools/export_drawing.py`)

- `OrthoDrawing.check q CL` checks `Valid (toX3C q CL)` field by field. `check_sound` proves it
  sound. The pair test covers (D2) ports, (D3) crossings and distinct elements at a set vertex.
- `tools/export_drawing.py` replays steps 0–3 of `build_board_lemma` verbatim: deduplication,
  the `planar_embed.planarity` rotation, node and edge order, and `orthogonal_drawing`. It
  **asserts** that the replayed drawing is the one behind the board, by comparing scaled centres
  with `features["boxes"]` and scaled corner chains with `features["corridors"]`. Every drawing
  already has its bounding box at the origin. The exporter writes `CrossCheckDrawingData.lean`
  (84 kB) and runs in 0.4 s.
- Calibration: all 44 drawings pass `check` in the kernel on the first run, so the definition of
  `Valid` matches `validate_drawing` on the corpus. The checker has teeth. The kernel rejects a
  route stopping short of its target, a route through another vertex's point, a wrong `q`, and
  a re-routed edge that shares points with another route. `SameBoard` also rejects the board of
  another family.

## Target 5 — cross-check against `build_board_lemma` (`CrossCheckDrawing*.lean`, `sorry`: 0)

For each of the 44 families that yield a board, the kernel proves five statements:

- `vaNN : dNN.check qNN CNN = true` — the drawing is valid, hence `invNN` (I1)–(I4) by
  `lemmaD4`, and `verdictNN` holds by `theorem3_drawing`;
- `eqNN : SameBoard dNN qNN CNN lNN kNN` — **the board `build` computes in Lean from the drawing
  is the board of `build_board_lemma` as data**:
  - equal width and height;
  - the label number (byte `x + W·y` = `e + 1` on `R_e`, `128 + g` on `z_g`, `0` impassable)
    equals `lNN.lab`, the number the session-4 check certified;
  - equal lists `p_e` and `z_g`;
  - equal dockings `(g, e, x, y)` for every `e ∈ S_g`.

  The label number is assembled by bitwise or, so a hex claimed by two owners would break the
  equality. The match is exact on every board, with no discrepancy from the D.6 substitutions:
  the drawing already contains the packed components, and Lean builds from the same drawing.
- `s1NN`: the drawing's `G'` is exactly Lean's step 1 (`Step1.vkinds`, `Step1.pairs`) for the
  cut rotation read off the drawing, and that rotation lists each element's members once.

`lake build CrossCheckDrawing` takes about 76–93 s wall with four modules in parallel. Times are
per-declaration differences of the profiler's running totals.

| Board | Family | Drawing gw×gh | V | E | unit steps | Board | Free | Valid (kernel) | Lean board = Python board | Time va / eq, s |
|---|---|---|---|---|---|---|---|---|---|---|
| `d00` | 0 | 3×4 | 4 | 3 | 8 | 53×73 | 169 | ✓ | ✓ | <0.05 / 0.22 |
| `d01` | 1 | 5×16 | 16 | 18 | 57 | 93×313 | 1152 | ✓ | ✓ | 0.72 / 1.43 |
| `d02` | 2 | 6×16 | 16 | 18 | 76 | 113×313 | 1532 | ✓ | ✓ | 0.98 / 1.9 |
| `d03` | 3 | 4×16 | 16 | 18 | 49 | 73×313 | 992 | ✓ | ✓ | 0.7 / 1.18 |
| `d04` | 4 | 8×16 | 16 | 18 | 82 | 153×313 | 1654 | ✓ | ✓ | 1.09 / 2.15 |
| `d05` | 5 | 6×16 | 16 | 18 | 80 | 113×313 | 1612 | ✓ | ✓ | 1.08 / 2.1 |
| `d06` | 6 | 4×16 | 16 | 18 | 56 | 73×313 | 1132 | ✓ | ✓ | 0.71 / 1.38 |
| `d07` | 7 | 4×16 | 16 | 18 | 57 | 73×313 | 1152 | ✓ | ✓ | 0.69 / 1.45 |
| `d08` | 8 | 5×16 | 16 | 18 | 62 | 93×313 | 1252 | ✓ | ✓ | 0.79 / 1.5 |
| `d09` | 9 | 4×16 | 16 | 18 | 49 | 73×313 | 992 | ✓ | ✓ | 0.67 / 1.22 |
| `d10` | 10 | 8×16 | 16 | 18 | 86 | 153×313 | 1734 | ✓ | ✓ | 1.3 / 2.34 |
| `d11` | 11 | 7×12 | 12 | 12 | 57 | 133×233 | 1154 | ✓ | ✓ | 0.51 / 1.39 |
| `d12` | 12 | 7×12 | 12 | 12 | 49 | 133×233 | 994 | ✓ | ✓ | 0.45 / 1.44 |
| `d13` | 16 | 7×12 | 12 | 12 | 54 | 133×233 | 1094 | ✓ | ✓ | 0.49 / 1.22 |
| `d14` | 17 | 7×12 | 12 | 12 | 51 | 133×233 | 1034 | ✓ | ✓ | 0.5 / 1.37 |
| `d15` | 20 | 4×12 | 12 | 12 | 41 | 73×233 | 834 | ✓ | ✓ | 0.4 / 1.2 |
| `d16` | 21 | 4×16 | 16 | 18 | 52 | 73×313 | 1052 | ✓ | ✓ | 0.62 / 1.3 |
| `d17` | 22 | 5×16 | 16 | 18 | 59 | 93×313 | 1192 | ✓ | ✓ | 0.75 / 1.59 |
| `d18` | 23 | 5×16 | 16 | 18 | 59 | 93×313 | 1192 | ✓ | ✓ | 0.82 / 1.65 |
| `d19` | 24 | 7×16 | 16 | 18 | 75 | 133×313 | 1514 | ✓ | ✓ | 1.1 / 1.96 |
| `d20` | 26 | 5×16 | 16 | 18 | 61 | 93×313 | 1232 | ✓ | ✓ | 0.7 / 1.8 |
| `d21` | 27 | 4×16 | 16 | 18 | 55 | 73×313 | 1112 | ✓ | ✓ | 0.8 / 1.4 |
| `d22` | 28 | 6×16 | 16 | 18 | 74 | 113×313 | 1492 | ✓ | ✓ | 1.0 / 1.9 |
| `d23` | 29 | 5×16 | 16 | 18 | 64 | 93×313 | 1292 | ✓ | ✓ | 0.9 / 1.7 |
| `d24` | 30 | 5×16 | 16 | 18 | 62 | 93×313 | 1252 | ✓ | ✓ | 0.84 / 1.6 |
| `d25` | 31 | 9×20 | 20 | 21 | 130 | 173×393 | 2621 | ✓ | ✓ | 2.6 / 3.7 |
| `d26` | 32 | 9×20 | 20 | 21 | 110 | 173×393 | 2219 | ✓ | ✓ | 2.0 / 3.2 |
| `d27` | 33 | 13×20 | 20 | 21 | 179 | 253×393 | 3599 | ✓ | ✓ | 3.5 / 5.1 |
| `d28` | 34 | 11×20 | 20 | 21 | 136 | 213×393 | 2739 | ✓ | ✓ | 2.7 / 4.0 |
| `d29` | 35 | 9×20 | 20 | 21 | 131 | 173×393 | 2639 | ✓ | ✓ | 2.3 / 3.5 |
| `d30` | 36 | 4×20 | 20 | 21 | 64 | 73×393 | 1299 | ✓ | ✓ | 1.2 / 1.7 |
| `d31` | 37 | 11×20 | 20 | 21 | 141 | 213×393 | 2839 | ✓ | ✓ | 2.4 / 3.9 |
| `d32` | 38 | 8×20 | 20 | 21 | 102 | 153×393 | 2059 | ✓ | ✓ | 1.7 / 2.7 |
| `d33` | 39 | 7×20 | 20 | 21 | 82 | 133×393 | 1659 | ✓ | ✓ | 1.4 / 2.2 |
| `d34` | 40 | 7×20 | 20 | 21 | 81 | 133×393 | 1639 | ✓ | ✓ | 1.2 / 2.4 |
| `d35` | 44 | 7×24 | 24 | 27 | 122 | 133×473 | 2457 | ✓ | ✓ | 2.6 / 3.4 |
| `d36` | 47 | 10×24 | 24 | 27 | 150 | 193×473 | 3017 | ✓ | ✓ | 3.2 / 4.4 |
| `d37` | 48 | 6×24 | 24 | 27 | 108 | 113×473 | 2179 | ✓ | ✓ | 2.0 / 3.0 |
| `d38` | 50 | 7×24 | 24 | 27 | 131 | 133×473 | 2637 | ✓ | ✓ | 2.5 / 4.9 |
| `d39` | 51 | 17×20 | 24 | 24 | 158 | 333×393 | 3190 | ✓ | ✓ | 3.9 / 4.6 |
| `d40` | 52 | 12×20 | 24 | 24 | 85 | 233×393 | 1728 | ✓ | ✓ | 1.4 / 2.6 |
| `d41` | 53 | 11×24 | 24 | 24 | 168 | 213×473 | 3388 | ✓ | ✓ | 5.3 / 4.9 |
| `d42` | 54 | 16×20 | 24 | 24 | 181 | 313×393 | 3650 | ✓ | ✓ | 5.7 / 5.1 |
| `d43` | 55 | 12×24 | 24 | 24 | 113 | 233×473 | 2286 | ✓ | ✓ | 2.3 / 4.7 |

Totals: 44 drawings, all `Valid` in the kernel; on all 44 the Lean board equals the Python board
field for field, and `G'` equals Lean's step 1. Kernel time: about 68 s for `va` and 108 s for
`eq` summed over the four parallel modules. The yes/no verdicts themselves are session 4's
(32 yes, 12 no). `verdictNN` now derives them from the drawing through the universal lemma, not
from a certified board.

## Target 6 (stretch) — steps 0 and 1 (`Homm3/Step0.lean`, `Homm3/Step1.lean`, `sorry`: 0)

- Step 0 works on encodings with universe `[0, nX)`. `CoverRaw nX C` means pairwise disjoint
  members whose union is the universe. The no-certificates are proved implications:
  - `no_mod3`: `nX` is not divisible by 3;
  - `no_few`: `|C| < nX / 3`;
  - `no_uncovered`: some element lies in no member;
  - `step0_sound` packages all three as one Bool test after deduplication.

  `cover_dedup` shows that deleting repeated members does not change the answer, through
  `coverRaw_iff_sets`: exact cover depends only on the set of members. `cover_zero` shows
  `|X| = 0` is a yes-instance. `coverRaw_iff` links `CoverRaw (3q)` to `X3C.ExactCover` for
  well-formed instances.
- Step 1 is proved combinatorially, without the embedding. `vkinds`/`pairs` build `G'` for a cut
  rotation, in `build_board_lemma`'s order. `card_V` gives `|V(G')| = 4|C|` and `card_E` gives
  `|E(G')| = 6|C| − |X|` when every element is covered, both by double counting through
  `sum_deg` (`Σ_e d_e = 3|C|`). On the corpus, `s1NN` ties every drawing's `G'` to this
  construction.
- Not done: `Δ(G') ≤ 3` as a theorem about `pairs`, and a proof that `IsStep1` implies the `G'`
  half of `Valid`. On the corpus the latter is covered by `vaNN` together with `s1NN`. Estimate:
  ½ session of list bookkeeping. The drawing half of step 1, that `G'` stays plane, remains a
  citation with steps 2–3.

## Findings (session 5)

1. **(D2)–(D3) need simple routes** (`main.md:1483–1486`). The proof uses that a route never
   revisits a grid point: a segment containing an end's point is then the first or last segment
   (`seg_at_u`, `seg_at_v`). "No path passing through a vertex" must also cover the route's own
   endpoints in its interior. Otherwise a corridor could re-enter its own end's box, and at a
   set vertex it would run through `z_S`. "Grid path" suggests simplicity, and
   `validate_drawing` checks it ("visits a grid point twice"). `Valid` states it (`route.nodup`).
2. **Lemma D.3 needs a boundary clause the paper does not state** (`main.md:1390–1402`,
   `main.md:1587–1590`). Step 6 argues that distinct regions never touch because their features
   are non-incident in `Γ`, so (SEP′) applies. For the corridor of `e` entering a set box at port
   `p` next to the arm of `e′ ≠ e`, the features **are** incident: both belong to the set
   vertex's box. What keeps them apart is that the only arm cells on side `p` of the box belong
   to the arm of port `p`. Otherwise the corridor hex just outside the port could touch another
   arm's boundary cell. Lemma D.3 as stated (paths from ports, non-touching arms, `Z` touched only
   at the ends, unused port closed) does not imply this. It holds for all four Appendix C patterns
   (`arms_side`, kernel), and the Lean proof uses it.
3. **The step-4 case split is per unit segment** (`main.md:1518–1541`). The paper's cases are
   non-incident features by (SEP′) and incident corridors near their shared box by the run
   argument. That split leaves out incident features far from the shared vertex: a box and a
   later segment of an incident edge's own route coming back near it, or two corridors with a
   common end approaching each other elsewhere. All of these are covered by (SEP) applied to unit
   segments (`sep_pt`, `sep_seg`), which is how the Lean proof is organized. The statement is
   true and the gap is only in the written case analysis.
4. **Step 2 is not needed by steps 4–6** (`main.md:1463–1480`). `Valid` does not ask for a
   connected `G'`, so `lemmaD4` covers a drawing of all components at once. The third
   subroutine substitution of D.6, packing the component *drawings* before scaling, is thus
   justified by the universal lemma itself. The corpus drawings are such packed drawings, and
   the boards match bit for bit.
5. **The stub is not load-bearing for (I1)–(I4)** (`main.md:1559–1579`). The proof treats the
   stub as part of `v_e^1`'s element box, all of which belongs to `R_e`. Separation needs only
   radius `≤ ρ`. So neither the "exactly one free neighbour" clause (`check_stub.py`, 64 cases)
   nor the measured `L∞` 12 neighbourhood of the stub is used, and a stub along a used port would
   do as well. Session 4's Finding 6 said Theorem 3 needs only `p_e ∈ R_e`; now Lemma D.4 needs no
   more either.
6. **`Δ(G′) ≤ 3` is used only at set vertices, where it follows from `S_g` having 3 elements**
   (`main.md:1446–1461`, `main.md:1559–1560`). The count of three ports at a set vertex comes from
   `P.WF` and the incidence clauses (`set_ports`). At element vertices neither the degree bound
   nor port uniqueness is used, because every hex of an element box and of its incident corridors
   belongs to the same region. `Valid` therefore omits the degree bound.
7. **Python and paper differ on isolated path vertices** (`main.md:1552–1554`). The paper frees
   "the axis segments from the centre to the used ports plus the centre". `embed_lemma.py` frees
   the centre only through the runs, so a path vertex with no incident route would keep its
   centre impassable. Lean follows the paper. The case never reaches the board: step 0 sends
   uncovered elements to `G_no`. The corpus boards agree bit for bit.
8. **Confirmations.** The following are all checked directly:
   - parity (`φ_even`; `boxHex` is `shift (20c₁ + 2, 2(10c₂ + 1))`, an even row shift,
     `main.md:1511`, `main.md:1542–1549`);
   - "`d_S^e` adjacent to `z_S` alone" (`dAlone`, by box separation);
   - the board border (the `ω = 6` margin keeps every free hex inside the rectangle, `region_in`,
     with no impassable frame needed beyond it, `main.md:1505–1512`);
   - `|E(G′)| = 6|C| − |X|` needs every element covered (`card_E`, `main.md:1461`).

## Blockers and friction (session 5)

- No mathematical blocker. The universal lemma closed in one session rather than the 2–3
  estimated. What made it short: the unit-segment form of (SEP), `omega` over 16 direction
  pairs, and a single proximity lemma (`prox`) that yields `rDisj`, `rClosed` and `rOpen`.
- The worktree guard rejects compound shell lines (heredocs with `cd`, `$(...)` arithmetic).
  Snippets are written with the Write tool and inserted by a small script that checks the
  marker count, as in session 4.
- The name `P` for `X3C` collided with a drawing accessor `Dr.P` (`unfold P` hit the local). The
  accessor is now `loc`.
- A `Decidable` instance for one big conjunction of adapter facts failed to synthesize, while each
  part succeeded. The fact is split into nine `decide +kernel` theorems.
- `(List.range 5).map (fun t => … t …)` with `t` coerced to `ℤ` elaborated as a coerced list
  (`do`-notation in the goal). The binder is typed explicitly `(t : ℕ)`.
- `List.mergeSort` is well-founded recursion and is avoided in kernel checks. `ordOf` uses
  `filterMap` over indices instead.

## Totals (end of session 5)

- 35 modules + root, **12039** library lines (session 4: 9757). There are also
  `CrossCheckDrawing*.lean` (6 files, data 84 kB) and `tools/export_drawing.py` (≈ 240 lines).
- Theorems: **700** by the session-4 count (session 4: 541). New modules, with lines / theorems:
  - `EmbedGeom` 521 / 58;
  - `Embed` 1221 / 82;
  - `EmbedCheck` 244 / 4;
  - `Step0` 161 / 10;
  - `Step1` 144 / 5.
- **0 `sorry`**, 0 axioms introduced, no `native_decide`.
- Wall clock: reading and design about 10 min (22:55–23:05), target 2 about 10 min, targets 3–4
  about 19 min (to 23:34), targets 1 and 5 10 min (to 23:44), target 6 7 min (to 23:51), write-up
  about 15 min.

## What remains

- **Steps 0–3 as mathematics**: planarity (DMP / Hopcroft–Tarjan), the embedding half of step 1,
  and Tamassia–Tollis stay citations, as planned. These are formalization projects of their own,
  far beyond this artifact.
- Optional, about ½ session: `Δ(G') ≤ 3` for `Step1.pairs`, and "`IsStep1` ⇒ the `G'` half of
  `Valid`". That would split `Valid` into "Lean's step 1" plus pure drawing geometry
  (D1)–(D3).
- Optional: polynomial-time bounds as statements about running time. Lean functions are
  computable, but complexity is not formalized anywhere in the library.
- With this session, Theorem 3 is formalized **modulo only the drawing**: for any `X3C` instance
  and any valid orthogonal drawing of its `G'`, the constructed board is a correct instance. The
  literature supplies the drawing for planar instances.

## Commits (session 5)

- `4a7c619` formal/lean: сессия 5, цели 2–4 — универсальная Лемма D.4 (шаги 4–6), lemmaD4, theorem3_drawing
- `2b81daa` formal/lean: сессия 5, цели 1 и 5 — чекер чертежа, тотальная форма, сверка 44 чертежей с build_board_lemma
- `1bb4f54` formal/lean: сессия 5, цель 6 — шаги 0 и 1 (no-сертификаты, дедупликация, |V|, |E|)
- (this write-up: the commit that adds this section)
