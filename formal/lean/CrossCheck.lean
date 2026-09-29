import Homm3.Exec
import Homm3.Theorem1
import Homm3.LemmaE20

/-!
# Session 2, target 4b. Execution cross-check against `brute_force.py` / `dp_single_type.py`

Run: `lake env lean CrossCheck.lean` (not part of the library build: it takes minutes).

Every number here is computed by the *verified* search of `Homm3/Exec.lean` on the Lean
semantics (`Step`), and compared with the number the Python reference prints:

* **Theorem 1 tier** (`brute_force.py`, 28 PARTITION instances, variant `waitdefend` = `(‡)`):
  Python's `best_value` is the maximum over all allocations of its attack-only search.  Lean
  computes (a) the same fragment, `max_α valueAO`, and (b) where feasible the **full-model
  optimum** `optimum (G a)` (all player actions: `WAIT`, `DEFEND`, move, `WALK_AND_ATTACK`),
  which by `armyAllocation_iff` decides `ARMY-ALLOCATION` exactly.
* **Theorem 2 tier** (`brute_force.py`, 14 3-PARTITION instances, bijection allocations):
  Lean computes the attack-only maximum over the same 720 bijections.
* **`dp_single_type.py` check [2]** (40 single-creature corridors, seed 20261018): Lean's
  full-model optimum against the DP value (which Python asserts equals its game search).
* **Negative control** (multi-creature enemy stacks): full-model optimum `3`, DP `0`.

Python's instance data are transcribed from its printed output and from a scratch re-run
of its seeded generator (session-2 notes in `PROGRESS.md`).
-/

open Homm3 Homm3.Corridor

namespace CrossCheck

/-! ## Instances -/

/-- `brute_force.py`, Theorem 1 tier, variant `waitdefend`: `(a, B, PARTITION?, best_value)`. -/
def thm1Cases : List (List ℕ × ℕ × String × ℕ) := [
  ([1, 1], 1, "Y", 1),
  ([2, 2], 2, "Y", 2),
  ([1, 3], 2, "N", 1),
  ([3, 5], 4, "N", 3),
  ([2, 4, 6], 6, "Y", 6),
  ([1, 2, 3], 3, "Y", 3),
  ([1, 1, 2, 4], 4, "Y", 4),
  ([2, 3, 4, 5], 7, "Y", 7),
  ([1, 5, 6, 8], 10, "N", 9),
  ([3, 3, 3, 3], 6, "Y", 6),
  ([2, 2, 3, 7], 7, "Y", 7),
  ([1, 2, 3, 6], 6, "Y", 6),
  ([1, 4, 6, 9], 10, "Y", 10),
  ([2, 5, 5, 8], 10, "Y", 10),
  ([1, 2, 3], 3, "Y", 3),
  ([3, 8, 9], 10, "N", 9),
  ([4, 4, 6], 7, "N", 6),
  ([1, 3, 6], 5, "N", 4),
  ([3, 6, 7], 8, "N", 7),
  ([4, 8, 8], 10, "N", 8),
  ([2, 3, 6, 7], 9, "Y", 9),
  ([2, 5, 6, 7], 10, "N", 9),
  ([2, 2, 4, 6], 7, "N", 6),
  ([2, 2, 3, 3], 5, "Y", 5),
  ([2, 4, 5, 7], 9, "Y", 9),
  ([1, 1, 4, 4], 5, "Y", 5),
  ([4, 5, 6, 7], 11, "Y", 11),
  ([6, 6, 7, 7], 13, "Y", 13)]

/-- `brute_force.py`, Theorem 2 tier, variant `waitdefend`: `(a, T, 3-PARTITION?, kills)`. -/
def thm2Cases : List (List ℕ × ℕ × String × ℕ) := [
  ([9, 9, 7, 9, 7, 7], 24, "N", 1),
  ([8, 9, 12, 11, 8, 8], 28, "Y", 2),
  ([7, 10, 7, 7, 9, 8], 24, "Y", 2),
  ([10, 9, 12, 9, 8, 8], 28, "Y", 2),
  ([6, 7, 6, 8, 6, 7], 20, "Y", 2),
  ([7, 7, 8, 8, 10, 8], 24, "Y", 2),
  ([11, 10, 8, 9, 9, 9], 28, "Y", 2),
  ([6, 6, 8, 6, 6, 8], 20, "Y", 2),
  ([7, 7, 10, 10, 7, 7], 24, "Y", 2),
  ([11, 8, 13, 8, 8, 8], 28, "N", 1),
  ([10, 8, 10, 9, 11, 8], 28, "Y", 2),
  ([8, 8, 8, 8, 9, 7], 24, "Y", 2),
  ([8, 8, 7, 11, 7, 7], 24, "N", 1),
  ([7, 7, 7, 7, 6, 6], 20, "Y", 2)]

/-- `dp_single_type.py` check [2]: `(trial, [(hp, value)], B, dp)`. -/
def dpCases : List (ℕ × List (ℕ × ℕ) × ℕ × ℕ) := [
  (0, [(1, 8)], 3, 8),
  (1, [(1, 4), (1, 5), (3, 3)], 5, 12),
  (2, [(5, 1), (2, 3), (1, 2)], 5, 5),
  (3, [(5, 4), (5, 9), (1, 2)], 2, 2),
  (4, [(4, 1), (1, 9), (1, 3)], 6, 13),
  (5, [(5, 1)], 6, 1),
  (6, [(3, 9), (1, 5), (1, 1)], 1, 5),
  (7, [(4, 9)], 6, 9),
  (8, [(4, 8)], 6, 8),
  (9, [(5, 4), (1, 8), (5, 4)], 4, 8),
  (10, [(1, 3)], 6, 3),
  (11, [(3, 7), (2, 1), (1, 6)], 1, 6),
  (12, [(4, 4), (1, 2)], 6, 6),
  (13, [(2, 4), (5, 2), (5, 6)], 2, 4),
  (14, [(2, 7), (5, 7), (2, 8)], 6, 15),
  (15, [(5, 5), (4, 8)], 2, 0),
  (16, [(1, 4), (2, 1)], 1, 4),
  (17, [(5, 6), (2, 5), (4, 1)], 5, 6),
  (18, [(4, 9), (4, 7)], 5, 9),
  (19, [(3, 2), (5, 8), (2, 3)], 2, 3),
  (20, [(4, 4)], 1, 0),
  (21, [(5, 1)], 2, 0),
  (22, [(5, 7), (2, 5), (5, 5)], 1, 0),
  (23, [(3, 7), (3, 9), (5, 7)], 4, 9),
  (24, [(1, 3), (5, 6), (5, 5)], 2, 3),
  (25, [(5, 6)], 6, 6),
  (26, [(4, 4), (2, 3), (2, 6)], 1, 0),
  (27, [(1, 3), (3, 5), (3, 5)], 4, 8),
  (28, [(3, 9), (5, 1)], 1, 0),
  (29, [(5, 1)], 2, 0),
  (30, [(1, 1)], 5, 1),
  (31, [(5, 5), (3, 3), (1, 7)], 5, 10),
  (32, [(4, 3), (2, 4), (5, 7)], 4, 4),
  (33, [(5, 3), (5, 3), (5, 1)], 2, 0),
  (34, [(4, 1), (1, 6)], 1, 6),
  (35, [(1, 6), (5, 5), (2, 2)], 2, 6),
  (36, [(1, 8), (4, 1), (4, 4)], 3, 8),
  (37, [(3, 2), (5, 3), (3, 6)], 2, 0),
  (38, [(1, 3), (2, 1), (1, 7)], 5, 11),
  (39, [(1, 3), (3, 3), (5, 8)], 6, 11)]

/-- `brute_force.build_3partition_instance`: board `(8m+2) × 3`; group `g` has its enemy at
`(8g+1, 1)` and slots at `(8g, 1), (8g+1, 0), (8g+1, 2)`; type `i` has damage `a_i`,
`hp 5`, speed 2, stock 1; enemies `hp T`, speed 1, value 1; `W = m`. -/
def threePart (a : List ℕ) (T : ℕ) : Instance :=
  let m := a.length / 3
  { width := 8 * m + 2
    height := 3
    obstacles := ∅
    slots := (List.range m).flatMap (fun g =>
      [⟨8 * g, 1⟩, ⟨8 * g + 1, 0⟩, ⟨8 * g + 1, 2⟩])
    army := a.map (fun ai => (⟨1, 1, ai, 5, 2, 0⟩, 1))
    enemies := (List.range m).map (fun g => ⟨⟨1, 1, 1, T, 1, 1⟩, 1, ⟨8 * g + 1, 1⟩⟩)
    R := 1
    W := m }

/-- The bijection tier of `brute_force.run_3partition_case`: slot `s` gets type `π s`. -/
def bijAllocs (k : ℕ) : List (ℕ → SlotAlloc) :=
  (List.range k).permutations.map (fun π j => ⟨π.getD j 0, 1⟩)

/-- `dp_single_type.build_corridor`: enemies `(count, hp, value)`, enemy speed `0` as in the
script, player `att = def = 1`, damage 1, `hp 5`, speed 2, stock `B`. -/
def dpCorridor (enemies : List (ℕ × ℕ × ℕ)) (B : ℕ) : Instance :=
  let n := enemies.length
  { width := 5 * n
    height := 1
    obstacles := ∅
    slots := (List.range n).map p
    army := [(⟨1, 1, 1, 5, 2, 0⟩, B)]
    enemies := (List.range n).map (fun j =>
      let e := enemies.getD j (0, 0, 0)
      ⟨⟨1, 1, 1, e.2.1, 0, e.2.2⟩, e.1, Corridor.e j⟩)
    R := 1
    W := 1 }

def maxOver (L : List (ℕ → SlotAlloc)) (f : (ℕ → SlotAlloc) → ℕ) : ℕ := (L.map f).foldr max 0

/-! ## Runner -/

def timed (f : Unit → ℕ) : IO (ℕ × ℕ) := do
  let t0 ← IO.monoMsNow
  let v ← IO.lazyPure f
  let t1 ← IO.monoMsNow
  return (v, t1 - t0)

def okStr (b : Bool) : String := if b then "agree" else "DISAGREE"

def runThm1 (full : List ℕ → Bool) : IO Unit := do
  IO.println "== Theorem 1 tier (brute_force.py, waitdefend) =="
  IO.println "a | B | PARTITION | python best | lean AO | lean full | verdict | ms"
  for (a, B, part, py) in thm1Cases do
    let I := G a
    let (ao, t1) ← timed fun _ => maxOver (allocs I) (valueAO I)
    let (fl, t2) ← if full a then do
        let (v, t) ← timed fun _ => optimum I
        pure (some v, t)
      else pure (none, 0)
    let flStr := match fl with | some v => toString v | none => "-"
    let good := ao == py && (match fl with | some v => v == py | none => true) &&
      (decide (I.W ≤ ao) == (part == "Y"))
    IO.println s!"{a} | {B} | {part} | {py} | {ao} | {flStr} | {okStr good} | {t1 + t2}"

def runThm2 (idx : List ℕ) : IO Unit := do
  IO.println "== Theorem 2 tier (brute_force.py, waitdefend, bijections) =="
  IO.println "a | T | 3-PARTITION | python kills | lean AO | all feasible | verdict | ms"
  for i in idx do
    let (a, T, part, py) := thm2Cases.getD i ([], 0, "", 0)
    let I := threePart a T
    let L := bijAllocs 6
    let feas := L.all (fun α => decide (Feasible I α))
    let (ao, t) ← timed fun _ => maxOver L (valueAO I)
    let good := ao == py && feas && (decide (I.W ≤ ao) == (part == "Y"))
    IO.println s!"{a} | {T} | {part} | {py} | {ao} | {feas} | {okStr good} | {t}"

def runDp : IO Unit := do
  IO.println "== dp_single_type.py check [2] (full model vs DP) =="
  IO.println "trial | enemies (hp,value) | B | dp | lean full | verdict | ms"
  for (tr, es, B, d) in dpCases do
    let I := dpCorridor (es.map (fun e => (1, e.1, e.2))) B
    let (v, t) ← timed fun _ => optimum I
    IO.println s!"{tr} | {es} | {B} | {d} | {v} | {okStr (v == d)} | {t}"
  let I := dpCorridor [(6, 2, 1), (6, 2, 1)] 6
  let (v, t) ← timed fun _ => optimum I
  IO.println s!"negative control [(6,2,1),(6,2,1)] B=6 | dp 0 | python game 3 | lean full {v} | {okStr (v == 3)} | {t}"

/-! ## Session 3: Tier B cross-check support -/

/-- `threePart` is `G_{3P}` of `Theorem2.lean` on every six-entry list (`m = 2`, the whole
Theorem 2 tier of `brute_force.py`), so session 2's runs of `threePart` are runs of `G3P`. -/
theorem threePart_eq6 (x0 x1 x2 x3 x4 x5 T : ℕ) :
    threePart [x0, x1, x2, x3, x4, x5] T = G3P [x0, x1, x2, x3, x4, x5] T := by
  simp only [threePart, G3P, famInst, Thm2.layout, famPlayer, famEnemy, List.length_cons,
    List.length_nil]
  norm_num [List.range_succ, Thm2.seat, Thm2.ehex]

/-- A restricted attack-only successor function: a player stack passes, or strikes a living
enemy from the **first** hex of its BFS list adjacent to it (one approach hex per target
instead of all). Every successor is an attack-only successor (`mem_succsR`), so its value is
attained by a genuine play and bounds the optimum from below. -/
def succsR (I : Instance) (s : State) : List State :=
  match s.queue with
  | [] => succsEnd I s
  | i :: q =>
    if (s.units i).alive then
      if (s.units i).side = .enemy then
        if s.phase = .normal then [sWait s i q] else [sDefend s i q]
      else
        let R := reachListOf I s.units i
        sMove s i q (s.units i).hex ::
          (List.range I.N).filterMap (fun t =>
            if (s.units t).alive ∧ (s.units t).side = .enemy then
              (R.find? (fun d => decide (Hex.Adj d (s.units t).hex))).map
                (fun d => sAttack s i q d t)
            else none)
    else [sSkip s q]

theorem mem_succsR {I : Instance} {s s' : State} (h : s' ∈ succsR I s) : s' ∈ succsAO I s := by
  rcases hq : s.queue with _ | ⟨i, q⟩
  · simp only [succsR, hq] at h; simpa [succsAO, hq] using h
  · simp only [succsR, hq] at h
    simp only [succsAO, hq]
    split_ifs at h ⊢ with ha hs hp
    · exact h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · obtain ⟨t, ht, hft⟩ := List.mem_filterMap.mp h
        split_ifs at hft with hc
        obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hft
        have hp' := List.find?_some hd
        have hm := List.mem_of_find?_eq_some hd
        exact List.mem_cons_of_mem _ (mem_attacks.mpr ⟨d, mem_reachListOf.mp hm, t,
          List.mem_range.mp ht, hc.1, hc.2, of_decide_eq_true hp', rfl⟩)
    · exact h

theorem succsR_ne_nil {I : Instance} {s : State} (hd : ¬ Done s) : succsR I s ≠ [] := by
  rcases hq : s.queue with _ | ⟨i, q⟩
  · simp only [succsR, hq]; exact succsEnd_ne_nil hq hd
  · simp only [succsR, hq]; split_ifs <;> simp

/-- The value of the restricted search. -/
def valueR (I : Instance) (α : ℕ → SlotAlloc) : ℕ :=
  bestWith I (succsR I) (μ I (initState I α)) (initState I α)

theorem valueR_attained {I : Instance} {α : ℕ → SlotAlloc} :
    ∃ s, Reach I α s ∧ Done s ∧ destroyed I s = valueR I α :=
  bestWith_attained (fun _ _ h => step_of_mem_succsAO (mem_succsR h))
    (fun _ h => succsR_ne_nil h) _ _ le_rfl

/-- A single greedy line through `succsR`: always the **last** listed successor (a player
strikes the highest-index living enemy it can reach, else passes). Cheap, and attained. -/
def succsG (I : Instance) (s : State) : List State :=
  match (succsR I s).getLast? with
  | some t => [t]
  | none => []

theorem mem_succsG {I : Instance} {s s' : State} (h : s' ∈ succsG I s) : s' ∈ succsAO I s := by
  unfold succsG at h
  rcases hl : (succsR I s).getLast? with _ | t
  · simp [hl] at h
  · simp only [hl, List.mem_singleton] at h
    subst h
    exact mem_succsR (List.mem_of_getLast? hl)

theorem succsG_ne_nil {I : Instance} {s : State} (hd : ¬ Done s) : succsG I s ≠ [] := by
  unfold succsG
  rcases hl : (succsR I s).getLast? with _ | t
  · exact absurd (List.getLast?_eq_none_iff.mp hl) (succsR_ne_nil hd)
  · simp

/-- The value of the greedy line. -/
def valueG (I : Instance) (α : ℕ → SlotAlloc) : ℕ :=
  bestWith I (succsG I) (μ I (initState I α)) (initState I α)

theorem valueG_attained {I : Instance} {α : ℕ → SlotAlloc} :
    ∃ s, Reach I α s ∧ Done s ∧ destroyed I s = valueG I α :=
  bestWith_attained (fun _ _ h => step_of_mem_succsAO (mem_succsG h))
    (fun _ h => succsG_ne_nil h) _ _ le_rfl

/-- An allocation in `verify_featureless.py`'s format: slot `j` holds type `l[j]` or nothing. -/
def pyAlloc (l : List (Option ℕ)) (j : ℕ) : SlotAlloc :=
  match l.getD j none with
  | some t => ⟨t, 1⟩
  | none => ⟨0, 0⟩

/-! ### Proof-level verdicts on the tested instances (kernel-checked) -/

theorem g3p_yes {a : List ℕ} {T : ℕ} (hP : Promise3P a T) (σ : List ℕ)
    (h : ThreeP.checkSeating a T σ = true) : ArmyAllocation (G3P a T) :=
  (Thm2.theorem2 a T hP).mp (ThreeP.of_seating σ h)

theorem g3p_no {a : List ℕ} {T : ℕ} (hP : Promise3P a T) (hm : 0 < a.length / 3)
    (h : ThreeP.checkNoTriple a T = true) : ¬ ArmyAllocation (G3P a T) :=
  fun hA => ThreeP.not_of_checkNoTriple hm h ((Thm2.theorem2 a T hP).mpr hA)

theorem gf_yes {a : List ℕ} {T : ℕ} (hP : Promise3P a T) (σ : List ℕ)
    (h : ThreeP.checkSeating a T σ = true) :
    ArmyAllocation (GF a T) ∧ ThmF.BattlePlay (GF a T) ThmF.αId ∧
      ThmF.HpAllocation (GF a T) (a.length / 3 * T) :=
  have h3 := ThreeP.of_seating σ h
  ⟨(ThmF.theorem4 a T hP).mp h3, (ThmF.cor41 a T hP).mp h3, (ThmF.cor42 a T hP).1.mp h3⟩

theorem gf_no {a : List ℕ} {T : ℕ} (hP : Promise3P a T) (hm : 0 < a.length / 3)
    (h : ThreeP.checkNoTriple a T = true) :
    ¬ ArmyAllocation (GF a T) ∧ ¬ ThmF.BattlePlay (GF a T) ThmF.αId ∧
      ¬ ThmF.HpAllocation (GF a T) (a.length / 3 * T) :=
  have hn := ThreeP.not_of_checkNoTriple hm h
  ⟨fun hA => hn ((ThmF.theorem4 a T hP).mpr hA), fun hA => hn ((ThmF.cor41 a T hP).mpr hA),
    fun hA => hn ((ThmF.cor42 a T hP).1.mpr hA)⟩

-- `brute_force.py`, Theorem 2 tier: the 14 instances (Python's 3-PARTITION column and game
-- verdict in `thm2Cases`), yes-seatings from a scratch run of `_solution_assignment`.
theorem t2_c0 : ¬ ArmyAllocation (G3P [9, 9, 7, 9, 7, 7] 24) := g3p_no (by decide) (by decide) rfl
theorem t2_c1 : ArmyAllocation (G3P [8, 9, 12, 11, 8, 8] 28) := g3p_yes (by decide) [0, 1, 3, 2, 4, 5] rfl
theorem t2_c2 : ArmyAllocation (G3P [7, 10, 7, 7, 9, 8] 24) := g3p_yes (by decide) [0, 1, 2, 3, 4, 5] rfl
theorem t2_c3 : ArmyAllocation (G3P [10, 9, 12, 9, 8, 8] 28) := g3p_yes (by decide) [0, 1, 3, 2, 4, 5] rfl
theorem t2_c4 : ArmyAllocation (G3P [6, 7, 6, 8, 6, 7] 20) := g3p_yes (by decide) [0, 1, 5, 2, 3, 4] rfl
theorem t2_c5 : ArmyAllocation (G3P [7, 7, 8, 8, 10, 8] 24) := g3p_yes (by decide) [0, 1, 4, 2, 3, 5] rfl
theorem t2_c6 : ArmyAllocation (G3P [11, 10, 8, 9, 9, 9] 28) := g3p_yes (by decide) [0, 2, 3, 1, 4, 5] rfl
theorem t2_c7 : ArmyAllocation (G3P [6, 6, 8, 6, 6, 8] 20) := g3p_yes (by decide) [0, 1, 2, 3, 4, 5] rfl
theorem t2_c8 : ArmyAllocation (G3P [7, 7, 10, 10, 7, 7] 24) := g3p_yes (by decide) [0, 1, 2, 3, 4, 5] rfl
theorem t2_c9 : ¬ ArmyAllocation (G3P [11, 8, 13, 8, 8, 8] 28) := g3p_no (by decide) (by decide) rfl
theorem t2_c10 : ArmyAllocation (G3P [10, 8, 10, 9, 11, 8] 28) := g3p_yes (by decide) [0, 1, 2, 3, 4, 5] rfl
theorem t2_c11 : ArmyAllocation (G3P [8, 8, 8, 8, 9, 7] 24) := g3p_yes (by decide) [0, 1, 2, 3, 4, 5] rfl
theorem t2_c12 : ¬ ArmyAllocation (G3P [8, 8, 7, 11, 7, 7] 24) := g3p_no (by decide) (by decide) rfl
theorem t2_c13 : ArmyAllocation (G3P [7, 7, 7, 7, 6, 6] 20) := g3p_yes (by decide) [0, 1, 4, 2, 3, 5] rfl

-- `verify_featureless.py` C6 default tier (and `verify_hp_objective.py`'s smallest cases).
theorem t4_yes13 : ArmyAllocation (GF [4, 4, 4, 4, 5, 5] 13) ∧
    ThmF.BattlePlay (GF [4, 4, 4, 4, 5, 5] 13) ThmF.αId ∧
    ThmF.HpAllocation (GF [4, 4, 4, 4, 5, 5] 13) 26 :=
  gf_yes (by decide) [0, 1, 4, 2, 3, 5] rfl
theorem t4_no13 : ¬ ArmyAllocation (GF [4, 4, 4, 4, 4, 6] 13) ∧
    ¬ ThmF.BattlePlay (GF [4, 4, 4, 4, 4, 6] 13) ThmF.αId ∧
    ¬ ThmF.HpAllocation (GF [4, 4, 4, 4, 4, 6] 13) 26 :=
  gf_no (by decide) (by decide) rfl

/-- `BattlePlay` depends on the allocation only through the normalized slots. -/
theorem battlePlay_congr {I : Instance} {α β : ℕ → SlotAlloc}
    (h : ∀ j < I.k, normA (α j) = normA (β j)) : ThmF.BattlePlay I α ↔ ThmF.BattlePlay I β := by
  unfold ThmF.BattlePlay Reach initState
  rw [initUnits_congr h]

/-- `verify_featureless.py`'s identity allocation is `αId` of Corollary 4.1 on six slots. -/
def pyId6 : List (Option ℕ) := [some 0, some 1, some 2, some 3, some 4, some 5]

theorem pyId6_norm (a : List ℕ) (T : ℕ) (hk : (GF a T).k = 6) :
    ∀ j < (GF a T).k, normA (pyAlloc pyId6 j) = normA (ThmF.αId j) := by
  intro j hj
  rw [hk] at hj
  interval_cases j <;> rfl

/-- C6 yes-instance, identity allocation: a play destroys both enemies (exact value 2). -/
theorem t4_yes13_id : ThmF.BattlePlay (GF [4, 4, 4, 4, 5, 5] 13) (pyAlloc pyId6) :=
  (battlePlay_congr (pyId6_norm _ _ rfl)).mpr t4_yes13.2.1

/-- C6 no-instance, identity allocation: no play destroys both (exact value `≤ 1`). -/
theorem t4_no13_id : ¬ ThmF.BattlePlay (GF [4, 4, 4, 4, 4, 6] 13) (pyAlloc pyId6) :=
  fun h => t4_no13.2.1 ((battlePlay_congr (pyId6_norm _ _ rfl)).mp h)

/-- Per-allocation upper bound on `G_F` (proof level): `destroyed · T ≤ Σ nominal`. -/
theorem gf_value_le {a : List ℕ} {T : ℕ} (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x)
    {α : ℕ → SlotAlloc} (hα : Feasible (GF a T) α) {s : State} (hs : Reach (GF a T) α s) :
    destroyed (GF a T) s * T ≤
      ∑ j ∈ Finset.range (3 * (a.length / 3)), nominal (GF a T) α j := by
  have := Fam.destroyed_mul_le (L := ThmF.layout (a.length / 3)) hT ha hα hs
  simp only [ThmF.layout, List.length_map, List.length_range] at this
  exact this

end CrossCheck
