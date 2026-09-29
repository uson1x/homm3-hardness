import Homm3.MatchingReach

/-!
# Session 2, target 4a. An executable, verified decision procedure for `ARMY-ALLOCATION`

The semantics of `Battle.lean` is a relation (`Step`).  This module makes it executable and
proves the executable version equivalent:

* `succs I s` lists the successors of a position; `step_iff_mem_succs`:
  `Step I s s' ↔ s' ∈ succs I s` (all nine rules, both directions).
* `μ I s` is a termination measure: every step decreases it (`Step.μ_lt`), and `μ = 0`
  only at a finished battle.  Every unfinished position has a successor (`progress`), a
  finished one has none (`not_step_of_done`).
* `bestWith I next f s` is the maximum destroyed value over the complete plays from `s`
  that follow the successor function `next`, with fuel `f ≥ μ I s`; `le_bestWith` and
  `bestWith_attained` are its correctness, generic in `next`.
* `allocs I` enumerates the feasible allocations up to the fields `initUnits` reads;
  `exists_mem_allocs` shows every feasible allocation has the same starting position as one
  of them.
* **`armyAllocation_iff`**: `ArmyAllocation I ↔ I.W ≤ optimum I`, for every instance; hence
  a `Decidable (ArmyAllocation I)` instance.
* The **attack-only fragment** of `brute_force.py` (at its `NORMAL` activation a player
  stack either passes or issues `WALK_AND_ATTACK` with any target and approach hex; it never
  waits, moves or defends): `succsAO`, a sub-relation of `Step` (`step_of_mem_succsAO`).  Its
  value `valueAO` is attained by a genuine play (`valueAO_attained`) and is at most the full
  value (`valueAO_le_value`).  "Pass" is realized as the legal move to the stack's own hex,
  which changes nothing (the player's `DEFEND` flag is already down).
-/

namespace Homm3

open Function

/-! ## Lists instead of finsets -/

/-- The BFS of `reach`, on lists (`Finset.toList` is not computable). -/
def reachL (free : Hex → Prop) [DecidablePred free] (p : Hex) : ℕ → List Hex
  | 0 => [p]
  | s + 1 =>
    let r := reachL free p s
    (r ++ r.flatMap (fun h => h.nbrs.filter (fun q => decide (free q)))).dedup

theorem mem_reachL {free : Hex → Prop} [DecidablePred free] (p : Hex) :
    ∀ s q, q ∈ reachL free p s ↔ q ∈ reach free p s
  | 0, q => by simp [reachL, reach]
  | s + 1, q => by
    simp only [reachL, reach, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_filter, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      mem_reachL p s]

def reachListOf (I : Instance) (us : ℕ → Stack) (i : ℕ) : List Hex :=
  reachL (free I us i) (us i).hex (us i).type.spd

theorem mem_reachListOf {I : Instance} {us : ℕ → Stack} {i : ℕ} {h : Hex} :
    h ∈ reachListOf I us i ↔ h ∈ reachOf I us i := mem_reachL _ _ _

/-- The living enemy stacks adjacent to `dest`. -/
def targets (I : Instance) (us : ℕ → Stack) (dest : Hex) : List ℕ :=
  (List.range I.N).filter
    (fun t => decide ((us t).alive ∧ (us t).side = .enemy ∧ Hex.Adj dest (us t).hex))

theorem mem_targets {I : Instance} {us : ℕ → Stack} {dest : Hex} {t : ℕ} :
    t ∈ targets I us dest ↔
      t < I.N ∧ (us t).alive ∧ (us t).side = .enemy ∧ Hex.Adj dest (us t).hex := by
  simp [targets]

/-! ## The successor function -/

def sSkip (s : State) (q : List ℕ) : State := { s with queue := q }
def sWait (s : State) (i : ℕ) (q : List ℕ) : State :=
  { s with units := update s.units i (activate (s.units i)), queue := q,
           bucket := s.bucket ++ [i] }
def sDefend (s : State) (i : ℕ) (q : List ℕ) : State :=
  { s with units := update s.units i { activate (s.units i) with defending := true },
           queue := q }
def sMove (s : State) (i : ℕ) (q : List ℕ) (dest : Hex) : State :=
  { s with units := update s.units i { activate (s.units i) with hex := dest }, queue := q }
def sAttack (s : State) (i : ℕ) (q : List ℕ) (dest : Hex) (t : ℕ) : State :=
  { s with units := resolveAttack s.units i t dest, queue := q }
def sToWait (s : State) : State :=
  { s with phase := .wait, queue := s.bucket.mergeSort (waitLe s.units), bucket := [] }

/-- Successors when the current phase queue is exhausted. -/
def succsEnd (I : Instance) (s : State) : List State :=
  (if s.phase = .normal then [sToWait s] else []) ++
    (if s.phase = .wait ∧ 1 < s.roundsLeft then [newRound I s] else [])

/-- All attacks of stack `i`. -/
def attacks (I : Instance) (s : State) (i : ℕ) (q : List ℕ) : List State :=
  (reachListOf I s.units i).flatMap (fun dest => (targets I s.units dest).map (sAttack s i q dest))

/-- All successors of a position. -/
def succs (I : Instance) (s : State) : List State :=
  match s.queue with
  | [] => succsEnd I s
  | i :: q =>
    if (s.units i).alive then
      if (s.units i).side = .enemy then
        if s.phase = .normal then [sWait s i q] else [sDefend s i q]
      else
        (if s.phase = .normal then [sWait s i q] else []) ++ [sDefend s i q] ++
          (reachListOf I s.units i).map (sMove s i q) ++ attacks I s i q
    else [sSkip s q]

/-- The attack-only fragment searched by `brute_force.py`. -/
def succsAO (I : Instance) (s : State) : List State :=
  match s.queue with
  | [] => succsEnd I s
  | i :: q =>
    if (s.units i).alive then
      if (s.units i).side = .enemy then
        if s.phase = .normal then [sWait s i q] else [sDefend s i q]
      else sMove s i q (s.units i).hex :: attacks I s i q
    else [sSkip s q]

variable {I : Instance} {s s' : State}

theorem mem_attacks {i : ℕ} {q : List ℕ} :
    s' ∈ attacks I s i q ↔ ∃ dest ∈ reachOf I s.units i, ∃ t, t < I.N ∧ (s.units t).alive ∧
      (s.units t).side = .enemy ∧ Hex.Adj dest (s.units t).hex ∧ s' = sAttack s i q dest t := by
  simp only [attacks, List.mem_flatMap, List.mem_map, mem_reachListOf, mem_targets]
  constructor
  · rintro ⟨dest, hd, t, ⟨h1, h2, h3, h4⟩, rfl⟩; exact ⟨dest, hd, t, h1, h2, h3, h4, rfl⟩
  · rintro ⟨dest, hd, t, h1, h2, h3, h4, rfl⟩; exact ⟨dest, hd, t, ⟨h1, h2, h3, h4⟩, rfl⟩

theorem mem_succsEnd (hq : s.queue = []) : s' ∈ succsEnd I s ↔ Step I s s' := by
  constructor
  · intro h
    simp only [succsEnd, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hp
      · rw [List.mem_singleton] at h; subst h; exact Step.toWait hp hq
      · simp at h
    · split_ifs at h with hp
      · rw [List.mem_singleton] at h; subst h; exact Step.nextRound hp.1 hq hp.2
      · simp at h
  · intro h
    cases h with
    | skip hq' => rw [hq] at hq'; cases hq'
    | enemyWait _ hq' => rw [hq] at hq'; cases hq'
    | enemyDefend _ hq' => rw [hq] at hq'; cases hq'
    | playerWait _ hq' => rw [hq] at hq'; cases hq'
    | playerDefend hq' => rw [hq] at hq'; cases hq'
    | playerMove hq' => rw [hq] at hq'; cases hq'
    | playerAttack hq' => rw [hq] at hq'; cases hq'
    | toWait hp _ => simp [succsEnd, hp, sToWait]
    | nextRound hp _ hr => simp [succsEnd, hp, hr]

/-- **The successor function is exact.** -/
theorem step_iff_mem_succs : Step I s s' ↔ s' ∈ succs I s := by
  rcases hq : s.queue with _ | ⟨i, q⟩
  · simp only [succs, hq]; exact (mem_succsEnd hq).symm
  · simp only [succs, hq]
    constructor
    · intro h
      cases h with
      | skip hq' ha =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp [ha, sSkip]
      | enemyWait hp hq' ha hs =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp [ha, hs, hp, sWait]
      | enemyDefend hp hq' ha hs =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp [ha, hs, hp, sDefend]
      | playerWait hp hq' ha hs =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp [ha, hs, hp, sWait]
      | playerDefend hq' ha hs =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp [ha, hs, sDefend]
      | playerMove hq' ha hs hd =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp only [ha, hs, ↓reduceIte, reduceCtorEq, List.mem_append, List.mem_map,
          mem_reachListOf]
        exact Or.inl (Or.inr ⟨_, hd, rfl⟩)
      | playerAttack hq' ha hs hd ht hta hts hadj =>
        rw [hq] at hq'; injection hq' with e1 e2; subst e1; subst e2
        simp only [ha, hs, ↓reduceIte, reduceCtorEq, List.mem_append]
        exact Or.inr (mem_attacks.mpr ⟨_, hd, _, ht, hta, hts, hadj, rfl⟩)
      | toWait _ hq' => rw [hq] at hq'; cases hq'
      | nextRound _ hq' => rw [hq] at hq'; cases hq'
    · intro h
      by_cases ha : (s.units i).alive
      · rw [if_pos ha] at h
        by_cases hs : (s.units i).side = .enemy
        · rw [if_pos hs] at h
          by_cases hp : s.phase = .normal
          · rw [if_pos hp, List.mem_singleton] at h; subst h
            exact Step.enemyWait hp hq ha hs
          · rw [if_neg hp, List.mem_singleton] at h; subst h
            have hp' : s.phase = .wait := by cases h' : s.phase <;> simp_all
            exact Step.enemyDefend hp' hq ha hs
        · rw [if_neg hs] at h
          have hs' : (s.units i).side = .player := by cases h' : (s.units i).side <;> simp_all
          simp only [List.mem_append, List.mem_map, List.mem_singleton, mem_reachListOf] at h
          rcases h with ((h | h) | ⟨dest, hd, rfl⟩) | h
          · split_ifs at h with hp
            · rw [List.mem_singleton] at h; subst h; exact Step.playerWait hp hq ha hs'
            · simp at h
          · subst h; exact Step.playerDefend hq ha hs'
          · exact Step.playerMove hq ha hs' hd
          · obtain ⟨dest, hd, t, ht, hta, hts, hadj, rfl⟩ := mem_attacks.mp h
            exact Step.playerAttack hq ha hs' hd ht hta hts hadj
      · rw [if_neg ha, List.mem_singleton] at h; subst h
        exact Step.skip hq ha

/-- The attack-only fragment is a sub-relation of `Step`. -/
theorem step_of_mem_succsAO (h : s' ∈ succsAO I s) : Step I s s' := by
  rw [step_iff_mem_succs]
  rcases hq : s.queue with _ | ⟨i, q⟩
  · simp only [succsAO, hq] at h; simpa only [succs, hq] using h
  · simp only [succsAO, hq] at h
    simp only [succs, hq]
    split_ifs at h ⊢ with ha hs hp <;> try exact h
    all_goals
      have key : s' ∈ (reachListOf I s.units i).map (sMove s i q) ∨ s' ∈ attacks I s i q := by
        rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (List.mem_map.mpr ⟨_, mem_reachListOf.mpr (start_mem_reach _ _), rfl⟩)
        · exact Or.inr h
      rcases key with k | k <;> simp [k]

/-! ## Termination and progress -/

def phaseCost (s : State) : ℕ :=
  match s.phase with
  | .normal => 2 * s.queue.length + s.bucket.length + 1
  | .wait => s.queue.length

/-- The termination measure. -/
def μ (I : Instance) (s : State) : ℕ := (s.roundsLeft - 1) * (2 * I.N + 2) + phaseCost s

theorem length_normalQueue (N : ℕ) (us : ℕ → Stack) : (normalQueue N us).length ≤ N := by
  unfold normalQueue
  rw [List.length_mergeSort]
  exact (List.length_filter_le _ _).trans (by simp)

theorem Step.μ_lt (h : Step I s s') : μ I s' < μ I s := by
  cases h with
  | skip hq =>
    unfold μ phaseCost; cases hp : s.phase <;> simp [hq] <;> omega
  | enemyWait hp hq => unfold μ phaseCost; simp [hp, hq]; omega
  | enemyDefend hp hq => unfold μ phaseCost; simp [hp, hq]
  | playerWait hp hq => unfold μ phaseCost; simp [hp, hq]; omega
  | playerDefend hq => unfold μ phaseCost; cases hp : s.phase <;> simp [hq] <;> omega
  | playerMove hq => unfold μ phaseCost; cases hp : s.phase <;> simp [hq] <;> omega
  | playerAttack hq => unfold μ phaseCost; cases hp : s.phase <;> simp [hq] <;> omega
  | toWait hp hq => unfold μ phaseCost; simp [hp, hq, List.length_mergeSort]
  | nextRound hp hq hr =>
    unfold μ phaseCost
    simp only [newRound, hp, hq, List.length_nil, List.length_cons]
    have hL := length_normalQueue I.N (fun i => { s.units i with retal := 1 })
    obtain ⟨r, hr'⟩ : ∃ r, s.roundsLeft = r + 2 := ⟨s.roundsLeft - 2, by omega⟩
    rw [hr', show r + 2 - 1 - 1 = r by omega, show r + 2 - 1 = r + 1 by omega,
      show (r + 1) * (2 * I.N + 2) = r * (2 * I.N + 2) + (2 * I.N + 2) from Nat.succ_mul _ _]
    generalize r * (2 * I.N + 2) = X
    generalize (normalQueue I.N fun i => { s.units i with retal := 1 }).length = L at hL
    omega

instance (s : State) : Decidable (Done s) := by unfold Done; infer_instance

theorem done_of_μ_zero (h : μ I s = 0) : Done s := by
  unfold μ phaseCost at h
  have h2 : 0 < 2 * I.N + 2 := by omega
  cases hp : s.phase <;> rw [hp] at h <;> simp only at h
  · omega
  · refine ⟨hp, List.eq_nil_of_length_eq_zero (by omega), ?_⟩
    by_contra hr
    have : 0 < (s.roundsLeft - 1) * (2 * I.N + 2) := Nat.mul_pos (by omega) h2
    omega

theorem not_step_of_done (hd : Done s) : ¬ Step I s s' := by
  obtain ⟨hp, hq, hr⟩ := hd
  intro h
  cases h with
  | skip hq' => rw [hq] at hq'; cases hq'
  | enemyWait _ hq' => rw [hq] at hq'; cases hq'
  | enemyDefend _ hq' => rw [hq] at hq'; cases hq'
  | playerWait _ hq' => rw [hq] at hq'; cases hq'
  | playerDefend hq' => rw [hq] at hq'; cases hq'
  | playerMove hq' => rw [hq] at hq'; cases hq'
  | playerAttack hq' => rw [hq] at hq'; cases hq'
  | toWait hp' => rw [hp] at hp'; cases hp'
  | nextRound _ _ hr' => omega

theorem succsEnd_ne_nil (hq : s.queue = []) (hd : ¬ Done s) : succsEnd I s ≠ [] := by
  unfold succsEnd
  cases hp : s.phase
  · simp
  · have : 1 < s.roundsLeft := by
      by_contra h; exact hd ⟨hp, hq, by omega⟩
    simp [this]

theorem succs_ne_nil (hd : ¬ Done s) : succs I s ≠ [] := by
  rcases hq : s.queue with _ | ⟨i, q⟩
  · simp only [succs, hq]; exact succsEnd_ne_nil hq hd
  · simp only [succs, hq]; split_ifs <;> simp

theorem succsAO_ne_nil (hd : ¬ Done s) : succsAO I s ≠ [] := by
  rcases hq : s.queue with _ | ⟨i, q⟩
  · simp only [succsAO, hq]; exact succsEnd_ne_nil hq hd
  · simp only [succsAO, hq]; split_ifs <;> simp

/-! ## The search -/

/-- Maximum destroyed value over complete plays from `s` following `next`, with fuel. -/
def bestWith (I : Instance) (next : State → List State) : ℕ → State → ℕ
  | 0, s => destroyed I s
  | f + 1, s => if Done s then destroyed I s else ((next s).map (bestWith I next f)).foldr max 0

theorem le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem foldr_max_mem {l : List ℕ} (hl : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases l with _ | ⟨z, l⟩
    · simp
    · rcases max_choice y (List.foldr max 0 (z :: l)) with h | h <;> rw [h]
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by simp))

theorem eq_of_done {s₀ s₁ : State} (hd : Done s₀) (h : Relation.ReflTransGen (Step I) s₀ s₁) :
    s₁ = s₀ := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · exact h.symm
  · exact absurd hc (not_step_of_done hd)

/-- The search dominates every complete play that follows `Step`, when `next` lists all
successors. -/
theorem le_bestWith {next : State → List State}
    (hc : ∀ s s', Step I s s' → s' ∈ next s) :
    ∀ f s, μ I s ≤ f → ∀ s', Relation.ReflTransGen (Step I) s s' → Done s' →
      destroyed I s' ≤ bestWith I next f s
  | 0, s, hμ, s', h, hd' => by
    rw [eq_of_done (done_of_μ_zero (I := I) (by omega)) h]; exact le_rfl
  | f + 1, s, hμ, s', h, hd' => by
    by_cases hd : Done s
    · rw [eq_of_done hd h]; simp [bestWith, hd]
    · simp only [bestWith, hd, ↓reduceIte]
      rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hsc, hcs⟩
      · exact absurd hd' hd
      · have := le_bestWith hc f c (by have := hsc.μ_lt; omega) s' hcs hd'
        exact this.trans (le_foldr_max (List.mem_map_of_mem (hc _ _ hsc)))

/-- The search value is attained by a complete play, when `next` lists only successors and
never gets stuck before the end. -/
theorem bestWith_attained {next : State → List State}
    (hs : ∀ s s', s' ∈ next s → Step I s s') (hp : ∀ s, ¬ Done s → next s ≠ []) :
    ∀ f s, μ I s ≤ f → ∃ s', Relation.ReflTransGen (Step I) s s' ∧ Done s' ∧
      destroyed I s' = bestWith I next f s
  | 0, s, hμ => ⟨s, .refl, done_of_μ_zero (I := I) (by omega), rfl⟩
  | f + 1, s, hμ => by
    by_cases hd : Done s
    · exact ⟨s, .refl, hd, by simp [bestWith, hd]⟩
    · simp only [bestWith, hd, ↓reduceIte]
      have hne : (next s).map (bestWith I next f) ≠ [] := by simpa using hp s hd
      obtain ⟨c, hc, hceq⟩ := List.mem_map.mp (foldr_max_mem hne)
      have hstep := hs _ _ hc
      obtain ⟨s', h', hd', he⟩ := bestWith_attained hs hp f c (by have := hstep.μ_lt; omega)
      exact ⟨s', Relation.ReflTransGen.head hstep h', hd', by rw [he, hceq]⟩

/-! ## Values of an allocation -/

/-- The optimum over all plays from the start of `α`. -/
def value (I : Instance) (α : ℕ → SlotAlloc) : ℕ :=
  bestWith I (succs I) (μ I (initState I α)) (initState I α)

/-- The optimum over the attack-only fragment. -/
def valueAO (I : Instance) (α : ℕ → SlotAlloc) : ℕ :=
  bestWith I (succsAO I) (μ I (initState I α)) (initState I α)

variable {α : ℕ → SlotAlloc}

theorem le_value {s : State} (h : Reach I α s) (hd : Done s) : destroyed I s ≤ value I α :=
  le_bestWith (fun _ _ h => step_iff_mem_succs.mp h) _ _ le_rfl s h hd

theorem value_attained : ∃ s, Reach I α s ∧ Done s ∧ destroyed I s = value I α :=
  bestWith_attained (fun _ _ h => step_iff_mem_succs.mpr h) (fun _ h => succs_ne_nil h) _ _ le_rfl

theorem valueAO_attained : ∃ s, Reach I α s ∧ Done s ∧ destroyed I s = valueAO I α :=
  bestWith_attained (fun _ _ h => step_of_mem_succsAO h) (fun _ h => succsAO_ne_nil h) _ _ le_rfl

theorem valueAO_le_value : valueAO I α ≤ value I α := by
  obtain ⟨s, h, hd, he⟩ := valueAO_attained (I := I) (α := α)
  rw [← he]; exact le_value h hd

/-! ## Allocations -/

/-- The choices for one slot: empty, or `(type t, count c)` with `1 ≤ c ≤ stock t`. -/
def slotChoices (I : Instance) : List SlotAlloc :=
  ⟨0, 0⟩ :: (List.range I.army.length).flatMap
    (fun t => (List.range (I.army.getD t default).2).map (fun c => ⟨t, c + 1⟩))

def toAlloc (l : List SlotAlloc) (j : ℕ) : SlotAlloc := l.getD j ⟨0, 0⟩

instance (I : Instance) : DecidablePred (Feasible I) := by
  intro α; unfold Feasible; infer_instance

/-- The feasible allocations, up to what `initUnits` reads. -/
def allocs (I : Instance) : List (ℕ → SlotAlloc) :=
  (((List.replicate I.k (slotChoices I)).sections).filter
    (fun l => decide (Feasible I (toAlloc l)))).map toAlloc

theorem feasible_of_mem_allocs {α : ℕ → SlotAlloc} (h : α ∈ allocs I) : Feasible I α := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
  exact of_decide_eq_true (List.mem_filter.mp hl).2

/-- Empty slots normalized to `⟨0, 0⟩`. -/
def normA (a : SlotAlloc) : SlotAlloc := if a.count = 0 then ⟨0, 0⟩ else a

theorem normA_count (a : SlotAlloc) : (normA a).count = a.count := by
  unfold normA; split_ifs <;> simp_all

theorem initUnits_congr {α β : ℕ → SlotAlloc} (h : ∀ j < I.k, normA (α j) = normA (β j)) :
    initUnits I α = initUnits I β := by
  funext i
  by_cases hi : i < I.k
  · rw [initUnits_player hi, initUnits_player hi]
    have hc : (α i).count = (β i).count := by
      have := congrArg SlotAlloc.count (h i hi); rwa [normA_count, normA_count] at this
    have ht : I.slotType α i = I.slotType β i := by
      unfold Instance.slotType
      by_cases h0 : 0 < (α i).count
      · have : α i = β i := by
          have := h i hi; unfold normA at this
          rwa [if_neg (by omega), if_neg (by omega)] at this
        rw [this]
      · rw [if_neg h0, if_neg (by omega)]
    rw [hc, ht]
  · unfold initUnits; rw [if_neg hi, if_neg hi]

theorem sum_ite_le_stock {α : ℕ → SlotAlloc} (hα : Feasible I α) {j t : ℕ} (hj : j < I.k)
    (ht : (α j).type = t) (htl : t < I.army.length) : (α j).count ≤ (I.army.getD t default).2 := by
  refine le_trans ?_ (hα.2 t htl)
  exact Finset.single_le_sum (f := fun j => (α j).count) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ht⟩)

theorem normA_mem_slotChoices (hα : Feasible I α) {j : ℕ} (hj : j < I.k) :
    normA (α j) ∈ slotChoices I := by
  unfold normA slotChoices
  split_ifs with hc
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(α j).type, ?_, ?_⟩)
    · exact List.mem_range.mpr (hα.1 j hj (by omega))
    · refine List.mem_map.mpr ⟨(α j).count - 1, List.mem_range.mpr ?_, ?_⟩
      · have := sum_ite_le_stock hα hj rfl (hα.1 j hj (by omega)); omega
      · rcases h : α j with ⟨t, c⟩
        rw [h] at hc; simp only at hc ⊢; congr 1; omega

/-- **Every feasible allocation has the starting position of one in `allocs`.** -/
theorem exists_mem_allocs (hα : Feasible I α) :
    ∃ β ∈ allocs I, initState I β = initState I α := by
  set l := (List.range I.k).map (fun j => normA (α j)) with hl
  have hget : ∀ j < I.k, toAlloc l j = normA (α j) := by
    intro j hj; simp [toAlloc, hl, List.getD_eq_getElem?_getD, hj]
  have hnorm : ∀ j < I.k, normA (toAlloc l j) = normA (α j) := by
    intro j hj; rw [hget j hj]; unfold normA; split_ifs <;> simp_all
  have hinit : initUnits I (toAlloc l) = initUnits I α := initUnits_congr hnorm
  refine ⟨toAlloc l, List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · rw [List.mem_sections]
    rw [List.forall₂_iff_get]
    refine ⟨by simp [hl], fun n h1 h2 => ?_⟩
    simp only [hl, List.length_map, List.length_range] at h1
    simp only [hl, List.get_eq_getElem, List.getElem_map, List.getElem_range,
      List.getElem_replicate]
    exact normA_mem_slotChoices hα h1
  · apply decide_eq_true
    refine ⟨fun j hj hc => ?_, fun t ht => le_trans ?_ (hα.2 t ht)⟩
    · rw [hget j hj] at hc ⊢
      unfold normA at hc ⊢
      split_ifs at hc ⊢ with h0
      · simp at hc
      · exact hα.1 j hj (by omega)
    · rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro j hj
      rw [hget j (Finset.mem_range.mp hj)]
      unfold normA
      split_ifs <;> simp_all
  · simp only [initState, hinit]

theorem mem_allocs_zero : ∃ β ∈ allocs I, True := by
  obtain ⟨β, hβ, -⟩ := exists_mem_allocs (I := I) (α := fun _ => ⟨0, 0⟩)
    ⟨fun _ _ h => absurd h (by simp), fun _ _ => by simp⟩
  exact ⟨β, hβ, trivial⟩

/-! ## The decision procedure -/

/-- The optimum destroyed value of the instance. -/
def optimum (I : Instance) : ℕ := ((allocs I).map (value I)).foldr max 0

/-- **`ARMY-ALLOCATION` is decided by the executable optimum**, on every instance. -/
theorem armyAllocation_iff : ArmyAllocation I ↔ I.W ≤ optimum I := by
  constructor
  · rintro ⟨α, hα, s, hs, hd, hW⟩
    obtain ⟨β, hβ, he⟩ := exists_mem_allocs hα
    have hs' : Reach I β s := by simp only [Reach]; rw [he]; exact hs
    have := le_value hs' hd
    exact hW.trans (this.trans (le_foldr_max (List.mem_map_of_mem hβ)))
  · intro hW
    obtain ⟨β0, hβ0, -⟩ := mem_allocs_zero (I := I)
    have hne : (allocs I).map (value I) ≠ [] := by simpa using List.ne_nil_of_mem hβ0
    obtain ⟨β, hβ, hv⟩ := List.mem_map.mp (foldr_max_mem hne)
    obtain ⟨s, hs, hd, he⟩ := value_attained (I := I) (α := β)
    exact ⟨β, feasible_of_mem_allocs hβ, s, hs, hd, by rw [he, hv]; exact hW⟩

instance (I : Instance) : Decidable (ArmyAllocation I) :=
  decidable_of_iff _ armyAllocation_iff.symm

/-- The attack-only optimum over a given list of feasible allocations is attained by a genuine
play; so `W ≤` it certifies a yes-instance. -/
theorem armyAllocation_of_AO {L : List (ℕ → SlotAlloc)} (hL : ∀ α ∈ L, Feasible I α)
    (hW : I.W ≤ (L.map (valueAO I)).foldr max 0) (hne : L ≠ []) : ArmyAllocation I := by
  have hne' : L.map (valueAO I) ≠ [] := by simpa using hne
  obtain ⟨β, hβ, hv⟩ := List.mem_map.mp (foldr_max_mem hne')
  obtain ⟨s, hs, hd, he⟩ := valueAO_attained (I := I) (α := β)
  exact ⟨β, hL β hβ, s, hs, hd, by rw [he, hv]; exact hW⟩

end Homm3
