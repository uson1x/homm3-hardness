import Homm3.Prop11Lower

/-!
# Stage 5. Proposition 1.1 (packaged) and Theorem 1 as an equivalence

* `prop11_opt`: on the corridor family the optimum over all feasible allocations and all
  plays is exactly `dp = OPT` of the knapsack `(K)`, with thresholds `⌈t_j/d⌉`.
* `prop11_decide`: hence `ARMY-ALLOCATION` on the family is decided by `W ≤ dp`.
* `theorem1`: `PARTITION a ↔ ARMY-ALLOCATION (G a)` for positive `a` with even sum.
* `theorem1_total`: the paper's total reduction (Appendix E, Theorem 1, "Totality")
  on integer lists: `G_no` for a nonpositive entry or an odd sum, `G((1,1))` for the empty
  list, `G(a)` otherwise.

NP-hardness of PARTITION, membership in NP and polynomial running time of the map are
outside the pilot: no axioms are introduced, only the equivalences are proved.
-/

namespace Homm3.Corridor

variable {n : ℕ} {t v : ℕ → ℕ} {d B W : ℕ}

/-- **Proposition 1.1** (corridor family): the optimum destroyed value is `dp = OPT`. -/
theorem prop11_opt (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) :
    (∀ α, Feasible (inst n t v d B W) α → ∀ s,
        Relation.ReflTransGen (Step (inst n t v d B W)) (initState (inst n t v d B W) α) s →
        destroyed (inst n t v d B W) s ≤ Knapsack.dp v (thr t d) n B) ∧
    ∃ α, Feasible (inst n t v d B W) α ∧ ∃ s,
      Relation.ReflTransGen (Step (inst n t v d B W)) (initState (inst n t v d B W) α) s ∧
      Done s ∧ destroyed (inst n t v d B W) s = Knapsack.dp v (thr t d) n B := by
  refine ⟨fun α hα s hs => (Knapsack.dp_eq_OPT n B).symm ▸ upper hd ht hα hs, ?_⟩
  obtain ⟨S, hS, hSv⟩ := Knapsack.OPT_attained (v := v) (b := thr t d) n B
  obtain ⟨α, hα, s, hs, hdone, hle⟩ := lower (v := v) (W := W) hd ht hS
  refine ⟨α, hα, s, hs, hdone, le_antisymm ?_ ?_⟩
  · rw [Knapsack.dp_eq_OPT]; exact upper hd ht hα hs
  · rw [Knapsack.dp_eq_OPT, ← hSv]; exact hle

/-- **Proposition 1.1, decision form**: `ARMY-ALLOCATION` on the corridor family is
decided by the knapsack dynamic program. -/
theorem prop11_decide (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) :
    ArmyAllocation (inst n t v d B W) ↔ W ≤ Knapsack.dp v (thr t d) n B := by
  constructor
  · rintro ⟨α, hα, s, hs, -, hW⟩
    exact hW.trans ((prop11_opt (W := W) hd ht).1 α hα s hs)
  · intro hW
    obtain ⟨α, hα, s, hs, hdone, heq⟩ := (prop11_opt (v := v) (W := W) hd ht).2
    exact ⟨α, hα, s, hs, hdone, heq ▸ hW⟩

/-! ## Theorem 1 -/

/-- `PARTITION` (positive integers are required separately): some subset has exactly half
the total.  Stated as `2 · Σ_S a = Σ a`, which is also correct for odd totals; the
truncating form `Σ_S a = Σ a / 2` would accept e.g. `a = (1, 2)`. -/
def PARTITION (a : List ℕ) : Prop :=
  ∃ S ⊆ Finset.range a.length, 2 * ∑ j ∈ S, a.getD j 0 = a.sum

/-- The instance `G(a)`: `t = v = a`, `d = 1`, stock and target `B = Σ a / 2`. -/
def G (a : List ℕ) : Instance :=
  inst a.length (fun j => a.getD j 0) (fun j => a.getD j 0) 1 (a.sum / 2) (a.sum / 2)

theorem thr_one (t : ℕ → ℕ) (j : ℕ) : thr t 1 j = t j := by simp [thr]

theorem sum_range_getD (a : List ℕ) : ∑ j ∈ Finset.range a.length, a.getD j 0 = a.sum := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    ring

/-- **Theorem 1** (the equivalence): for positive `a` with even sum,
`PARTITION a ↔ ARMY-ALLOCATION (G a)`.  (No `n ≥ 1` is needed for the equivalence; the
paper needs it only so that `W = B ∈ ℤ_{>0}` is a legal target.) -/
theorem theorem1 (a : List ℕ) (hpos : ∀ x ∈ a, 0 < x) (heven : Even a.sum) :
    PARTITION a ↔ ArmyAllocation (G a) := by
  have ht : ∀ j < a.length, 1 ≤ a.getD j 0 := by
    intro j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact hpos _ (List.getElem_mem hj)
  unfold G
  rw [prop11_decide le_rfl ht, Knapsack.dp_eq_OPT]
  obtain ⟨B, hB⟩ := heven
  have hB2 : a.sum / 2 = B := by omega
  rw [hB2]
  have hthr : thr (fun j => a.getD j 0) 1 = fun j => a.getD j 0 := funext (thr_one _)
  rw [hthr]
  constructor
  · rintro ⟨S, hS, hsum⟩
    have hsumB : ∑ j ∈ S, a.getD j 0 = B := by omega
    exact hsumB.symm.le.trans (Knapsack.le_OPT (Knapsack.mem_feasible.mpr ⟨hS, hsumB.le⟩))
  · intro hle
    obtain ⟨S, hS, hSv⟩ := Knapsack.OPT_attained (v := fun j => a.getD j 0)
      (b := fun j => a.getD j 0) a.length B
    obtain ⟨hSsub, hSw⟩ := Knapsack.mem_feasible.mp hS
    refine ⟨S, hSsub, ?_⟩
    omega

/-! ## The total reduction -/

/-- The fixed no-instance `G_no` of Lemma D.4: a `1 × 1` board, one slot, one creature of
stock one, no enemies, `W = 1`. -/
def Gno : Instance where
  width := 1
  height := 1
  obstacles := ∅
  slots := [⟨0, 0⟩]
  army := [(⟨1, 1, 1, 1, 1, 0⟩, 1)]
  enemies := []
  R := 1
  W := 1

theorem Gno_no : ¬ ArmyAllocation Gno := by
  rintro ⟨α, -, s, hs, -, hW⟩
  -- the only stack is the player's; its side never changes, so nothing is destroyed
  have hside : (s.units 0).side = .player := by
    have key : ∀ s', Relation.ReflTransGen (Step Gno) (initState Gno α) s' →
        (s'.units 0).side = .player := by
      intro s' h
      induction h with
      | refl => simp [initState, initUnits, Instance.k, Gno]
      | tail _ h ih => rw [h.side]; exact ih
    exact key s hs
  have : destroyed Gno s = 0 := by
    simp [destroyed, Instance.N, Instance.k, Instance.n, Gno, hside]
  have h1 : Gno.W = 1 := rfl
  omega

/-- `PARTITION` over integer encodings: every entry positive and some subset has exactly
half the total. -/
def PARTITIONℤ (a : List ℤ) : Prop :=
  (∀ x ∈ a, 0 < x) ∧ ∃ S ⊆ Finset.range a.length, 2 * ∑ j ∈ S, a.getD j 0 = a.sum

/-- The total reduction of Appendix E ("Totality"). -/
def reduction (a : List ℤ) : Instance :=
  if (∀ x ∈ a, 0 < x) ∧ Even a.sum then
    if a = [] then G [1, 1] else G (a.map Int.toNat)
  else Gno

theorem PARTITION_one_one : PARTITION [1, 1] :=
  ⟨{0}, by simp, by simp⟩

theorem sum_map_toNat {a : List ℤ} (h : ∀ x ∈ a, 0 ≤ x) :
    ((a.map Int.toNat).sum : ℤ) = a.sum := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.forall_mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add, ih h.2, Int.toNat_of_nonneg h.1]

theorem partition_map_toNat {a : List ℤ} (hpos : ∀ x ∈ a, 0 < x) :
    PARTITIONℤ a ↔ PARTITION (a.map Int.toNat) := by
  have hget : ∀ j, ((a.map Int.toNat).getD j 0 : ℤ) = a.getD j 0 := by
    intro j
    by_cases hj : j < a.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
      simp only [List.getElem_map]
      exact Int.toNat_of_nonneg (le_of_lt (hpos _ (List.getElem_mem hj)))
    · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]
      rfl
  have hsum := sum_map_toNat (fun x hx => le_of_lt (hpos x hx))
  have key : ∀ S : Finset ℕ, ((2 * ∑ j ∈ S, (a.map Int.toNat).getD j 0 : ℕ) : ℤ) =
      2 * ∑ j ∈ S, a.getD j 0 := by
    intro S; push_cast; simp only [hget]
  unfold PARTITIONℤ PARTITION
  simp only [List.length_map]
  constructor
  · rintro ⟨-, S, hS, h⟩
    refine ⟨S, hS, ?_⟩
    have := key S
    rw [h, ← hsum] at this
    exact_mod_cast this
  · rintro ⟨S, hS, h⟩
    refine ⟨hpos, S, hS, ?_⟩
    rw [← key S, h, hsum]

/-- **Theorem 1, total form**: the reduction of Appendix E is correct on every integer
list. -/
theorem theorem1_total (a : List ℤ) : PARTITIONℤ a ↔ ArmyAllocation (reduction a) := by
  unfold reduction
  split_ifs with hgood hnil
  · subst hnil
    have h1 : ArmyAllocation (G [1, 1]) :=
      (theorem1 [1, 1] (by simp) ⟨1, rfl⟩).mp PARTITION_one_one
    exact ⟨fun _ => h1, fun _ => ⟨by simp, ∅, by simp, by simp⟩⟩
  · have hnn : ∀ x ∈ a, 0 ≤ x := fun x hx => le_of_lt (hgood.1 x hx)
    have hposN : ∀ x ∈ a.map Int.toNat, 0 < x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hgood.1 y hy
      omega
    have hevenN : Even (a.map Int.toNat).sum := by
      rw [← Int.even_coe_nat, sum_map_toNat hnn]; exact hgood.2
    rw [partition_map_toNat hgood.1]
    exact theorem1 _ hposN hevenN
  · refine ⟨fun h => absurd ⟨h.1, ?_⟩ hgood, fun h => absurd h Gno_no⟩
    obtain ⟨S, -, hS⟩ := h.2
    exact ⟨∑ j ∈ S, a.getD j 0, by rw [← hS]; ring⟩

end Homm3.Corridor
