import Mathlib

/-!
# Stage 3a. The 0-1 knapsack optimum `(K)` and the dynamic program

Source of truth: `homm3/paper/main.md` Appendix E, proof of Proposition 1.1, display `(K)`;
`homm3/scripts/dp_single_type.py`, function `dp`.

Items are indexed `0, …, k−1` with values `v j` and weights (thresholds) `b j`.

`dp_single_type.dp` keeps one budget row and updates it in place in *descending* capacity
order, so that `best[cap − b]` is still the previous row's value when `best[cap]` is
written; the row after item `j` is therefore exactly
`cap ↦ if b_j ≤ cap then max(best cap, v_j + best (cap − b_j)) else best cap`, which is the
recurrence `dp` below.  The array-level in-place loop itself is not formalized.
-/

namespace Homm3.Knapsack

variable (v b : ℕ → ℕ)

/-- Subsets of the first `k` items whose total weight is at most `B`. -/
def feasible (k B : ℕ) : Finset (Finset ℕ) :=
  (Finset.range k).powerset.filter (fun S => ∑ j ∈ S, b j ≤ B)

/-- `(K)`: `OPT = max{ Σ_{j∈S} v_j : S ⊆ [k], Σ_{j∈S} b_j ≤ B }`. -/
def OPT (k B : ℕ) : ℕ := (feasible b k B).sup (fun S => ∑ j ∈ S, v j)

/-- The textbook dynamic program over (item prefix, capacity). -/
def dp : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, cap => if b k ≤ cap then max (dp k cap) (v k + dp k (cap - b k)) else dp k cap

variable {v b}

theorem mem_feasible {k B : ℕ} {S : Finset ℕ} :
    S ∈ feasible b k B ↔ S ⊆ Finset.range k ∧ ∑ j ∈ S, b j ≤ B := by
  simp [feasible]

/-- Every feasible subset is dominated by the DP value. -/
theorem le_dp : ∀ (k cap : ℕ) (S : Finset ℕ), S ∈ feasible b k cap →
    ∑ j ∈ S, v j ≤ dp v b k cap
  | 0, cap, S, hS => by
    rw [mem_feasible] at hS
    have : S = ∅ := by simpa using hS.1
    simp [this, dp]
  | k + 1, cap, S, hS => by
    rw [mem_feasible] at hS
    obtain ⟨hsub, hw⟩ := hS
    by_cases hk : k ∈ S
    · -- `S = insert k S'` with `S' ⊆ range k`
      set S' := S.erase k with hS'
      have hS'sub : S' ⊆ Finset.range k := by
        intro j hj
        rw [Finset.mem_erase] at hj
        have := Finset.mem_range.mp (hsub hj.2)
        exact Finset.mem_range.mpr (by omega)
      have hb : b k + ∑ j ∈ S', b j = ∑ j ∈ S, b j := Finset.add_sum_erase S b hk
      have hv : v k + ∑ j ∈ S', v j = ∑ j ∈ S, v j := Finset.add_sum_erase S v hk
      have hbk : b k ≤ cap := by omega
      have ih := le_dp k (cap - b k) S' (mem_feasible.mpr ⟨hS'sub, by omega⟩)
      simp only [dp, hbk, ↓reduceIte]
      rw [← hv]
      exact le_trans (by omega) (le_max_right _ _)
    · have hS'sub : S ⊆ Finset.range k := by
        intro j hj
        have := Finset.mem_range.mp (hsub hj)
        have : j ≠ k := fun h => hk (h ▸ hj)
        exact Finset.mem_range.mpr (by omega)
      have ih := le_dp k cap S (mem_feasible.mpr ⟨hS'sub, hw⟩)
      simp only [dp]
      split_ifs
      · exact le_trans ih (le_max_left _ _)
      · exact ih

/-- The DP value is attained by a feasible subset. -/
theorem dp_attained : ∀ (k cap : ℕ), ∃ S ∈ feasible b k cap, ∑ j ∈ S, v j = dp v b k cap
  | 0, cap => ⟨∅, by simp [mem_feasible], by simp [dp]⟩
  | k + 1, cap => by
    have lift : ∀ {S : Finset ℕ} {c : ℕ}, S ∈ feasible b k c → S ⊆ Finset.range (k + 1) :=
      fun h => (mem_feasible.mp h).1.trans (Finset.range_subset_range.mpr (Nat.le_succ k))
    obtain ⟨S₁, h₁, e₁⟩ := dp_attained k cap
    by_cases hbk : b k ≤ cap
    · obtain ⟨S₂, h₂, e₂⟩ := dp_attained k (cap - b k)
      have hkS₂ : k ∉ S₂ := fun h => by
        have := Finset.mem_range.mp ((mem_feasible.mp h₂).1 h); omega
      simp only [dp, hbk, ↓reduceIte]
      rcases le_total (dp v b k cap) (v k + dp v b k (cap - b k)) with hle | hle
      · refine ⟨insert k S₂, mem_feasible.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Finset.insert_subset (Finset.mem_range.mpr (Nat.lt_succ_self k)) (lift h₂)
        · rw [Finset.sum_insert hkS₂]; have := (mem_feasible.mp h₂).2; omega
        · rw [Finset.sum_insert hkS₂, e₂, max_eq_right hle]
      · exact ⟨S₁, mem_feasible.mpr ⟨lift h₁, (mem_feasible.mp h₁).2⟩,
          by rw [e₁, max_eq_left hle]⟩
    · simp only [dp, hbk, ↓reduceIte]
      exact ⟨S₁, mem_feasible.mpr ⟨lift h₁, (mem_feasible.mp h₁).2⟩, e₁⟩

/-- **The DP is correct:** `dp = max{Σ v_j : Σ b_j ≤ B}`. -/
theorem dp_eq_OPT (k B : ℕ) : dp v b k B = OPT v b k B := by
  apply le_antisymm
  · obtain ⟨S, hS, e⟩ := dp_attained (v := v) (b := b) k B
    rw [← e]; exact Finset.le_sup (f := fun S => ∑ j ∈ S, v j) hS
  · exact Finset.sup_le fun S hS => le_dp k B S hS

/-- `OPT` is attained. -/
theorem OPT_attained (k B : ℕ) : ∃ S ∈ feasible b k B, ∑ j ∈ S, v j = OPT v b k B := by
  rw [← dp_eq_OPT]; exact dp_attained k B

theorem le_OPT {k B : ℕ} {S : Finset ℕ} (h : S ∈ feasible b k B) :
    ∑ j ∈ S, v j ≤ OPT v b k B :=
  Finset.le_sup (f := fun S => ∑ j ∈ S, v j) h

/-- A tiny sanity check, the Prop 1.1 "persistent reach" counter-example numbers:
`b = (1, 1)`, `v = (1, 1)`, `B = 2` gives `2`. -/
example : dp (fun _ => 1) (fun _ => 1) 2 2 = 2 := by decide

end Homm3.Knapsack
