import Homm3.Hex

/-!
# Stage 3b. The corridor geometry of `G(a)` and Lemma E.4

Source of truth: `homm3/paper/main.md` Appendix E, "The instance `G(a)`" and Lemma E.4;
`homm3/scripts/brute_force.py`, `build_partition_instance`.

Slots are indexed from `0` here (the paper indexes from `1`): slot `j` deploys on
`p j = (5j, 0)` and its enemy stands on `e j = (5j + 1, 0)`.  Row `0` is even.
-/

namespace Homm3.Corridor

open Hex

/-- Deployment hex of slot `j` (paper: `p_{j+1} = 5j`). -/
def p (j : ℕ) : Hex := ⟨5 * j, 0⟩

/-- Hex of enemy `j` (paper: `e_{j+1} = 5j + 1`). -/
def e (j : ℕ) : Hex := ⟨5 * j + 1, 0⟩

theorem adj_p_e (j : ℕ) : Adj (p j) (e j) := by
  simp [Adj, nbrs, p, e]

/-- **Lemma E.4**, the formula: `dist(p_j, e_{j'}) = |5(j − j') − 1|`. -/
theorem dist_p_e (j j' : ℕ) : dist (p j) (e j') = |5 * ((j : ℤ) - j') - 1| := by
  rw [p, e, dist_row, ← abs_neg]; congr 1; ring

/-- **Lemma E.4**, part 1: `dist(p_j, e_j) = 1`. -/
theorem dist_p_e_self (j : ℕ) : dist (p j) (e j) = 1 := by
  rw [dist_p_e]; norm_num

/-- **Lemma E.4**, part 2: `dist(p_j, e_{j'}) ≥ 4` for `j ≠ j'`. -/
theorem dist_p_e_ne {j j' : ℕ} (h : j ≠ j') : 4 ≤ dist (p j) (e j') := by
  rw [dist_p_e]
  rcases lt_or_gt_of_ne h with h | h
  · have : (j : ℤ) + 1 ≤ j' := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith
  · have : (j' : ℤ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith

/-- The tight margin of the remark after Lemma E.4: the minimum `4` is attained backward,
the forward gap is `6`. -/
theorem dist_backward (j : ℕ) : dist (p (j + 1)) (e j) = 4 := by
  rw [dist_p_e]; push_cast; norm_num

theorem dist_forward (j : ℕ) : dist (p j) (e (j + 1)) = 6 := by
  rw [dist_p_e]; push_cast; norm_num

/-- Block width 4 would be too narrow: the backward gap drops to `3 = spd + 1`. -/
example (j : ℕ) : Hex.dist ⟨4 * (j + 1 : ℤ), 0⟩ ⟨4 * j + 1, 0⟩ = 3 := by
  rw [dist_row]; norm_num; ring_nf; norm_num

/-- **Lemma E.4 + E.3 combined (the metric test of Lemma E.9, hypothesis 2):** a stack of
speed `2` on `p j` can strike no enemy hex `e j'` with `j' ≠ j`, whatever hexes are free. -/
theorem no_foreign_strike {free : Hex → Prop} [DecidablePred free] {j j' : ℕ} {h : Hex}
    (hh : h ∈ reach free (p j) 2) (hz : Adj h (e j')) : j' = j := by
  by_contra hne
  have h1 := strike_radius (p j) 2 hh hz
  have h2 := dist_p_e_ne (Ne.symm hne)
  push_cast at h1
  linarith

end Homm3.Corridor
