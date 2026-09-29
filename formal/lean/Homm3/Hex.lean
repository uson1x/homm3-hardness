import Mathlib

/-!
# Stage 1. Hexes, adjacency (R1), distance (R2), BFS reach (R11)

Source of truth: `homm3/MODEL.md` §2, `homm3/paper/main.md` Appendix E "Conventions"
and Lemma E.3, `homm3/scripts/homm3_model.py` (`Battlefield.neighbours`,
`Battlefield.distance`, `Battle.reachable`).

Hexes live in `ℤ × ℤ` (column `x`, row `y`); a board is a predicate cutting out the
`width × height` rectangle.  Working on all of `ℤ²` costs nothing: the neighbour rule is
the same, and a walk on the board is in particular a walk on `ℤ²`.
-/

namespace Homm3

/-- A hex in offset coordinates: column `x`, row `y`. -/
@[ext] structure Hex where
  x : ℤ
  y : ℤ
deriving DecidableEq, Repr

namespace Hex

/-- The six R1 neighbours (`homm3_model.py`, `Battlefield.neighbours`), with
`ε := y mod 2`: from an even row the upper/lower neighbours sit at columns `x, x+1`,
from an odd row at `x-1, x`. -/
def nbrs (h : Hex) : List Hex :=
  let ε := h.y % 2
  [⟨h.x - 1, h.y⟩, ⟨h.x + 1, h.y⟩,
   ⟨h.x - ε, h.y - 1⟩, ⟨h.x + 1 - ε, h.y - 1⟩,
   ⟨h.x - ε, h.y + 1⟩, ⟨h.x + 1 - ε, h.y + 1⟩]

/-- R1 adjacency. -/
def Adj (p q : Hex) : Prop := q ∈ p.nbrs

instance : DecidableRel Adj := fun p q => inferInstanceAs (Decidable (q ∈ p.nbrs))

/-- Axial column `A(x, y) = x + ⌊y/2⌋` (Lean's `Int` division by `2` is floor division). -/
def axial (h : Hex) : ℤ := h.x + h.y / 2

/-- The R2 gauge of a displacement `(δA, δy)`, transcribed literally from
`Battlefield.distance`: `max` when the signs agree, the sum otherwise. -/
def gauge (a b : ℤ) : ℤ :=
  if (0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0) then max |a| |b| else |a| + |b|

/-- R2 distance. -/
def dist (p q : Hex) : ℤ := gauge (q.axial - p.axial) (q.y - p.y)

/-- The gauge in closed form: the hexagonal norm `max(|a|, |b|, |a - b|)`. -/
theorem gauge_eq (a b : ℤ) : gauge a b = max (max |a| |b|) |a - b| := by
  unfold gauge
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> omega

theorem gauge_nonneg (a b : ℤ) : 0 ≤ gauge a b := by
  rw [gauge_eq]; exact le_trans (abs_nonneg a) (le_trans (le_max_left _ _) (le_max_left _ _))

/-- The gauge is subadditive (it is a norm). -/
theorem gauge_add (a b c d : ℤ) : gauge (a + c) (b + d) ≤ gauge a b + gauge c d := by
  rw [gauge_eq, gauge_eq, gauge_eq]
  have h1 := abs_add_le a c
  have h2 := abs_add_le b d
  have h3 := abs_add_le (a - b) (c - d)
  have e : a + c - (b + d) = (a - b) + (c - d) := by ring
  rw [e]
  refine max_le (max_le ?_ ?_) ?_
  · exact le_trans h1 (add_le_add (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  · exact le_trans h2 (add_le_add (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_left _ _)))
  · exact le_trans h3 (add_le_add (le_max_right _ _) (le_max_right _ _))

theorem dist_self (p : Hex) : dist p p = 0 := by simp [dist, gauge]

theorem dist_nonneg (p q : Hex) : 0 ≤ dist p q := gauge_nonneg _ _

/-- Triangle inequality for R2. -/
theorem dist_triangle (p q r : Hex) : dist p r ≤ dist p q + dist q r := by
  unfold dist
  have := gauge_add (q.axial - p.axial) (q.y - p.y) (r.axial - q.axial) (r.y - q.y)
  have e1 : q.axial - p.axial + (r.axial - q.axial) = r.axial - p.axial := by ring
  have e2 : q.y - p.y + (r.y - q.y) = r.y - p.y := by ring
  rwa [e1, e2] at this

/-- In axial coordinates every R1 step is one of `±(1,0), ±(0,1), ±(1,1)`, in both row
parities; hence every step has gauge exactly `1`. -/
theorem dist_of_adj {p q : Hex} (h : Adj p q) : dist p q = 1 := by
  simp only [Adj, nbrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases p with ⟨x, y⟩
  have e1 : (y - 1) / 2 = y / 2 - 1 + y % 2 := by omega
  have e2 : (y + 1) / 2 = y / 2 + y % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [dist, gauge_eq, axial, e1, e2, hy] <;> ring_nf <;> norm_num

theorem adj_symm {p q : Hex} (h : Adj p q) : Adj q p := by
  simp only [Adj, nbrs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases p with ⟨x, y⟩
  rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Hex.mk.injEq, and_true] <;> omega

/-- On a single row (`y = 0`) the R2 distance degenerates to `|δx|`. -/
theorem dist_row (x₁ x₂ : ℤ) : dist ⟨x₁, 0⟩ ⟨x₂, 0⟩ = |x₂ - x₁| := by
  simp only [dist, gauge_eq, axial]
  norm_num

end Hex

/-! ## BFS reach over free hexes -/

/-- Layered BFS (`Battle.reachable`): `reach free p 0 = {p}`, and layer `s+1` adds every
free neighbour of layer `s`.  `free` is the set of enterable hexes of the current
position (on the board, not an obstacle, not occupied by a living unit); the start hex
itself need not be free (the stack stands on it). -/
def reach (free : Hex → Prop) [DecidablePred free] (p : Hex) : ℕ → Finset Hex
  | 0 => {p}
  | s + 1 =>
    let r := reach free p s
    r ∪ r.biUnion (fun h => (h.nbrs.filter (fun q => decide (free q))).toFinset)

variable {free : Hex → Prop} [DecidablePred free]

theorem start_mem_reach (p : Hex) : ∀ s, p ∈ reach free p s
  | 0 => by simp [reach]
  | s + 1 => by
    simp only [reach, Finset.mem_union]; exact Or.inl (start_mem_reach p s)

theorem reach_mono (p : Hex) {s t : ℕ} (h : s ≤ t) : reach free p s ⊆ reach free p t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by intro q hq; simp only [reach, Finset.mem_union]; exact Or.inl hq)

/-- **Lemma E.3, metric half.** Whatever hexes are free, BFS reach within `s` steps stays
within R2 distance `s`. -/
theorem dist_le_of_mem_reach (p : Hex) : ∀ (s : ℕ) (q : Hex), q ∈ reach free p s →
    Hex.dist p q ≤ s
  | 0, q, hq => by
    simp only [reach, Finset.mem_singleton] at hq; subst hq; simp [Hex.dist_self]
  | s + 1, q, hq => by
    simp only [reach, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      List.mem_filter] at hq
    rcases hq with hq | ⟨h, hh, hq, _⟩
    · have := dist_le_of_mem_reach p s q hq; push_cast; linarith
    · have h1 := dist_le_of_mem_reach p s h hh
      have h2 := Hex.dist_of_adj (p := h) (q := q) hq
      have := Hex.dist_triangle p h q
      push_cast; linarith

/-- **Lemma E.3.** A stack of speed `s` standing on `p` that walks to some `h` in its BFS
reach and strikes an enemy on a hex `z` adjacent to `h` has `dist p z ≤ s + 1` — whatever
hexes are free at the time. -/
theorem strike_radius (p : Hex) (s : ℕ) {h z : Hex} (hh : h ∈ reach free p s)
    (hz : Hex.Adj h z) : Hex.dist p z ≤ s + 1 := by
  have h1 := dist_le_of_mem_reach p s h hh
  have h2 := Hex.dist_of_adj hz
  have := Hex.dist_triangle p h z
  linarith

end Homm3
