import Homm3.Hex

/-!
# Session 3. Walks in the BFS reach, for a given set of free hexes

The converse of the metric half of Lemma E.3 for an *arbitrary* free set: a walk of free
hexes from `p` of length `≤ s` ends in `reach free p s`.  Stated in the two forms Theorem 4's
routing (Lemma E.17) uses: one step (`reach_succ`), and a straight walk along a row
(`reach_row`).  Session 2's `mem_reach_univ` is the special case of the full grid.
-/

namespace Homm3

variable {free : Hex → Prop} [DecidablePred free]

/-- One more free step stays in the reach, one layer further. -/
theorem reach_succ {p h q : Hex} {s : ℕ} (hh : h ∈ reach free p s) (hadj : Hex.Adj h q)
    (hq : free q) : q ∈ reach free p (s + 1) := by
  simp only [reach, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq]
  exact Or.inr ⟨h, hh, hadj, hq⟩

theorem adj_right (x y : ℤ) : Hex.Adj ⟨x, y⟩ ⟨x + 1, y⟩ := by simp [Hex.Adj, Hex.nbrs]
theorem adj_left (x y : ℤ) : Hex.Adj ⟨x, y⟩ ⟨x - 1, y⟩ := by simp [Hex.Adj, Hex.nbrs]

/-- **A straight walk along row `y`**, all of whose hexes in `[0, w)` are free, costs `|c − x|`
layers. -/
theorem reach_row {p : Hex} {y w : ℤ} (hrow : ∀ x, 0 ≤ x → x < w → free ⟨x, y⟩) :
    ∀ (d : ℕ) (x c : ℤ) (s : ℕ), 0 ≤ x → x < w → 0 ≤ c → c < w → (c - x).natAbs = d →
      (⟨x, y⟩ : Hex) ∈ reach free p s → (⟨c, y⟩ : Hex) ∈ reach free p (s + d)
  | 0, x, c, s, _, _, _, _, hd, hm => by
    have : c = x := by omega
    subst this; simpa using hm
  | d + 1, x, c, s, hx0, hxw, hc0, hcw, hd, hm => by
    by_cases hlt : x < c
    · have h1 : (⟨x + 1, y⟩ : Hex) ∈ reach free p (s + 1) :=
        reach_succ hm (adj_right x y) (hrow _ (by omega) (by omega))
      have := reach_row hrow d (x + 1) c (s + 1) (by omega) (by omega) hc0 hcw (by omega) h1
      rwa [show s + 1 + d = s + (d + 1) by omega] at this
    · have h1 : (⟨x - 1, y⟩ : Hex) ∈ reach free p (s + 1) :=
        reach_succ hm (adj_left x y) (hrow _ (by omega) (by omega))
      have := reach_row hrow d (x - 1) c (s + 1) (by omega) (by omega) hc0 hcw (by omega) h1
      rwa [show s + 1 + d = s + (d + 1) by omega] at this

end Homm3
