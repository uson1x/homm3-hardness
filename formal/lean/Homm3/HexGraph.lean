import Homm3.Hex

/-!
# Lemma E.3, the converse half: R2 distance is the graph distance of R1 adjacency

Paper, Appendix E, Lemma E.3, proof, "Conversely": when `δA` and `δy` agree in sign,
diagonal steps plus straight ones realize the displacement in `max(|δA|, |δy|)` steps; when
they differ, `|δA| + |δy|` straight steps do.  Together with `dist_le_of_mem_reach` (the
metric half, Stage 1) this gives: on the full grid, `q` is in the BFS reach of `p` within
`s` steps **iff** `dist p q ≤ s` (`mem_reach_univ_iff`).
-/

namespace Homm3

namespace Hex

theorem gauge_nn {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : gauge a b = max a b := by
  simp [gauge, ha, hb, abs_of_nonneg]

theorem gauge_neg {a b : ℤ} (ha : a < 0) (hb : b < 0) : gauge a b = max (-a) (-b) := by
  simp [gauge, ha, hb, abs_of_neg]

theorem gauge_pn {a b : ℤ} (ha : 0 ≤ a) (hb : b < 0) : gauge a b = a - b := by
  have : ¬ ((0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0)) := by omega
  simp only [gauge, this, ↓reduceIte, abs_of_nonneg ha, abs_of_neg hb]; ring

theorem gauge_np {a b : ℤ} (ha : a < 0) (hb : 0 ≤ b) : gauge a b = b - a := by
  have : ¬ ((0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0)) := by omega
  simp only [gauge, this, ↓reduceIte, abs_of_neg ha, abs_of_nonneg hb]; ring

theorem gauge_eq_zero {a b : ℤ} (h : gauge a b = 0) : a = 0 ∧ b = 0 := by
  rw [gauge_eq] at h
  have ha : |a| ≤ 0 := h ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hb : |b| ≤ 0 := h ▸ (le_max_right _ _).trans (le_max_left _ _)
  exact ⟨abs_nonpos_iff.mp ha, abs_nonpos_iff.mp hb⟩

/-- In axial coordinates the six neighbours of `q` are displaced by
`(−1,0), (1,0), (−1,−1), (0,−1), (0,1), (1,1)`. -/
theorem nbr_axial (q : Hex) :
    ∀ u ∈ [((-1 : ℤ), (0 : ℤ)), (1, 0), (-1, -1), (0, -1), (0, 1), (1, 1)],
      ∃ q' ∈ q.nbrs, q'.axial = q.axial + u.1 ∧ q'.y = q.y + u.2 := by
  obtain ⟨x, y⟩ := q
  have e1 : (y - 1) / 2 = y / 2 - 1 + y % 2 := by omega
  have e2 : (y + 1) / 2 = y / 2 + y % 2 := by omega
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨x - 1, y⟩, by simp [nbrs], by simp [axial]; ring, by simp⟩
  · exact ⟨⟨x + 1, y⟩, by simp [nbrs], by simp [axial]; ring, by simp⟩
  · exact ⟨⟨x - y % 2, y - 1⟩, by simp [nbrs], by simp only [axial, e1]; ring, by simp; ring⟩
  · exact ⟨⟨x + 1 - y % 2, y - 1⟩, by simp [nbrs], by simp only [axial, e1]; ring,
      by simp; ring⟩
  · exact ⟨⟨x - y % 2, y + 1⟩, by simp [nbrs], by simp only [axial, e2]; ring, by simp⟩
  · exact ⟨⟨x + 1 - y % 2, y + 1⟩, by simp [nbrs], by simp only [axial, e2]; ring, by simp⟩

/-- The gauge by sign cases, in a form `omega` can read after `max_def`. -/
def gaugeIf (a b : ℤ) : ℤ :=
  if 0 ≤ a ∧ 0 ≤ b then max a b else if a < 0 ∧ b < 0 then max (-a) (-b)
  else if 0 ≤ a then a - b else b - a

theorem gauge_val (a b : ℤ) : gauge a b = gaugeIf a b := by
  unfold gaugeIf
  split_ifs with h1 h2 h3
  · exact gauge_nn h1.1 h1.2
  · exact gauge_neg h2.1 h2.2
  · exact gauge_pn h3 (by omega)
  · exact gauge_np (by omega) (by omega)

/-- Some neighbour of `q` is one step closer to `p` (for `q ≠ p`). -/
theorem exists_nbr_closer (p q : Hex) (h : 0 < dist p q) :
    ∃ q' ∈ q.nbrs, dist p q' + 1 = dist p q := by
  set a := q.axial - p.axial with ha
  set b := q.y - p.y with hb
  have hd : dist p q = gauge a b := rfl
  have pick : ∀ u ∈ [((-1 : ℤ), (0 : ℤ)), (1, 0), (-1, -1), (0, -1), (0, 1), (1, 1)],
      gauge (a + u.1) (b + u.2) + 1 = gauge a b →
        ∃ q' ∈ q.nbrs, dist p q' + 1 = dist p q := by
    intro u hu hg
    obtain ⟨q', hq', hx, hy⟩ := nbr_axial q u hu
    refine ⟨q', hq', ?_⟩
    have : dist p q' = gauge (a + u.1) (b + u.2) := by
      simp only [dist, hx, hy, ha, hb]; congr 1 <;> ring
    rw [this, hd, hg]
  rw [hd] at h
  have fin : ∀ c e : ℤ, gauge c e + 1 = gauge a b ↔
      gaugeIf c e + 1 = gaugeIf a b := by
    intro c e; rw [gauge_val, gauge_val]
  rcases lt_trichotomy a 0 with ha0 | ha0 | ha0 <;>
    rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
  · exact pick (1, 1) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · exact pick (1, 0) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · exact pick (1, 0) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · exact pick (0, 1) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · rw [ha0, hb0] at h; simp [gauge] at h
  · exact pick (0, -1) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · exact pick (-1, 0) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · exact pick (-1, 0) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))
  · exact pick (-1, -1) (by simp) ((fin _ _).mpr (by
      simp only [gaugeIf, max_def]; split_ifs <;> omega))

theorem eq_of_dist_zero {p q : Hex} (h : dist p q = 0) : q = p := by
  obtain ⟨h1, h2⟩ := gauge_eq_zero h
  obtain ⟨x, y⟩ := q; obtain ⟨x', y'⟩ := p
  simp only [axial] at h1 h2
  ext <;> simp <;> omega

end Hex

/-- **Lemma E.3, converse half.** On the full grid (every hex free) a hex at R2 distance
`≤ s` is in the BFS reach within `s` steps. -/
theorem mem_reach_univ (p : Hex) : ∀ (s : ℕ) (q : Hex), Hex.dist p q ≤ s →
    q ∈ reach (fun _ => True) p s
  | 0, q, h => by
    have := Hex.dist_nonneg p q
    have hq := Hex.eq_of_dist_zero (p := p) (q := q) (by push_cast at h; omega)
    subst hq
    exact start_mem_reach _ 0
  | s + 1, q, h => by
    by_cases hle : Hex.dist p q ≤ s
    · exact reach_mono p (Nat.le_succ s) (mem_reach_univ p s q hle)
    · obtain ⟨q', hq', hd⟩ := Hex.exists_nbr_closer p q (by push_cast at hle; omega)
      have ih := mem_reach_univ p s q' (by push_cast at h hle ⊢; omega)
      simp only [reach, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
        List.mem_filter, decide_true, and_true]
      exact Or.inr ⟨q', ih, Hex.adj_symm hq'⟩

/-- **Lemma E.3, both halves on the full grid**: BFS reach within `s` steps is exactly the
R2 ball of radius `s`, i.e. R2 distance is the graph distance of R1 adjacency. -/
theorem mem_reach_univ_iff (p q : Hex) (s : ℕ) :
    q ∈ reach (fun _ => True) p s ↔ Hex.dist p q ≤ s :=
  ⟨dist_le_of_mem_reach p s q, mem_reach_univ p s q⟩

/-- A BFS over any set of free hexes is contained in the BFS over the full grid. -/
theorem reach_subset_univ (free : Hex → Prop) [DecidablePred free] (p : Hex) (s : ℕ) :
    reach free p s ⊆ reach (fun _ => True) p s :=
  fun q hq => mem_reach_univ p s q (dist_le_of_mem_reach p s q hq)

end Homm3
