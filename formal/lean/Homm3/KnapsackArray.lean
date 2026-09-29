import Homm3.Knapsack

/-!
# Session 2, target 5b. The one-row array DP of `dp_single_type.dp`, and its correctness

`homm3/scripts/dp_single_type.py`:

```
best = [0] * (budget + 1)
for v, b in zip(values, needs):
    if b > budget: continue
    for cap in range(budget, b - 1, -1):
        cand = best[cap - b] + v
        if cand > best[cap]: best[cap] = cand
return best[budget]
```

`dpArray` transcribes it on an `Array ℕ` of size `B + 1`, updated in place (`setIfInBounds`)
in **descending** capacity order.  `dpArray_eq_dp`: it returns the recursive `dp` (hence
`OPT` of `(K)`, `dp_eq_OPT`).  The invariant of the inner loop is the whole argument: after the
caps `B, B−1, …, B−n+1` have been processed, those entries hold the new row and all lower
entries still hold the old row, so `best[cap − b]` (with `cap − b < cap`, or `= cap` when
`b = 0`) is still the old value when it is read.  Space: one array of `B + 1` numbers;
time: `Σ_j (B + 1 − b_j) ≤ k (B + 1)` inner iterations.
-/

namespace Homm3.Knapsack

/-- Inner loop: `cap = B, B−1, …, b`. -/
def rowStep (v b B : ℕ) (best : Array ℕ) : Array ℕ :=
  (List.range (B + 1 - b)).foldl
    (fun arr i =>
      let cap := B - i
      let cand := arr.getD (cap - b) 0 + v
      if cand > arr.getD cap 0 then arr.setIfInBounds cap cand else arr)
    best

/-- The whole program. -/
def dpArray (v b : ℕ → ℕ) (k B : ℕ) : ℕ :=
  ((List.range k).foldl
    (fun arr j => if b j > B then arr else rowStep (v j) (b j) B arr)
    (Array.replicate (B + 1) 0)).getD B 0

theorem getD_setIfInBounds (arr : Array ℕ) {i : ℕ} (x j : ℕ) (hi : i < arr.size) :
    (arr.setIfInBounds i x).getD j 0 = if i = j then x else arr.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all

/-- One recurrence row. -/
def newRow (v b : ℕ) (old : ℕ → ℕ) (c : ℕ) : ℕ :=
  if b ≤ c then max (old c) (v + old (c - b)) else old c

/-- The inner-loop invariant after `n` descending steps. -/
theorem rowStep_inv (v b B : ℕ) (hb : b ≤ B) (best : Array ℕ) (hs : best.size = B + 1) :
    ∀ n ≤ B + 1 - b,
      let arr := (List.range n).foldl
        (fun arr i =>
          let cap := B - i
          let cand := arr.getD (cap - b) 0 + v
          if cand > arr.getD cap 0 then arr.setIfInBounds cap cand else arr) best
      arr.size = B + 1 ∧ ∀ c ≤ B, arr.getD c 0 =
        if B + 1 - n ≤ c then newRow v b (fun c => best.getD c 0) c else best.getD c 0 := by
  intro n
  induction n with
  | zero => intro _; simp only [List.range_zero, List.foldl_nil]; exact ⟨hs, fun c hc => by
      rw [if_neg (by omega)]⟩
  | succ n ih =>
    intro hn
    obtain ⟨hsz, hval⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hA : (List.range n).foldl _ best = arr at hsz hval
    -- the cap processed now is `B − n ≥ b`
    have hcap : b ≤ B - n := by omega
    have hread1 : arr.getD (B - n - b) 0 = best.getD (B - n - b) 0 := by
      rw [hval _ (by omega), if_neg (by omega)]
    have hread2 : arr.getD (B - n) 0 = best.getD (B - n) 0 := by
      rw [hval _ (by omega), if_neg (by omega)]
    simp only [hread1, hread2]
    split_ifs with hlt
    · refine ⟨by simp [hsz], fun c hc => ?_⟩
      rw [getD_setIfInBounds _ _ _ (by omega)]
      by_cases hceq : B - n = c
      · subst hceq
        rw [if_pos rfl, if_pos (by omega)]
        simp only [newRow, if_pos hcap]
        rw [max_eq_right (by omega)]; ring
      · rw [if_neg hceq, hval c hc]
        by_cases h1 : B + 1 - n ≤ c
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · refine ⟨hsz, fun c hc => ?_⟩
      by_cases hceq : B - n = c
      · subst hceq
        rw [hread2, if_pos (by omega)]
        simp only [newRow, if_pos hcap]
        rw [max_eq_left (by omega)]
      · rw [hval c hc]
        by_cases h1 : B + 1 - n ≤ c
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]

/-- **The inner loop computes one recurrence row**, in place. -/
theorem rowStep_spec (v b B : ℕ) (hb : b ≤ B) (best : Array ℕ) (hs : best.size = B + 1) :
    (rowStep v b B best).size = B + 1 ∧ ∀ c ≤ B,
      (rowStep v b B best).getD c 0 = newRow v b (fun c => best.getD c 0) c := by
  obtain ⟨h1, h2⟩ := rowStep_inv v b B hb best hs (B + 1 - b) le_rfl
  refine ⟨h1, fun c hc => ?_⟩
  unfold rowStep
  rw [h2 c hc]
  split_ifs with h
  · rfl
  · simp only [newRow, if_neg (show ¬ b ≤ c by omega)]

/-- The outer-loop invariant: after items `0 … j−1` the array holds `dp v b j ·`. -/
theorem outer_inv (v b : ℕ → ℕ) (B : ℕ) : ∀ j,
    let arr := (List.range j).foldl
      (fun arr j => if b j > B then arr else rowStep (v j) (b j) B arr)
      (Array.replicate (B + 1) 0)
    arr.size = B + 1 ∧ ∀ c ≤ B, arr.getD c 0 = dp v b j c
  | 0 => by
    simp only [List.range_zero, List.foldl_nil, Array.size_replicate, true_and]
    intro c hc
    simp [Array.getD_eq_getD_getElem?, dp, show c < B + 1 by omega]
  | j + 1 => by
    obtain ⟨hsz, hval⟩ := outer_inv v b B j
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl _ _ = arr at hsz hval
    split_ifs with hbig
    · refine ⟨hsz, fun c hc => ?_⟩
      rw [hval c hc]
      simp only [dp, if_neg (show ¬ b j ≤ c by omega)]
    · obtain ⟨h1, h2⟩ := rowStep_spec (v j) (b j) B (by omega) arr hsz
      refine ⟨h1, fun c hc => ?_⟩
      rw [h2 c hc]
      simp only [newRow, dp]
      split_ifs with hbc
      · rw [hval c hc, hval (c - b j) (by omega)]
      · rw [hval c hc]

/-- **The array program of `dp_single_type.py` computes the DP**, hence `OPT` of `(K)`. -/
theorem dpArray_eq_dp (v b : ℕ → ℕ) (k B : ℕ) : dpArray v b k B = dp v b k B :=
  (outer_inv v b B k).2 B le_rfl

theorem dpArray_eq_OPT (v b : ℕ → ℕ) (k B : ℕ) : dpArray v b k B = OPT v b k B := by
  rw [dpArray_eq_dp, dp_eq_OPT]

/-- The script's `[1]` numbers, spot-checked by evaluation. -/
example : dpArray (fun j => [3, 4, 5].getD j 0) (fun j => [2, 3, 4].getD j 0) 3 5 = 7 := by decide

end Homm3.Knapsack
