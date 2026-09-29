import Mathlib

/-!
# Stage 2. Damage (R7) in the exact-rational model

Source of truth: `homm3/MODEL.md` §4 (Definition 4.1 and "Arithmetic semantics"),
`homm3/paper/main.md` §2.2 (R7), Appendix E "`(★)` in full", Lemma E.20's arithmetic.

The theorems of the paper are about the *exact-rational* model: constants `1/20`, `4`,
`1/40`, `7/10`, exact products, exact floor, lower clamp `max(1, ·)`.  The shooter melee
penalty is omitted: the formalized fragment is `H3-det-melee` (MODEL.md Def. 7.1a),
on which this is the whole formula.
-/

namespace Homm3

/-- Attack factor: `1 + min(Δ/20, 4)` if `Δ > 0`, else `1`. -/
def fAtt (Δ : ℤ) : ℚ := if 0 < Δ then 1 + min ((1 / 20 : ℚ) * Δ) 4 else 1

/-- Defence factor: `1 − min(−Δ/40, 7/10)` if `Δ < 0`, else `1`. -/
def fDef (Δ : ℤ) : ℚ := if Δ < 0 then 1 - min ((1 / 40 : ℚ) * (-Δ)) (7 / 10) else 1

/-- R7: a stack of `count` creatures of flat per-creature damage `d` striking with
advantage `Δ = att − def` deals `max(1, ⌊count · d · f_att · f_def⌋)`. -/
def damage (count d : ℕ) (Δ : ℤ) : ℕ :=
  max 1 (⌊((count * d : ℕ) : ℚ) * fAtt Δ * fDef Δ⌋).toNat

/-- The `DEFEND` bonus (R13): `+20 %` of defence as an integer, floor `+1`. -/
def defendBonus (def_ : ℕ) : ℕ := max 1 (def_ * 20 / 100)

theorem fAtt_zero : fAtt 0 = 1 := by simp [fAtt]
theorem fDef_zero : fDef 0 = 1 := by simp [fDef]

theorem fAtt_pos (Δ : ℤ) : 0 < fAtt Δ := by
  unfold fAtt; split_ifs with h
  · have : (0 : ℚ) < Δ := by exact_mod_cast h
    have : 0 < min ((1 / 20 : ℚ) * Δ) 4 := lt_min (by positivity) (by norm_num)
    linarith
  · norm_num

theorem fDef_pos (Δ : ℤ) : 0 < fDef Δ := by
  unfold fDef; split_ifs with h
  · have := min_le_right ((1 / 40 : ℚ) * (-Δ)) (7 / 10); linarith
  · norm_num

theorem fAtt_mono {Δ Δ' : ℤ} (h : Δ ≤ Δ') : fAtt Δ ≤ fAtt Δ' := by
  have hq : (Δ : ℚ) ≤ Δ' := by exact_mod_cast h
  unfold fAtt; split_ifs with h1 h2 h2
  · have : (1 / 20 : ℚ) * Δ ≤ 1 / 20 * Δ' := by linarith
    linarith [min_le_min_right (4 : ℚ) this]
  · omega
  · have : (0 : ℚ) < Δ' := by exact_mod_cast h2
    have : 0 < min ((1 / 20 : ℚ) * Δ') 4 := lt_min (by positivity) (by norm_num)
    linarith
  · exact le_rfl

theorem fDef_mono {Δ Δ' : ℤ} (h : Δ ≤ Δ') : fDef Δ ≤ fDef Δ' := by
  have hq : (Δ : ℚ) ≤ Δ' := by exact_mod_cast h
  unfold fDef; split_ifs with h1 h2 h2
  · have : (1 / 40 : ℚ) * (-Δ') ≤ 1 / 40 * (-Δ) := by linarith
    linarith [min_le_min_right (7 / 10 : ℚ) this]
  · have : (0 : ℚ) ≤ 1 / 40 * (-Δ) := by
      have : (Δ : ℚ) < 0 := by exact_mod_cast h1
      linarith
    have := le_min this (by norm_num : (0 : ℚ) ≤ 7 / 10)
    linarith
  · omega
  · exact le_rfl

theorem fAtt_le_one {Δ : ℤ} (h : Δ ≤ 0) : fAtt Δ = 1 := by
  unfold fAtt; simp only [show ¬ (0 < Δ) by omega, ↓reduceIte]

/-- The clamp: every blow deals at least `1`. -/
theorem one_le_damage (c d : ℕ) (Δ : ℤ) : 1 ≤ damage c d Δ := le_max_left _ _

/-- **Damage is monotone in the advantage.** Raising the target's defence (e.g. the
`DEFEND` bonus) can only lower the damage. -/
theorem damage_mono (c d : ℕ) {Δ Δ' : ℤ} (h : Δ ≤ Δ') : damage c d Δ ≤ damage c d Δ' := by
  unfold damage
  apply max_le_max le_rfl
  apply Int.toNat_le_toNat
  apply Int.floor_mono
  have h0 : (0 : ℚ) ≤ ((c * d : ℕ) : ℚ) := by positivity
  have ha := fAtt_mono h
  have hd := fDef_mono h
  have := fAtt_pos Δ
  have := fDef_pos Δ
  calc ((c * d : ℕ) : ℚ) * fAtt Δ * fDef Δ ≤ ((c * d : ℕ) : ℚ) * fAtt Δ' * fDef Δ := by
        gcongr
    _ ≤ ((c * d : ℕ) : ℚ) * fAtt Δ' * fDef Δ' := by
        have := fAtt_pos Δ'
        gcongr

/-- **`(★)`, Δ = 0.** With `count · d ≥ 1` the clamp is inert and the nominal damage is
dealt exactly.  (The hypothesis is needed: `damage 0 d 0 = 1` by the clamp.) -/
theorem damage_zero {c d : ℕ} (h : 1 ≤ c * d) : damage c d 0 = c * d := by
  simp only [damage, fAtt_zero, fDef_zero, mul_one, Int.floor_natCast, Int.toNat_natCast]
  exact max_eq_right h

/-- Without the hypothesis `1 ≤ c·d` the Δ = 0 statement is false. -/
example : damage 0 1 0 = 1 := by simp [damage, fAtt_zero, fDef_zero]

/-- At `Δ ≤ 0` a blow deals at most nominal (given `c·d ≥ 1`). -/
theorem damage_le_nominal {c d : ℕ} {Δ : ℤ} (hΔ : Δ ≤ 0) (h : 1 ≤ c * d) :
    damage c d Δ ≤ c * d :=
  (damage_mono c d hΔ).trans (damage_zero h).le

/-- The `DEFEND` bonus at `α = 1`: defence `1` becomes `2`, so `Δ = 1 − 2 = −1`. -/
theorem defendBonus_one : defendBonus 1 = 1 := by decide

theorem fDef_neg_one : fDef (-1) = 39 / 40 := by norm_num [fDef]

/-- The defended blow at `α = 1`: `max(1, ⌊c·d · 39/40⌋)`. -/
theorem damage_neg_one (c d : ℕ) :
    damage c d (-1) = max 1 (⌊((c * d : ℕ) : ℚ) * (39 / 40)⌋).toNat := by
  simp [damage, fAtt_le_one (show (-1 : ℤ) ≤ 0 by norm_num), fDef_neg_one]

/-- **E.20 arithmetic, part 1.** A defended blow (`Δ = −1`) never exceeds nominal. -/
theorem damage_neg_one_le {c d : ℕ} (h : 1 ≤ c * d) : damage c d (-1) ≤ c * d :=
  damage_le_nominal (by norm_num) h

/-- **E.20 arithmetic, part 2.** A defended blow (`Δ = −1`) equals nominal **exactly when
`c·d = 1`** (the clamp lifts `⌊39/40⌋ = 0` back to `1`); for `c·d ≥ 2` it is strictly
below nominal.  So "strictly less" is false at `c·d = 1`. -/
theorem clamp_floor_39_40_eq_iff {n : ℕ} (h : 1 ≤ n) :
    max 1 (⌊(n : ℚ) * (39 / 40)⌋).toNat = n ↔ n = 1 := by
  constructor
  · intro heq
    by_contra hne
    have h2 : (2 : ℚ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hlt : ⌊(n : ℚ) * (39 / 40)⌋ < (n : ℤ) := by
      rw [Int.floor_lt]; push_cast; nlinarith
    generalize ⌊(n : ℚ) * (39 / 40)⌋ = z at heq hlt
    omega
  · rintro rfl; norm_num

theorem damage_neg_one_eq_iff {c d : ℕ} (h : 1 ≤ c * d) :
    damage c d (-1) = c * d ↔ c * d = 1 := by
  rw [damage_neg_one]; exact clamp_floor_39_40_eq_iff h

/-- Strictly below nominal when `c·d ≥ 2`. -/
theorem damage_neg_one_lt {c d : ℕ} (h : 2 ≤ c * d) : damage c d (-1) < c * d := by
  have hle := damage_neg_one_le (c := c) (d := d) (by omega)
  have hne : damage c d (-1) ≠ c * d := fun e => by
    have := (damage_neg_one_eq_iff (by omega)).mp e; omega
  omega

/-- Cross-check with MODEL.md §4 "Arithmetic semantics": a defended blow of base 90 against
attack 0 / defence 10 (`+2` bonus, so `Δ = −12`, `f_def = 7/10` exactly) floors to `63` in
the exact model (the float reference gives `62`). -/
example : defendBonus 10 = 2 ∧ damage 90 1 (0 - (10 + 2)) = 63 := by
  refine ⟨by decide, ?_⟩
  norm_num [damage, fAtt, fDef]

end Homm3
