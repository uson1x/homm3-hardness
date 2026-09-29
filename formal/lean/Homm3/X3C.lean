import Homm3.Accounting

/-!
# Session 4, target 1. `X3C`, exact covers, the resource lemma (Lemma 3.2), blow arithmetic

Paper: §3.3 (the arithmetic, Lemma 3.2), Appendix D.1 (the instance `G_3(X, C)`).

* `X3C` — a universe `[0, 3q)` and a list `C` of members (`set g`, `g < n`).  `WF`: every
  member is a 3-subset of the universe.  `ExactCover`: an index set `K` of pairwise disjoint
  members covering the universe; `card_cover`: then `|K| = q` (the paper's "`q` pairwise
  disjoint members").  Planarity of the incidence graph is **not** part of the formal
  problem: Theorem 3 is formalized for *every* board satisfying (I1)–(I4) (`X3CBoard.lean`),
  which is where planarity enters the paper (Lemma D.4).
* **Lemma 3.2** (`lemma32`), for every `μ ∈ (0, 1)` in `ℚ` with `D(c) = max(1, ⌊μc⌋)`, and its
  abstract core `resource` (only `b_i ≤ c_i` and `b_i = c_i → c_i = 1` are used).
* The blow of `c` player creatures of flat damage 1: `damage c 1 Δ = D_{f_def(Δ)}(c)` for
  `Δ ≤ 0` (`damage_one_eq_Dmu`), with `f_def(Δ) ∈ (0, 1)` for `Δ < 0` — so Lemma 3.2 applies to
  the undefended (`μ = 0.35` at `def 27`) and the defended (`μ = 0.3`) branch alike, and to the
  historical constants (`def 41`: `μ = 0.3` on both branches).
* With at most one creature, every blow at `Δ ≤ 0` is exactly `1` (`damage_le_one_eq`) — the
  arithmetic of Lemma D.8 and of Corollary 3.1, which needs `def(Q) ≥ att(P)` only.
-/

namespace Homm3

/-! ## The source problem -/

/-- An `X3C` instance: universe `[0, 3q)`, members `C` (a list; repeats allowed). -/
structure X3C where
  q : ℕ
  C : List (Finset ℕ)

namespace X3C

variable (P : X3C)

/-- Number of members. -/
def n : ℕ := P.C.length

/-- Member `g` (`∅` out of range). -/
def set (g : ℕ) : Finset ℕ := P.C.getD g ∅

/-- Well-formedness: every member is a 3-subset of the universe `[0, 3q)`. -/
structure WF : Prop where
  card : ∀ g < P.n, (P.set g).card = 3
  sub : ∀ g < P.n, ∀ e ∈ P.set g, e < 3 * P.q

/-- **Exact cover**: pairwise disjoint members covering the universe. -/
def ExactCover : Prop :=
  ∃ K : Finset ℕ, (∀ g ∈ K, g < P.n) ∧
    (∀ g ∈ K, ∀ g' ∈ K, g ≠ g' → Disjoint (P.set g) (P.set g')) ∧
    ∀ e < 3 * P.q, ∃ g ∈ K, e ∈ P.set g

variable {P}

/-- The members of a cover partition the universe. -/
theorem biUnion_eq (hP : P.WF) {K : Finset ℕ} (hK : ∀ g ∈ K, g < P.n)
    (hcov : ∀ e < 3 * P.q, ∃ g ∈ K, e ∈ P.set g) :
    K.biUnion P.set = Finset.range (3 * P.q) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨g, hg, he⟩; exact hP.sub g (hK g hg) e he
  · intro he; exact hcov e he

/-- **An exact cover has exactly `q` members.** -/
theorem card_cover (hP : P.WF) {K : Finset ℕ} (hK : ∀ g ∈ K, g < P.n)
    (hdis : ∀ g ∈ K, ∀ g' ∈ K, g ≠ g' → Disjoint (P.set g) (P.set g'))
    (hcov : ∀ e < 3 * P.q, ∃ g ∈ K, e ∈ P.set g) : K.card = P.q := by
  have h1 := congrArg Finset.card (biUnion_eq hP hK hcov)
  rw [Finset.card_biUnion (fun g hg g' hg' hne => hdis g hg g' hg' hne), Finset.card_range,
    Finset.sum_congr rfl (fun g hg => hP.card g (hK g hg)), Finset.sum_const, smul_eq_mul] at h1
  omega

/-- Conversely: `q` pairwise disjoint members inside the universe cover it. -/
theorem cover_of_card (hP : P.WF) {K : Finset ℕ} (hK : ∀ g ∈ K, g < P.n)
    (hdis : ∀ g ∈ K, ∀ g' ∈ K, g ≠ g' → Disjoint (P.set g) (P.set g')) (hq : P.q ≤ K.card) :
    ∀ e < 3 * P.q, ∃ g ∈ K, e ∈ P.set g := by
  have hsub : K.biUnion P.set ⊆ Finset.range (3 * P.q) := by
    intro e he
    obtain ⟨g, hg, he⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_range.mpr (hP.sub g (hK g hg) e he)
  have hc : (K.biUnion P.set).card = 3 * K.card := by
    rw [Finset.card_biUnion (fun g hg g' hg' hne => hdis g hg g' hg' hne),
      Finset.sum_congr rfl (fun g hg => hP.card g (hK g hg)), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc, Finset.card_range]; omega)
  intro e he
  rw [← Finset.mem_range, ← heq, Finset.mem_biUnion] at he
  exact he

/-- `q = 0`: the empty cover. -/
theorem exactCover_of_q_zero (h : P.q = 0) : P.ExactCover :=
  ⟨∅, by simp, by simp, fun e he => by omega⟩

end X3C

/-! ## Lemma 3.2 (the resource lemma) -/

/-- `D(c) = max(1, ⌊μc⌋)`. -/
def Dmu (μ : ℚ) (c : ℕ) : ℕ := max 1 (⌊μ * c⌋).toNat

/-- For `μ ∈ (0, 1)` and `c ≥ 1`: `D(c) ≤ c`, with equality only at `c = 1`. -/
theorem Dmu_le {μ : ℚ} (h0 : 0 < μ) (h1 : μ < 1) {c : ℕ} (hc : 1 ≤ c) :
    Dmu μ c ≤ c ∧ (Dmu μ c = c → c = 1) := by
  by_cases hc1 : c = 1
  · subst hc1
    have : ⌊μ⌋ = 0 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    simp [Dmu, this]
  · have hc2 : (2 : ℚ) ≤ c := by exact_mod_cast (show 2 ≤ c by omega)
    have hlt : ⌊μ * c⌋ < (c : ℤ) - 1 + 1 := by
      rw [Int.floor_lt]; push_cast; nlinarith
    have hle : (⌊μ * c⌋).toNat ≤ c - 1 := by omega
    have : Dmu μ c ≤ c - 1 := max_le (by omega) hle
    exact ⟨by omega, fun h => by omega⟩

/-- **The resource lemma, abstract core.** Blows `b_i ≤ c_i` with `b_i = c_i` only for
`c_i = 1`: reaching `3` costs `Σ c ≥ 3`, and `Σ c = 3` forces three singletons. -/
theorem resource {ι : Type*} (A : Finset ι) (c b : ι → ℕ) (hb : ∀ i ∈ A, b i ≤ c i)
    (hbe : ∀ i ∈ A, b i = c i → c i = 1) (h3 : 3 ≤ ∑ i ∈ A, b i) :
    3 ≤ ∑ i ∈ A, c i ∧ (∑ i ∈ A, c i = 3 → A.card = 3 ∧ ∀ i ∈ A, c i = 1) := by
  have hle := Finset.sum_le_sum hb
  refine ⟨h3.trans hle, fun heq => ?_⟩
  have hbc : ∑ i ∈ A, b i = ∑ i ∈ A, c i := by omega
  have hall := (Finset.sum_eq_sum_iff_of_le hb).mp hbc
  have hc1 : ∀ i ∈ A, c i = 1 := fun i hi => hbe i hi (hall i hi)
  refine ⟨?_, hc1⟩
  rw [Finset.sum_congr rfl hc1, Finset.sum_const, smul_eq_mul, mul_one] at heq
  exact heq

/-- **Lemma 3.2 (resource lemma).** Let `0 < μ < 1` and `D(c) = max(1, ⌊μc⌋)`.  If stacks of
sizes `c_i ≥ 1` (`i ∈ A`) each deliver at most `D(c_i)` and the total is at least `3`, then
`Σ c_i ≥ 3`, with equality iff `|A| = 3` and every `c_i = 1`. -/
theorem lemma32 {μ : ℚ} (h0 : 0 < μ) (h1 : μ < 1) {ι : Type*} (A : Finset ι) (c b : ι → ℕ)
    (hc : ∀ i ∈ A, 1 ≤ c i) (hb : ∀ i ∈ A, b i ≤ Dmu μ (c i)) (h3 : 3 ≤ ∑ i ∈ A, b i) :
    3 ≤ ∑ i ∈ A, c i ∧ (∑ i ∈ A, c i = 3 ↔ A.card = 3 ∧ ∀ i ∈ A, c i = 1) := by
  have hbc : ∀ i ∈ A, b i ≤ c i := fun i hi => (hb i hi).trans (Dmu_le h0 h1 (hc i hi)).1
  have hbe : ∀ i ∈ A, b i = c i → c i = 1 := fun i hi he =>
    (Dmu_le h0 h1 (hc i hi)).2 (le_antisymm (Dmu_le h0 h1 (hc i hi)).1 (he ▸ hb i hi))
  obtain ⟨hge, heq⟩ := resource A c b hbc hbe h3
  refine ⟨hge, heq, fun ⟨hcard, hc1⟩ => ?_⟩
  rw [Finset.sum_congr rfl hc1, Finset.sum_const, smul_eq_mul, mul_one, hcard]

/-! ## Blow arithmetic of `G_3` -/

theorem fDef_lt_one {Δ : ℤ} (h : Δ < 0) : fDef Δ < 1 := by
  unfold fDef
  rw [if_pos h]
  have : (0 : ℚ) < 1 / 40 * (-Δ) := by
    have : (Δ : ℚ) < 0 := by exact_mod_cast h
    linarith
  have := lt_min this (by norm_num : (0 : ℚ) < 7 / 10)
  linarith

/-- At `Δ ≤ 0` the blow of `c` creatures of flat damage `1` is `D_{f_def(Δ)}(c)`. -/
theorem damage_one_eq_Dmu {c : ℕ} {Δ : ℤ} (hΔ : Δ ≤ 0) : damage c 1 Δ = Dmu (fDef Δ) c := by
  simp only [damage, Dmu, fAtt_le_one hΔ, mul_one]
  rw [mul_comm]

/-- Damage is monotone in the count. -/
theorem damage_mono_count {c c' d : ℕ} (Δ : ℤ) (h : c ≤ c') : damage c d Δ ≤ damage c' d Δ := by
  unfold damage
  apply max_le_max le_rfl
  apply Int.toNat_le_toNat
  apply Int.floor_mono
  have := fAtt_pos Δ
  have := fDef_pos Δ
  have hc : ((c * d : ℕ) : ℚ) ≤ ((c' * d : ℕ) : ℚ) := by exact_mod_cast Nat.mul_le_mul_right d h
  gcongr

/-- **The blow bound of Theorem 3**: at `Δ < 0`, a stack of count `c' ≤ c` (`c ≥ 1`) of flat
damage 1 delivers `b ≤ c`, and `b = c` only when `c = 1`. -/
theorem blow_resource {c c' : ℕ} {Δ : ℤ} (hΔ : Δ < 0) (hc' : c' ≤ c) (hc : 1 ≤ c) :
    damage c' 1 Δ ≤ c ∧ (damage c' 1 Δ = c → c = 1) := by
  have h0 := fDef_pos Δ
  have h1 := fDef_lt_one hΔ
  have hm := damage_mono_count (d := 1) Δ hc'
  have hD := Dmu_le h0 h1 hc
  rw [damage_one_eq_Dmu hΔ.le] at hm ⊢
  rw [damage_one_eq_Dmu hΔ.le] at hm
  exact ⟨hm.trans hD.1, fun he => hD.2 (le_antisymm hD.1 (he.symm.le.trans hm))⟩

/-- **With at most one creature, every blow at `Δ ≤ 0` is exactly `1`.** -/
theorem damage_le_one_eq {c : ℕ} {Δ : ℤ} (hΔ : Δ ≤ 0) (hc : c ≤ 1) : damage c 1 Δ = 1 := by
  have h1 := damage_mono_count (d := 1) Δ hc
  have h2 : damage 1 1 Δ ≤ 1 * 1 := damage_le_nominal hΔ (by norm_num)
  have h3 := one_le_damage c 1 Δ
  omega

/-! ## The constants -/

/-- Published: `def(Q) = 27`, undefended `Δ = −26`: `μ = 1 − 0.65 = 0.35`. -/
theorem fDef_pub : fDef (1 - 27) = 7 / 20 := by norm_num [fDef]
/-- Published, defending: `27 + ⌊27·20/100⌋ = 32`, `Δ = −31`, past the cap: `μ = 0.3`. -/
theorem defendBonus_27 : defendBonus 27 = 5 := by decide
theorem fDef_pub_def : fDef (1 - (27 + 5)) = 3 / 10 := by norm_num [fDef]
/-- Historical (`verify_x3c.py`: `ENEMY_DEF = 41`): `μ = 0.3` on both branches. -/
theorem defendBonus_41 : defendBonus 41 = 8 := by decide
theorem fDef_hist : fDef (1 - 41) = 3 / 10 := by norm_num [fDef]
theorem fDef_hist_def : fDef (1 - (41 + 8)) = 3 / 10 := by norm_num [fDef]

/-- `D(1..12) = 1,1,1,1,1,2,2,2,3,3,3,4` at the published constants (§3.3). -/
theorem D_table : (List.range 12).map (fun c => damage (c + 1) 1 (1 - 27)) =
    [1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  norm_num [damage, fAtt, fDef]

/-- The negative control's constants (`def(Q) = att(P) = 1`): `D(c) = c`, Lemma 3.2 fails. -/
theorem damage_negctl (c : ℕ) (hc : 1 ≤ c) : damage c 1 (1 - 1) = c := by
  simpa using damage_zero (c := c) (d := 1) (by omega)

end Homm3
