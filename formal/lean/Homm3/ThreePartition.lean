import Mathlib

/-!
# Session 3. `3-PARTITION`, the source problem of Theorems 2 and 4

Paper: Appendix E, "Theorem 2", *Source problem*: given `3m` positive integers
`a_1, …, a_{3m}` and a bound `T` with `Σ a_i = mT` and `T/4 < a_i < T/2`, is there a partition of
`[3m]` into `m` triples each summing to `T`?

* `Promise3P a T` — the promise (`|a| = 3m`, `Σ a = mT`, `T < 4 a_i`, `2 a_i < T`); positivity
  of the `a_i` follows from `T < 4 a_i`.
* `THREE_PARTITION a T` — the question, literally: `m` triples `S g ⊆ [3m]` (`g < m`), each of
  three elements summing to `T`, pairwise disjoint, covering `[3m]`.  Indices are `0`-based,
  `a.getD i 0` is `a_{i+1}`.
* `ThreeP.of_disjoint` — **the counting argument of Lemmas E.14 / E.22**: `m` pairwise disjoint
  subsets of `[3m]`, each summing to at least `T`, under the promise, form a 3-partition.
  It consumes only `2 a_i < T` and `Σ a = mT`: every set needs three elements, `m` disjoint
  sets of at least three elements inside `[3m]` have exactly three each and cover `[3m]`, and
  the sums are then tight.  The lower promise `T < 4 a_i` is not used here (in the reductions
  it only supplies `a_i ≥ 1`, i.e. the model's `dmg ≥ 1`).
* `ThreeP.pick S g r` — the `r`-th smallest element of triple `g` (`r < 3`); the witnesses of
  Lemmas E.13 and E.21 seat these.  `pick_mem`, `pick_inj`, `pick_surj`, `sum_pick`.

No NP-hardness is formalized: `3-PARTITION` is a definition, not an axiom.
-/

namespace Homm3

/-- The promise of `3-PARTITION`: `|a| = 3m`, `Σ a = mT`, `T/4 < a_i < T/2`. -/
def Promise3P (a : List ℕ) (T : ℕ) : Prop :=
  a.length % 3 = 0 ∧ a.sum = a.length / 3 * T ∧ ∀ x ∈ a, T < 4 * x ∧ 2 * x < T

/-- **`3-PARTITION`**: `[3m]` splits into `m` triples, each summing to `T`. -/
def THREE_PARTITION (a : List ℕ) (T : ℕ) : Prop :=
  a.length % 3 = 0 ∧ ∃ S : ℕ → Finset ℕ,
    (∀ g < a.length / 3, S g ⊆ Finset.range a.length ∧ (S g).card = 3 ∧
      ∑ i ∈ S g, a.getD i 0 = T) ∧
    (∀ g < a.length / 3, ∀ g' < a.length / 3, g ≠ g' → Disjoint (S g) (S g')) ∧
    (∀ i < a.length, ∃ g < a.length / 3, i ∈ S g)

namespace ThreeP

variable {a : List ℕ} {T : ℕ}

theorem getD_mem {i : ℕ} (hi : i < a.length) : a.getD i 0 ∈ a := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem sum_getD (a : List ℕ) : ∑ j ∈ Finset.range a.length, a.getD j 0 = a.sum := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    ring

/-- Under the promise every entry is positive. -/
theorem pos_of_promise (hP : Promise3P a T) {i : ℕ} (hi : i < a.length) : 1 ≤ a.getD i 0 := by
  have := (hP.2.2 _ (getD_mem hi)).1; omega

/-- **The counting argument of Lemmas E.14 and E.22.** -/
theorem of_disjoint (hP : Promise3P a T) (S : ℕ → Finset ℕ)
    (hsub : ∀ g < a.length / 3, S g ⊆ Finset.range a.length)
    (hdisj : ∀ g < a.length / 3, ∀ g' < a.length / 3, g ≠ g' → Disjoint (S g) (S g'))
    (hge : ∀ g < a.length / 3, T ≤ ∑ i ∈ S g, a.getD i 0) : THREE_PARTITION a T := by
  obtain ⟨h3, hsum, hbd⟩ := hP
  set n := a.length with hn
  set m := n / 3 with hm
  have hn3 : n = 3 * m := by omega
  -- every set has at least three elements: two entries sum to less than `T`
  have hcard3 : ∀ g < m, 3 ≤ (S g).card := by
    intro g hg
    by_contra hlt
    push Not at hlt
    have h2 : ∀ i ∈ S g, 2 * a.getD i 0 + 1 ≤ T := by
      intro i hi
      have := (hbd _ (getD_mem (Finset.mem_range.mp (hsub g hg hi)))).2
      omega
    have hs := Finset.sum_le_sum h2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_const, smul_eq_mul] at hs
    have hge' := hge g hg
    have hcT : (S g).card * T ≤ 2 * T := Nat.mul_le_mul_right T (by omega)
    generalize (S g).card * T = P at hs hcT
    have hc0 : (S g).card = 0 := by omega
    have hT0 : T = 0 := by
      rw [Finset.card_eq_zero.mp hc0, Finset.sum_empty] at hge'; omega
    have := (hbd _ (getD_mem (show 0 < n by omega))).2
    omega
  -- the union: `m` disjoint sets of `≥ 3` elements inside `[3m]`
  have hpd : ((Finset.range m : Finset ℕ) : Set ℕ).PairwiseDisjoint S := by
    intro g hg g' hg' hne
    exact hdisj g (by simpa using hg) g' (by simpa using hg') hne
  set U := (Finset.range m).biUnion S with hU
  have hUsub : U ⊆ Finset.range n := by
    intro i hi
    obtain ⟨g, hg, hig⟩ := Finset.mem_biUnion.mp hi
    exact hsub g (Finset.mem_range.mp hg) hig
  have hcardU : U.card = ∑ g ∈ Finset.range m, (S g).card := Finset.card_biUnion hpd
  have hle : ∑ g ∈ Finset.range m, 3 ≤ ∑ g ∈ Finset.range m, (S g).card :=
    Finset.sum_le_sum (fun g hg => hcard3 g (Finset.mem_range.mp hg))
  have hUn : U.card ≤ n := by simpa using Finset.card_le_card hUsub
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
  have heq3 : ∑ g ∈ Finset.range m, 3 = ∑ g ∈ Finset.range m, (S g).card := by
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; omega
  have hc3 : ∀ g < m, (S g).card = 3 := by
    intro g hg
    exact ((Finset.sum_eq_sum_iff_of_le (fun g hg => hcard3 g (Finset.mem_range.mp hg))).mp
      heq3 g (Finset.mem_range.mpr hg)).symm
  have hUeq : U = Finset.range n :=
    Finset.eq_of_subset_of_card_le hUsub (by simp only [Finset.card_range]; omega)
  -- the sums are tight
  have hsU : ∑ g ∈ Finset.range m, ∑ i ∈ S g, a.getD i 0 = m * T := by
    rw [← Finset.sum_biUnion hpd, ← hU, hUeq, hn, sum_getD, hsum]
  have hTs : ∑ g ∈ Finset.range m, T = ∑ g ∈ Finset.range m, ∑ i ∈ S g, a.getD i 0 := by
    rw [hsU]; simp [mul_comm]
  have hsT : ∀ g < m, ∑ i ∈ S g, a.getD i 0 = T := by
    intro g hg
    exact ((Finset.sum_eq_sum_iff_of_le (fun g hg => hge g (Finset.mem_range.mp hg))).mp
      hTs g (Finset.mem_range.mpr hg)).symm
  refine ⟨h3, S, fun g hg => ⟨hsub g hg, hc3 g hg, hsT g hg⟩, hdisj, ?_⟩
  intro i hi
  have : i ∈ U := hUeq ▸ Finset.mem_range.mpr hi
  obtain ⟨g, hg, hig⟩ := Finset.mem_biUnion.mp this
  exact ⟨g, Finset.mem_range.mp hg, hig⟩

/-! ## Seating the triples -/

/-- The `r`-th smallest element of triple `g`. -/
def pick (S : ℕ → Finset ℕ) (g r : ℕ) : ℕ := ((S g).sort).getD r 0

variable {S : ℕ → Finset ℕ} {g r : ℕ}

theorem length_sort_eq (hc : (S g).card = 3) : ((S g).sort).length = 3 := by
  rw [Finset.length_sort]; exact hc

theorem pick_eq (hc : (S g).card = 3) (hr : r < 3) :
    pick S g r = ((S g).sort)[r]'(by rw [length_sort_eq hc]; exact hr) := by
  unfold pick; rw [List.getD_eq_getElem]

theorem pick_mem (hc : (S g).card = 3) (hr : r < 3) : pick S g r ∈ S g := by
  rw [pick_eq hc hr, ← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _

theorem pick_inj_r {r' : ℕ} (hc : (S g).card = 3) (hr : r < 3) (hr' : r' < 3)
    (h : pick S g r = pick S g r') : r = r' := by
  rw [pick_eq hc hr, pick_eq hc hr'] at h
  exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup _ (· ≤ ·))).mp h

theorem pick_surj {i : ℕ} (hc : (S g).card = 3) (hi : i ∈ S g) : ∃ r < 3, pick S g r = i := by
  rw [← Finset.mem_sort (· ≤ ·), List.mem_iff_getElem] at hi
  obtain ⟨r, hr, e⟩ := hi
  rw [length_sort_eq hc] at hr
  exact ⟨r, hr, by rw [pick_eq hc hr]; exact e⟩

theorem sum_pick (f : ℕ → ℕ) (hc : (S g).card = 3) :
    ∑ r ∈ Finset.range 3, f (pick S g r) = ∑ i ∈ S g, f i := by
  have hl := length_sort_eq hc
  have hsum : ∑ i ∈ S g, f i = (((S g).sort).map f).sum := by
    conv_lhs => rw [← Finset.sort_toFinset (S g) (· ≤ ·)]
    exact List.sum_toFinset _ (Finset.sort_nodup _ (· ≤ ·))
  rw [hsum]
  unfold pick
  generalize (S g).sort = l at hl ⊢
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l⟩⟩⟩⟩ <;> simp at hl
  simp [Finset.sum_range_succ]; ring

/-- The data of a 3-partition, unpacked: triples `S g` (`g < m`) with seats `pick S g r`. -/
structure Parts (a : List ℕ) (T : ℕ) (S : ℕ → Finset ℕ) : Prop where
  len : a.length = 3 * (a.length / 3)
  sub : ∀ g < a.length / 3, S g ⊆ Finset.range a.length
  card : ∀ g < a.length / 3, (S g).card = 3
  sum : ∀ g < a.length / 3, ∑ i ∈ S g, a.getD i 0 = T
  disj : ∀ g < a.length / 3, ∀ g' < a.length / 3, g ≠ g' → Disjoint (S g) (S g')
  cover : ∀ i < a.length, ∃ g < a.length / 3, i ∈ S g

theorem parts_of (h : THREE_PARTITION a T) : ∃ S, Parts a T S := by
  obtain ⟨h3, S, h1, h2, h4⟩ := h
  exact ⟨S, ⟨by omega, fun g hg => (h1 g hg).1, fun g hg => (h1 g hg).2.1,
    fun g hg => (h1 g hg).2.2, h2, h4⟩⟩

namespace Parts

variable (hS : Parts a T S)
include hS

theorem pick_lt (hg : g < a.length / 3) (hr : r < 3) : pick S g r < a.length :=
  Finset.mem_range.mp (hS.sub g hg (pick_mem (hS.card g hg) hr))

/-- Seats are injective: `pick S g r` determines `(g, r)`. -/
theorem pick_inj {g' r' : ℕ} (hg : g < a.length / 3) (hg' : g' < a.length / 3) (hr : r < 3)
    (hr' : r' < 3) (h : pick S g r = pick S g' r') : g = g' ∧ r = r' := by
  have hgg : g = g' := by
    by_contra hne
    have hd := hS.disj g hg g' hg' hne
    have h1 := pick_mem (hS.card g hg) hr
    have h2 := pick_mem (hS.card g' hg') hr'
    rw [h] at h1
    exact Finset.disjoint_left.mp hd h1 h2
  subst hgg
  exact ⟨rfl, pick_inj_r (hS.card g hg) hr hr' h⟩

/-- Every index is some seat. -/
theorem pick_cover {i : ℕ} (hi : i < a.length) :
    ∃ g < a.length / 3, ∃ r < 3, pick S g r = i := by
  obtain ⟨g, hg, hig⟩ := hS.cover i hi
  obtain ⟨r, hr, e⟩ := pick_surj (hS.card g hg) hig
  exact ⟨g, hg, r, hr, e⟩

theorem sum_pick_T (hg : g < a.length / 3) :
    ∑ r ∈ Finset.range 3, a.getD (pick S g r) 0 = T := by
  rw [sum_pick (fun i => a.getD i 0) (hS.card g hg), hS.sum g hg]

end Parts

end ThreeP

/-! ## Integer encodings (the totality branch) -/

/-- The syntactic checks of the totality branch (Appendix E, Theorem 2, *Totality*): the number
of items is divisible by 3, every `a_i > 0`, `T/4 < a_i < T/2`, and `Σ a_i = mT`. -/
def InDomain3P (a : List ℤ) (T : ℤ) : Prop :=
  a.length % 3 = 0 ∧ (∀ x ∈ a, 0 < x ∧ T < 4 * x ∧ 2 * x < T) ∧
    a.sum = ((a.length / 3 : ℕ) : ℤ) * T

instance (a : List ℤ) (T : ℤ) : Decidable (InDomain3P a T) := by
  unfold InDomain3P; infer_instance

/-- **`3-PARTITION` on integer encodings**: an encoding outside the problem's domain is a
no-instance (the convention of the totality branch). -/
def THREE_PARTITIONℤ (a : List ℤ) (T : ℤ) : Prop :=
  InDomain3P a T ∧ ∃ S : ℕ → Finset ℕ,
    (∀ g < a.length / 3, S g ⊆ Finset.range a.length ∧ (S g).card = 3 ∧
      ∑ i ∈ S g, a.getD i 0 = T) ∧
    (∀ g < a.length / 3, ∀ g' < a.length / 3, g ≠ g' → Disjoint (S g) (S g')) ∧
    (∀ i < a.length, ∃ g < a.length / 3, i ∈ S g)

namespace ThreeP

theorem getD_toNat {a : List ℤ} (hpos : ∀ x ∈ a, 0 < x) (i : ℕ) :
    (((a.map Int.toNat).getD i 0 : ℕ) : ℤ) = a.getD i 0 := by
  by_cases hi : i < a.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp only [List.getElem_map]
    exact Int.toNat_of_nonneg (le_of_lt (hpos _ (List.getElem_mem hi)))
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]
    rfl

theorem sum_toNat {a : List ℤ} (h : ∀ x ∈ a, 0 ≤ x) : ((a.map Int.toNat).sum : ℤ) = a.sum := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.forall_mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add, ih h.2, Int.toNat_of_nonneg h.1]

/-- In the domain and nonempty, the encoding satisfies the promise after `toNat`. -/
theorem promise_toNat {a : List ℤ} {T : ℤ} (h : InDomain3P a T) (hne : a ≠ []) :
    Promise3P (a.map Int.toNat) T.toNat := by
  obtain ⟨h3, hb, hs⟩ := h
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil a hne
  have hT : 0 < T := by have := hb x0 hx0; omega
  refine ⟨by simpa using h3, ?_, ?_⟩
  · have := sum_toNat (fun x hx => le_of_lt (hb x hx).1)
    rw [hs] at this
    simp only [List.length_map]
    have hTT : ((T.toNat : ℕ) : ℤ) = T := Int.toNat_of_nonneg hT.le
    rw [← hTT] at this
    exact_mod_cast this
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := hb x hx
    omega

/-- Membership in `THREE_PARTITIONℤ` is membership of the `toNat` encoding in
`THREE_PARTITION`, on the domain. -/
theorem toNat_iff {a : List ℤ} {T : ℤ} (h : InDomain3P a T) :
    THREE_PARTITIONℤ a T ↔ THREE_PARTITION (a.map Int.toNat) T.toNat := by
  have hpos : ∀ x ∈ a, 0 < x := fun x hx => (h.2.1 x hx).1
  have hsum : ∀ S : Finset ℕ, ((∑ i ∈ S, (a.map Int.toNat).getD i 0 : ℕ) : ℤ) =
      ∑ i ∈ S, a.getD i 0 := by
    intro S; push_cast; simp only [getD_toNat hpos]
  unfold THREE_PARTITIONℤ THREE_PARTITION
  simp only [List.length_map]
  by_cases hm : a.length / 3 = 0
  · -- no groups: both sides hold (the cover is vacuous: `|a| = 0`)
    have hl : a.length = 0 := by have := h.1; omega
    constructor
    · rintro ⟨-, S, -, -, -⟩
      exact ⟨h.1, fun _ => ∅, fun g hg => by omega, fun g hg => by omega, fun i hi => by omega⟩
    · rintro ⟨-, -⟩
      exact ⟨h, fun _ => ∅, fun g hg => by omega, fun g hg => by omega, fun i hi => by omega⟩
  · have hne : a ≠ [] := by rintro rfl; simp at hm
    obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil a hne
    have hT : 0 < T := by have := h.2.1 x0 hx0; omega
    have hTT : ((T.toNat : ℕ) : ℤ) = T := Int.toNat_of_nonneg hT.le
    have key : ∀ S : Finset ℕ, (∑ i ∈ S, (a.map Int.toNat).getD i 0 = T.toNat ↔
        ∑ i ∈ S, a.getD i 0 = T) := by
      intro S; rw [← hsum S, ← hTT]; exact_mod_cast Iff.rfl
    constructor
    · rintro ⟨-, S, h1, h2, h4⟩
      exact ⟨h.1, S, fun g hg => ⟨(h1 g hg).1, (h1 g hg).2.1, (key _).mpr (h1 g hg).2.2⟩, h2, h4⟩
    · rintro ⟨-, S, h1, h2, h4⟩
      exact ⟨h, S, fun g hg => ⟨(h1 g hg).1, (h1 g hg).2.1, (key _).mp (h1 g hg).2.2⟩, h2, h4⟩

/-- The empty encoding is a yes-instance. -/
theorem nil_iff (T : ℤ) : THREE_PARTITIONℤ [] T := by
  refine ⟨⟨rfl, by simp, by simp⟩, fun _ => ∅, fun g hg => by simp at hg, fun g hg => by simp at hg,
    fun i hi => by simp at hi⟩

/-- The fixed source yes-instance `((1,1,1), 3)` of the totality branch. -/
theorem yes_111 : THREE_PARTITION [1, 1, 1] 3 :=
  ⟨rfl, fun _ => {0, 1, 2}, fun g hg => by
    have : g = 0 := by simpa using hg
    subst this; refine ⟨by decide, by decide, by decide⟩,
    fun g hg g' hg' hne => by simp at hg hg'; omega,
    fun i hi => ⟨0, by simp, by simp at hi ⊢; omega⟩⟩

theorem promise_111 : Promise3P [1, 1, 1] 3 := by
  refine ⟨rfl, rfl, ?_⟩; simp

end ThreeP

/-! ## Deciding concrete instances -/

namespace ThreeP

/-- A seating certificate: `σ` lists `[|a|]` without repetition, and each consecutive block of
three sums to `T` (group `g` is `σ[3g], σ[3g+1], σ[3g+2]`). -/
def checkSeating (a : List ℕ) (T : ℕ) (σ : List ℕ) : Bool :=
  a.length % 3 == 0 && σ.length == a.length && decide σ.Nodup && σ.all (· < a.length) &&
    (List.range (a.length / 3)).all (fun g =>
      a.getD (σ.getD (3 * g) 0) 0 + a.getD (σ.getD (3 * g + 1) 0) 0 +
        a.getD (σ.getD (3 * g + 2) 0) 0 == T)

/-- A seating certificate proves `3-PARTITION`. -/
theorem of_seating {a : List ℕ} {T : ℕ} (σ : List ℕ) (h : checkSeating a T σ = true) :
    THREE_PARTITION a T := by
  simp only [checkSeating, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨h3, hlen⟩, hnd⟩, hlt⟩, hsum⟩ := h
  set n := a.length
  have hget : ∀ (p : ℕ) (hp : p < n), σ.getD p 0 = σ[p]'(by rw [hlen]; exact hp) :=
    fun p hp => by rw [List.getD_eq_getElem]
  have hinj : ∀ p < n, ∀ p' < n, σ.getD p 0 = σ.getD p' 0 → p = p' := by
    intro p hp p' hp' e
    rw [hget p hp, hget p' hp'] at e
    exact (List.Nodup.getElem_inj_iff hnd).mp e
  have hbd : ∀ p < n, σ.getD p 0 < n := fun p hp => by
    rw [hget p hp]; exact hlt _ (List.getElem_mem _)
  let S : ℕ → Finset ℕ := fun g => {σ.getD (3 * g) 0, σ.getD (3 * g + 1) 0, σ.getD (3 * g + 2) 0}
  have hne : ∀ g < n / 3, ∀ r < 3, ∀ r' < 3, r ≠ r' →
      σ.getD (3 * g + r) 0 ≠ σ.getD (3 * g + r') 0 := fun g hg r hr r' hr' h e =>
    h (by have := hinj _ (by omega) _ (by omega) e; omega)
  refine ⟨h3, S, fun g hg => ⟨?_, ?_, ?_⟩, fun g hg g' hg' hgg => ?_, fun i hi => ?_⟩
  · intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (hbd _ (by omega))
  · have h01 := hne g hg 0 (by norm_num) 1 (by norm_num) (by norm_num)
    have h02 := hne g hg 0 (by norm_num) 2 (by norm_num) (by norm_num)
    have h12 := hne g hg 1 (by norm_num) 2 (by norm_num) (by norm_num)
    simp only [add_zero] at h01 h02
    rw [Finset.card_eq_three]; exact ⟨_, _, _, h01, h02, h12, rfl⟩
  · have h01 := hne g hg 0 (by norm_num) 1 (by norm_num) (by norm_num)
    have h02 := hne g hg 0 (by norm_num) 2 (by norm_num) (by norm_num)
    have h12 := hne g hg 1 (by norm_num) 2 (by norm_num) (by norm_num)
    simp only [add_zero] at h01 h02
    simp only [S]
    rw [Finset.sum_insert (by
        rw [Finset.mem_insert, Finset.mem_singleton]; exact fun h => h.elim h01 h02),
      Finset.sum_insert (by rw [Finset.mem_singleton]; exact h12),
      Finset.sum_singleton, ← add_assoc]
    exact hsum g hg
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with e | e | e <;>
      exact hgg (by have := hinj _ (by omega) _ (by omega) e; omega)
  · -- `σ` is a permutation of `[n]`
    have hsub : σ.toFinset ⊆ Finset.range n := fun x hx =>
      Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
    have hcard : (Finset.range n).card ≤ σ.toFinset.card := by
      rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_range]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : i ∈ σ := List.mem_toFinset.mp (heq ▸ Finset.mem_range.mpr hi)
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hmem
    refine ⟨p / 3, by omega, ?_⟩
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    have : p = 3 * (p / 3) + p % 3 := by omega
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
    · left; rw [hget _ (by omega)]; congr 1; omega
    · right; left; rw [hget _ (by omega)]; congr 1; omega
    · right; right; rw [hget _ (by omega)]; congr 1; omega

instance (a : List ℕ) (T : ℕ) : Decidable (Promise3P a T) := by
  unfold Promise3P; infer_instance

/-- No three distinct entries sum to `T`. -/
def checkNoTriple (a : List ℕ) (T : ℕ) : Bool :=
  (List.range a.length).all fun i => (List.range a.length).all fun j =>
    (List.range a.length).all fun l =>
      i == j || i == l || j == l || a.getD i 0 + a.getD j 0 + a.getD l 0 != T

/-- If no three distinct entries sum to `T` (and `m ≥ 1`), there is no 3-partition. -/
theorem not_of_noTriple {a : List ℕ} {T : ℕ} (hm : 0 < a.length / 3)
    (h : ∀ i < a.length, ∀ j < a.length, ∀ l < a.length, i ≠ j → i ≠ l → j ≠ l →
      a.getD i 0 + a.getD j 0 + a.getD l 0 ≠ T) : ¬ THREE_PARTITION a T := by
  rintro ⟨-, S, h1, -, -⟩
  obtain ⟨hsub, hc, hs⟩ := h1 0 hm
  obtain ⟨x, y, z, hxy, hxz, hyz, hS⟩ := Finset.card_eq_three.mp hc
  rw [hS] at hsub hs
  have hx := Finset.mem_range.mp (hsub (Finset.mem_insert_self x _))
  have hy := Finset.mem_range.mp (hsub (Finset.mem_insert_of_mem (Finset.mem_insert_self y _)))
  have hz := Finset.mem_range.mp
    (hsub (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))))
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, ← add_assoc] at hs
  exact h x hx y hy z hz hxy hxz hyz hs

theorem not_of_checkNoTriple {a : List ℕ} {T : ℕ} (hm : 0 < a.length / 3)
    (h : checkNoTriple a T = true) : ¬ THREE_PARTITION a T := by
  refine not_of_noTriple hm (fun i hi j hj l hl hij hil hjl => ?_)
  simp only [checkNoTriple, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h i hi j hj l hl with ((h1 | h1) | h1) | h1
  · exact absurd h1 hij
  · exact absurd h1 hil
  · exact absurd h1 hjl
  · exact h1

end ThreeP

end Homm3
