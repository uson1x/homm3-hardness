import Homm3.Gadgets

/-!
# Session 5, target 2. The geometry of Lemma D.4, step 4: scaling and separation

Paper: Appendix D.4, step 4 (`main.md:1499–1541`) and the parity paragraph of step 5.

* Grid points `GP = ℤ × ℤ` of the orthogonal drawing, the four axis directions `dirV p` in the
  port order of Appendix C (`0` up, `1` right, `2` down, `3` left; rows grow downward).
* The scaling `φ(i, j) = (λ i + ω, λ j + ω)` with `λ = 20`, `ω = 6` (the drawing is taken with
  its bounding box at the origin, so `i_min = j_min = 0`), and `mv h t d = h + t·d`.
* **(SEP)** at the level of unit segments: a point of a scaled unit segment is at `L∞`
  distance `≥ λ = 20` from the image of every grid point that is not an endpoint of the segment
  (`sep_pt`), and points of two scaled unit segments without a common endpoint are `≥ 20`
  apart (`sep_seg`).  Images of distinct grid points are `≥ 20` apart (`sep_vv`).
* **Two runs from one vertex** (`sep_rays`): points at parameters `t, t' ≥ ρ + 1 = 5` on two
  different axis directions from the same centre are `≥ 5` apart — the paper's
  "`max(t, t')` (perpendicular axes) or `t + t'` (opposite axes)".
* A box hex (`L∞ ≤ ρ = 4` from the centre) within `L∞ 1` of a run point at parameter `≥ 5`
  lies on the box side of that run: its coordinate along the run is exactly `4`
  (`box_ray`).
-/

namespace Homm3

namespace Embed

open Gadgets

/-- A point of the drawing grid. -/
abbrev GP := ℤ × ℤ

/-- The four axis directions in the port order of Appendix C (`Gadgets.ports`): `0` up (`T`),
`1` right (`R`), `2` down (`B`), `3` left (`L`); rows grow downward. -/
def dirV : ℕ → GP
  | 0 => (0, -1)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | _ => (-1, 0)

/-- A unit axis step. -/
def IsUnit (d : GP) : Prop := d = (0, -1) ∨ d = (1, 0) ∨ d = (0, 1) ∨ d = (-1, 0)

instance (d : GP) : Decidable (IsUnit d) := by unfold IsUnit; infer_instance

theorem isUnit_dirV (p : ℕ) : IsUnit (dirV p) := by
  unfold IsUnit dirV
  rcases p with _ | _ | _ | p <;> simp

/-- Every unit step is `dirV p` for exactly one `p < 4`. -/
theorem isUnit_iff (d : GP) : IsUnit d ↔ ∃ p < 4, dirV p = d := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩, ⟨3, by norm_num, rfl⟩]
  · rintro ⟨p, -, rfl⟩; exact isUnit_dirV p

theorem dirV_inj {p p' : ℕ} (hp : p < 4) (hp' : p' < 4) (h : dirV p = dirV p') : p = p' := by
  interval_cases p <;> interval_cases p' <;> simp_all [dirV]

/-- The constants of step 4: scale `λ = 20`, box radius `ρ = 4`, offset `ω = 6`. -/
def lam : ℤ := 20
def rho : ℤ := 4
def omega : ℤ := 6

/-- **The scaling `φ`** (step 4), for a drawing whose bounding box starts at the origin. -/
def φ (a : GP) : Hex := ⟨20 * a.1 + 6, 20 * a.2 + 6⟩

/-- `h + t·d`. -/
def mv (h : Hex) (t : ℤ) (d : GP) : Hex := ⟨h.x + t * d.1, h.y + t * d.2⟩

@[simp] theorem mv_x (h : Hex) (t : ℤ) (d : GP) : (mv h t d).x = h.x + t * d.1 := rfl
@[simp] theorem mv_y (h : Hex) (t : ℤ) (d : GP) : (mv h t d).y = h.y + t * d.2 := rfl
@[simp] theorem φ_x (a : GP) : (φ a).x = 20 * a.1 + 6 := rfl
@[simp] theorem φ_y (a : GP) : (φ a).y = 20 * a.2 + 6 := rfl

theorem mv_zero (h : Hex) (d : GP) : mv h 0 d = h := by ext <;> simp

/-- Images sit on even rows (`λ`, `ω` even) — the parity requirement of step 5. -/
theorem φ_even (a : GP) : (φ a).y % 2 = 0 := by simp; omega

/-! ## `L∞` in linear form -/

theorem le_linf {k : ℤ} {p q : Hex} :
    k ≤ linf p q ↔ k ≤ p.x - q.x ∨ k ≤ q.x - p.x ∨ k ≤ p.y - q.y ∨ k ≤ q.y - p.y := by
  unfold linf
  simp only [le_max_iff, le_abs']
  omega

theorem linf_le {k : ℤ} {p q : Hex} :
    linf p q ≤ k ↔ p.x - q.x ≤ k ∧ q.x - p.x ≤ k ∧ p.y - q.y ≤ k ∧ q.y - p.y ≤ k := by
  unfold linf
  simp only [max_le_iff, abs_le]
  omega

theorem linf_le_one_of_adj {p q : Hex} (h : p = q ∨ Hex.Adj p q) : linf p q ≤ 1 := by
  rcases h with rfl | h
  · rw [linf_le]; omega
  · rw [adj_linf h]

theorem linf_mv (h : Hex) {t : ℤ} (ht : 0 ≤ t) {d : GP} (hd : IsUnit d) : linf (mv h t d) h = t := by
  apply le_antisymm
  · rw [linf_le]; rcases hd with rfl | rfl | rfl | rfl <;>
      simp only [mv_x, mv_y, mul_zero, mul_one, mul_neg, add_zero] <;> omega
  · rw [le_linf]; rcases hd with rfl | rfl | rfl | rfl <;>
      simp only [mv_x, mv_y, mul_zero, mul_one, mul_neg, add_zero] <;> omega

/-! ## (SEP) at the level of unit segments -/

/-- Images of distinct grid points are `λ = 20` apart. -/
theorem sep_vv {a c : GP} (h : a ≠ c) : 20 ≤ linf (φ a) (φ c) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨c1, c2⟩ := c
  simp only [ne_eq, Prod.mk.injEq, not_and_or] at h
  rw [le_linf]; simp only [φ_x, φ_y]; omega

/-- A point of the scaled unit segment `[φ a, φ (a + d)]` is `≥ 20` from the image of any grid
point other than `a`, `a + d`. -/
theorem sep_pt {a c d : GP} {t : ℤ} (hd : IsUnit d) (ht0 : 0 ≤ t) (ht : t ≤ 20)
    (h1 : c ≠ a) (h2 : c ≠ a + d) : 20 ≤ linf (mv (φ a) t d) (φ c) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨c1, c2⟩ := c
  rw [le_linf]
  rcases hd with rfl | rfl | rfl | rfl <;>
  simp only [ne_eq, Prod.mk.injEq, Prod.mk_add_mk, not_and_or] at h1 h2 <;>
  simp only [mv_x, mv_y, φ_x, φ_y] <;> omega

/-- Points of two scaled unit segments without a common endpoint are `≥ 20` apart. -/
theorem sep_seg {a a' d d' : GP} {t t' : ℤ} (hd : IsUnit d) (hd' : IsUnit d')
    (ht0 : 0 ≤ t) (ht : t ≤ 20) (ht0' : 0 ≤ t') (ht' : t' ≤ 20)
    (h1 : a ≠ a') (h2 : a ≠ a' + d') (h3 : a + d ≠ a') (h4 : a + d ≠ a' + d') :
    20 ≤ linf (mv (φ a) t d) (mv (φ a') t' d') := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := a'
  rw [le_linf]
  rcases hd with rfl | rfl | rfl | rfl <;> rcases hd' with rfl | rfl | rfl | rfl <;>
  simp only [ne_eq, Prod.mk.injEq, Prod.mk_add_mk, not_and_or] at h1 h2 h3 h4 <;>
  simp only [mv_x, mv_y, φ_x, φ_y] <;> omega

/-- **Two runs from one centre** along different directions, at parameters `≥ 5`, are `≥ 5`
apart. -/
theorem sep_rays {c : Hex} {d d' : GP} {t t' : ℤ} (hd : IsUnit d) (hd' : IsUnit d') (hne : d ≠ d')
    (ht : 5 ≤ t) (ht' : 5 ≤ t') : 5 ≤ linf (mv c t d) (mv c t' d') := by
  rw [le_linf]
  rcases hd with rfl | rfl | rfl | rfl <;> rcases hd' with rfl | rfl | rfl | rfl <;>
  simp_all <;> omega

/-- A hex of the box of radius `4` around `c` within `L∞ 1` of the run point `c + t·d`,
`t ≥ 5`, has coordinate exactly `4` along `d` (and `t = 5`). -/
theorem box_ray {c h : Hex} {d : GP} {t : ℤ} (hd : IsUnit d) (ht : 5 ≤ t)
    (hb : linf h c ≤ 4) (hh : linf h (mv c t d) ≤ 1) :
    (h.x - c.x) * d.1 + (h.y - c.y) * d.2 = 4 ∧ t = 5 := by
  rw [linf_le] at hb hh
  rcases hd with rfl | rfl | rfl | rfl <;> simp at hh ⊢ <;> omega

/-! ## The adapters of Appendix C, in the form step 5 uses -/

/-- The adapter for the missing direction `m` (`0` top, `1` right, `2` bottom, `3` left). -/
def armsOf : ℕ → List (ℕ × List (ℕ × ℕ))
  | 0 => armsTop
  | 1 => armsRight
  | 2 => armsBottom
  | _ => armsLeft

/-- The port cell of direction `p` in the local frame: `(4, 4) + 4·dirV p`. -/
def portCell (p : ℕ) : ℕ × ℕ := ports.getD p (0, 0)

/-- An arm is a path: consecutive cells adjacent. -/
def ChainAdj : List (ℕ × ℕ) → Prop
  | [] => True
  | [_] => True
  | c :: c' :: l => Hex.Adj (cell c) (cell c') ∧ ChainAdj (c' :: l)

instance : DecidablePred ChainAdj := fun l => by
  induction l with
  | nil => exact isTrue trivial
  | cons c l ih =>
    cases l with
    | nil => exact isTrue trivial
    | cons c' l => unfold ChainAdj; exact instDecidableAnd

/-! **The local facts of the four adapters** that the universal lemma uses, checked in the kernel
for every missing direction `m < 4`: the arms sit at the three ports other than `m`, one each;
each arm is a path inside the box from its port cell; no arm cell is `Z = (4, 4)`, and only its
last cell is adjacent to `Z`; the last cells are the three dockings; arms of different ports share
and touch no cell; a cell on the side `p` of the box (coordinate `4` along `dirV p`) belongs to the
arm of port `p`. -/

theorem arms_ports : ∀ m < 4, (armsOf m).map Prod.fst = (List.range 4).filter (· != m) := by
  decide +kernel

theorem arms_head : ∀ m < 4, ∀ a ∈ armsOf m, a.2.head? = some (portCell a.1) := by
  decide +kernel

theorem arms_chain : ∀ m < 4, ∀ a ∈ armsOf m, ChainAdj a.2 := by
  decide +kernel

theorem arms_cells : ∀ m < 4, ∀ a ∈ armsOf m, ∀ c ∈ a.2, c.1 < 9 ∧ c.2 < 9 ∧ c ≠ (4, 4) := by
  decide +kernel

theorem arms_zadj : ∀ m < 4, ∀ a ∈ armsOf m, ∀ c ∈ a.2,
    Hex.Adj (cell c) (cell (4, 4)) → a.2.getLast? = some c := by
  decide +kernel

theorem arms_side : ∀ m < 4, ∀ a ∈ armsOf m, ∀ c ∈ a.2, ∀ p < 4,
    ((c.1 : ℤ) - 4) * (dirV p).1 + ((c.2 : ℤ) - 4) * (dirV p).2 = 4 → a.1 = p := by
  decide +kernel

theorem arms_last : ∀ m < 4, ∀ a ∈ armsOf m, ∃ c ∈ docks, a.2.getLast? = some c := by
  decide +kernel

theorem arms_docks : ∀ m < 4, ∀ c ∈ docks, ∃ a ∈ armsOf m, a.2.getLast? = some c := by
  decide +kernel

theorem arms_apart : ∀ m < 4, ∀ a ∈ armsOf m, ∀ b ∈ armsOf m, a.1 ≠ b.1 →
    ∀ c ∈ a.2, ∀ c' ∈ b.2, c ≠ c' ∧ ¬ Hex.Adj (cell c) (cell c') := by
  decide +kernel

/-- The port cells are `(4, 4) + 4·dirV p`. -/
theorem portCell_eq : ∀ p < 4, ((portCell p).1 : ℤ) = 4 + 4 * (dirV p).1 ∧
    ((portCell p).2 : ℤ) = 4 + 4 * (dirV p).2 := by decide

/-! ## Walks along lists -/

/-- `a` and `b` are joined by a walk inside `A`: the relation of (I2)'s connectivity. -/
def Lnk (A : Finset Hex) (a b : Hex) : Prop :=
  a ∈ A ∧ b ∈ A ∧ Relation.ReflTransGen (fun x y => Hex.Adj x y ∧ y ∈ A) a b

namespace Lnk

variable {A : Finset Hex}

theorem refl {a : Hex} (h : a ∈ A) : Lnk A a a := ⟨h, h, .refl⟩

theorem trans {a b c : Hex} (h1 : Lnk A a b) (h2 : Lnk A b c) : Lnk A a c :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem step {a b : Hex} (ha : a ∈ A) (hb : b ∈ A) (h : Hex.Adj a b) : Lnk A a b :=
  ⟨ha, hb, .single ⟨h, hb⟩⟩

theorem symm {a b : Hex} (h : Lnk A a b) : Lnk A b a :=
  ⟨h.2.1, h.1, rtg_symm_in h.1 h.2.2⟩

end Lnk

/-! ## Unit steps in the hex grid -/

theorem adj_mv_succ (h : Hex) (t : ℤ) {d : GP} (hd : IsUnit d) :
    Hex.Adj (mv h t d) (mv h (t + 1) d) := by
  have := square_in_hex (mv h t d).x (mv h t d).y
  rcases hd with rfl | rfl | rfl | rfl
  · have e : mv h (t + 1) (0, -1) = ⟨(mv h t (0, -1)).x, (mv h t (0, -1)).y - 1⟩ := by
      ext <;> simp; ring
    rw [e]; exact this.2.2.2
  · have e : mv h (t + 1) (1, 0) = ⟨(mv h t (1, 0)).x + 1, (mv h t (1, 0)).y⟩ := by
      ext <;> simp; ring
    rw [e]; exact this.1
  · have e : mv h (t + 1) (0, 1) = ⟨(mv h t (0, 1)).x, (mv h t (0, 1)).y + 1⟩ := by
      ext <;> simp; ring
    rw [e]; exact this.2.2.1
  · have e : mv h (t + 1) (-1, 0) = ⟨(mv h t (-1, 0)).x - 1, (mv h t (-1, 0)).y⟩ := by
      ext <;> simp; ring
    rw [e]; exact this.2.1

/-- A run `c, c + d, …, c + t·d` inside `A`: its far end is linked to `c`. -/
theorem lnk_run {A : Finset Hex} (c : Hex) {d : GP} (hd : IsUnit d) :
    ∀ t : ℕ, (∀ τ : ℕ, τ ≤ t → mv c τ d ∈ A) → Lnk A (mv c t d) c
  | 0, h => by
    have h0 := h 0 le_rfl
    rw [Nat.cast_zero, mv_zero] at h0 ⊢
    exact Lnk.refl h0
  | t + 1, h => by
    have ih := lnk_run c hd t (fun τ hτ => h τ (by omega))
    have ha := adj_mv_succ c t hd
    have hs := Lnk.step (h (t + 1) le_rfl) (h t (by omega))
      (by push_cast; exact Hex.adj_symm ha)
    exact hs.trans ih

/-- `φ (a + d) = φ a + 20·d`. -/
theorem φ_add (a d : GP) : φ (a + d) = mv (φ a) 20 d := by
  ext <;> simp [Prod.fst_add, Prod.snd_add] <;> ring

/-! ## Routes: unit-step grid paths and their scaled points -/

/-- An edge of `G'` in the drawing: source `u` (an element-path vertex), target `v`, and the route
as the list of grid points it visits (unit steps, from `pos u` to `pos v`). -/
structure DEdge where
  u : ℕ
  v : ℕ
  r : List GP
deriving DecidableEq, Repr

namespace DEdge

variable (ε : DEdge)

/-- Number of unit segments. -/
def k : ℕ := ε.r.length - 1

/-- Route point `j`. -/
def rp (j : ℕ) : GP := ε.r.getD j (0, 0)

/-- Direction of unit segment `j`. -/
def sd (j : ℕ) : GP := ε.rp (j + 1) - ε.rp j

/-- **The scaled route**, parametrised by `s ∈ [0, 20k]`: the point at parameter `s % 20` on the
scaled unit segment `s / 20` (step 4: "a unit segment of `Γ` becomes the `λ + 1` hexes on the
corresponding axis-aligned run"). -/
def pt (s : ℕ) : Hex := mv (φ (ε.rp (s / 20))) ((s % 20 : ℕ) : ℤ) (ε.sd (s / 20))

/-- Direction of the route at its source and at its target. -/
def du : GP := ε.sd 0
def dv : GP := ε.rp (ε.k - 1) - ε.rp ε.k

/-- **The corridor** of the edge: the scaled route truncated at the two boxes, i.e. the points
at parameters `5 ≤ s ≤ 20k − 5` (`corr_iff`: exactly the route hexes at `L∞` distance `> ρ`
from both end images). -/
def corr : List Hex := (List.range (20 * ε.k - 9)).map (fun s => ε.pt (s + 5))

/-- A route: at least one unit segment, unit steps, no repeated grid point. -/
structure OK : Prop where
  len : 2 ≤ ε.r.length
  unit : ∀ j < ε.k, IsUnit (ε.sd j)
  nodup : ε.r.Nodup

variable {ε}

theorem rp_succ (j : ℕ) : ε.rp (j + 1) = ε.rp j + ε.sd j := by
  simp [sd]

theorem rp_mem (h : ε.OK) {j : ℕ} (hj : j ≤ ε.k) : ε.rp j ∈ ε.r := by
  have := h.len
  unfold rp
  unfold k at hj
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem rp_inj (h : ε.OK) {i j : ℕ} (hi : i ≤ ε.k) (hj : j ≤ ε.k) (he : ε.rp i = ε.rp j) :
    i = j := by
  have := h.len
  unfold rp at he
  unfold k at hi hj
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
  exact (h.nodup.getElem_inj_iff).mp he

theorem k_pos (h : ε.OK) : 1 ≤ ε.k := by have := h.len; unfold k; omega

theorem mem_rp {x : GP} (hx : x ∈ ε.r) : ∃ j ≤ ε.k, ε.rp j = x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  refine ⟨j, by unfold k; omega, ?_⟩
  unfold rp; rw [List.getD_eq_getElem]

/-- Every point of the scaled route lies on a scaled unit segment `j < k`, at parameter `t ≤ 20`. -/
theorem pt_seg (h : ε.OK) {s : ℕ} (hs : s ≤ 20 * ε.k) :
    ∃ j < ε.k, ∃ t : ℕ, t ≤ 20 ∧ s = 20 * j + t ∧ ε.pt s = mv (φ (ε.rp j)) t (ε.sd j) := by
  have hk := k_pos h
  rcases Nat.lt_or_ge s (20 * ε.k) with hlt | hge
  · exact ⟨s / 20, by omega, s % 20, by omega, by omega, rfl⟩
  · have hs' : s = 20 * ε.k := by omega
    refine ⟨ε.k - 1, by omega, 20, le_rfl, by omega, ?_⟩
    subst hs'
    have h1 : 20 * ε.k / 20 = ε.k := by omega
    have h2 : 20 * ε.k % 20 = 0 := by omega
    have h3 : ε.k = ε.k - 1 + 1 := by omega
    rw [pt, h1, h2, Nat.cast_zero, mv_zero]
    push_cast
    rw [← φ_add, ← rp_succ, ← h3]

theorem pt_zero : ε.pt 0 = φ (ε.rp 0) := by simp [pt, mv_zero]

theorem pt_end : ε.pt (20 * ε.k) = φ (ε.rp ε.k) := by
  have : 20 * ε.k / 20 = ε.k := by omega
  simp [pt, this, mv_zero]

/-- The first segment: `pt s = φ(pos u) + s·du` for `s ≤ 20`. -/
theorem pt_first (h : ε.OK) {s : ℕ} (hs : s ≤ 20) : ε.pt s = mv (φ (ε.rp 0)) s ε.du := by
  have hk := k_pos h
  rcases Nat.lt_or_ge s 20 with hlt | hge
  · have h1 : s / 20 = 0 := by omega
    have h2 : s % 20 = s := by omega
    simp only [pt, h1, h2, du]
  · have hs' : s = 20 := by omega
    subst hs'
    simp only [pt, Nat.reduceDiv, Nat.reduceMod, Nat.cast_zero, mv_zero, du]
    rw [show (1 : ℕ) = 0 + 1 from rfl, rp_succ, φ_add]; rfl

theorem dv_eq (h : ε.OK) : ε.dv = - ε.sd (ε.k - 1) ∧ ε.rp ε.k = ε.rp (ε.k - 1) + ε.sd (ε.k - 1) := by
  have hk := k_pos h
  have hkk : ε.k = ε.k - 1 + 1 := by omega
  have hr : ε.rp ε.k = ε.rp (ε.k - 1) + ε.sd (ε.k - 1) := by
    conv_lhs => rw [hkk]
    exact rp_succ _
  refine ⟨?_, hr⟩
  simp only [dv, hr]; abel

/-- The last segment: `pt s = φ(pos v) + (20k − s)·dv` for `20k − 20 ≤ s ≤ 20k`. -/
theorem pt_last (h : ε.OK) {s : ℕ} (hs1 : 20 * ε.k - 20 ≤ s) (hs2 : s ≤ 20 * ε.k) :
    ε.pt s = mv (φ (ε.rp ε.k)) ((20 * ε.k - s : ℕ) : ℤ) ε.dv := by
  have hk := k_pos h
  obtain ⟨hdv, hr⟩ := dv_eq h
  rcases Nat.lt_or_ge s (20 * ε.k) with hlt | hge
  · have h1 : s / 20 = ε.k - 1 := by omega
    have e1 : ((20 * ε.k - s : ℕ) : ℤ) = 20 - ((s % 20 : ℕ) : ℤ) := by omega
    rw [pt, h1, hr, hdv, e1]
    ext <;> simp [Prod.fst_add, Prod.snd_add] <;> ring
  · have hs' : s = 20 * ε.k := by omega
    subst hs'
    rw [pt_end]; simp [mv_zero]

/-- Consecutive scaled points are adjacent. -/
theorem pt_adj (h : ε.OK) {s : ℕ} (hs : s < 20 * ε.k) : Hex.Adj (ε.pt s) (ε.pt (s + 1)) := by
  have hj : s / 20 < ε.k := by omega
  have hu := h.unit _ hj
  rcases Nat.lt_or_ge (s % 20 + 1) 20 with hlt | hge
  · have h1 : (s + 1) / 20 = s / 20 := by omega
    have h2 : (s + 1) % 20 = s % 20 + 1 := by omega
    rw [pt, pt, h1, h2]; push_cast
    exact adj_mv_succ _ _ hu
  · have h1 : (s + 1) / 20 = s / 20 + 1 := by omega
    have h2 : (s + 1) % 20 = 0 := by omega
    have h3 : s % 20 = 19 := by omega
    rw [pt, pt, h1, h2, h3, Nat.cast_zero, mv_zero, rp_succ, φ_add]
    exact adj_mv_succ _ 19 hu

/-- A point of segment `j` is `≥ 20` from every grid point other than the segment's ends. -/
theorem pt_far (h : ε.OK) {j : ℕ} (hj : j < ε.k) {t : ℕ} (ht : t ≤ 20) {c : GP}
    (h1 : c ≠ ε.rp j) (h2 : c ≠ ε.rp (j + 1)) : 20 ≤ linf (mv (φ (ε.rp j)) t (ε.sd j)) (φ c) := by
  apply sep_pt (h.unit j hj) (by omega) (by exact_mod_cast ht) h1
  rwa [← rp_succ]

/-- A segment containing the source's point is the first one. -/
theorem seg_at_u (h : ε.OK) {j : ℕ} (hj : j < ε.k) (hx : ε.rp 0 = ε.rp j ∨ ε.rp 0 = ε.rp (j + 1)) :
    j = 0 := by
  rcases hx with hx | hx
  · exact (rp_inj h (by omega) (by omega) hx).symm
  · have := rp_inj h (by omega) (by omega) hx; omega

/-- A segment containing the target's point is the last one. -/
theorem seg_at_v (h : ε.OK) {j : ℕ} (hj : j < ε.k) (hx : ε.rp ε.k = ε.rp j ∨ ε.rp ε.k = ε.rp (j + 1)) :
    j = ε.k - 1 := by
  rcases hx with hx | hx
  · have := rp_inj h (by omega) (by omega) hx; omega
  · have := rp_inj h (by omega) (by omega) hx; omega

theorem du_unit (h : ε.OK) : IsUnit ε.du := h.unit 0 (k_pos h)

theorem dv_unit (h : ε.OK) : IsUnit ε.dv := by
  have hk := k_pos h
  have hu := h.unit (ε.k - 1) (by omega)
  rw [(dv_eq h).1]
  rcases hu with h | h | h | h <;> rw [h] <;> simp [IsUnit]

/-- **A route point near an end of its own route**: a point of segment `j` whose segment contains
the source's (target's) grid point is on the run from that end, at parameter `s` (`20k − s`). -/
theorem near_u (h : ε.OK) {s j t : ℕ} (hj : j < ε.k) (hst : s = 20 * j + t) (ht : t ≤ 20)
    (hx : ε.rp 0 = ε.rp j ∨ ε.rp 0 = ε.rp (j + 1)) : s ≤ 20 ∧ ε.pt s = mv (φ (ε.rp 0)) s ε.du := by
  have := seg_at_u h hj hx
  subst this
  exact ⟨by omega, pt_first h (by omega)⟩

theorem near_v (h : ε.OK) {s j t : ℕ} (hj : j < ε.k) (hst : s = 20 * j + t) (ht : t ≤ 20)
    (hx : ε.rp ε.k = ε.rp j ∨ ε.rp ε.k = ε.rp (j + 1)) :
    20 * ε.k - 20 ≤ s ∧ s ≤ 20 * ε.k ∧
      ε.pt s = mv (φ (ε.rp ε.k)) ((20 * ε.k - s : ℕ) : ℤ) ε.dv := by
  have := seg_at_v h hj hx
  subst this
  have hk := k_pos h
  exact ⟨by omega, by omega, pt_last h (by omega) (by omega)⟩

/-- `L∞` distance of a route point from the source's image: `s` on the first segment, `≥ 20`
beyond it. -/
theorem linf_u (h : ε.OK) {s : ℕ} (hs : s ≤ 20 * ε.k) :
    min (s : ℤ) 20 ≤ linf (ε.pt s) (φ (ε.rp 0)) := by
  obtain ⟨j, hj, t, ht, hst, hpt⟩ := pt_seg h hs
  by_cases hx : ε.rp 0 = ε.rp j ∨ ε.rp 0 = ε.rp (j + 1)
  · obtain ⟨hs20, hp⟩ := near_u h hj hst ht hx
    rw [hp, linf_mv _ (by omega) (du_unit h)]; exact min_le_left _ _
  · push Not at hx
    rw [hpt]; exact (min_le_right _ _).trans (pt_far h hj ht hx.1 hx.2)

theorem linf_v (h : ε.OK) {s : ℕ} (hs : s ≤ 20 * ε.k) :
    min ((20 * ε.k - s : ℕ) : ℤ) 20 ≤ linf (ε.pt s) (φ (ε.rp ε.k)) := by
  obtain ⟨j, hj, t, ht, hst, hpt⟩ := pt_seg h hs
  by_cases hx : ε.rp ε.k = ε.rp j ∨ ε.rp ε.k = ε.rp (j + 1)
  · obtain ⟨-, -, hp⟩ := near_v h hj hst ht hx
    rw [hp, linf_mv _ (by omega) (dv_unit h)]; exact min_le_left _ _
  · push Not at hx
    rw [hpt]; exact (min_le_right _ _).trans (pt_far h hj ht hx.1 hx.2)

/-- **The corridor is the scaled route minus the two end boxes** (step 5: "truncates every
corridor at the boxes at its ends"): for `s ≤ 20k`, `5 ≤ s ≤ 20k − 5` iff the point is at
`L∞ > ρ = 4` from both end images. -/
theorem corr_iff (h : ε.OK) {s : ℕ} (hs : s ≤ 20 * ε.k) :
    (5 ≤ s ∧ s ≤ 20 * ε.k - 5) ↔
      (4 < linf (ε.pt s) (φ (ε.rp 0)) ∧ 4 < linf (ε.pt s) (φ (ε.rp ε.k))) := by
  have hk := k_pos h
  have hu := linf_u h hs
  have hv := linf_v h hs
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨lt_of_lt_of_le ?_ hu, lt_of_lt_of_le ?_ hv⟩
    · rw [lt_min_iff]; constructor <;> omega
    · rw [lt_min_iff]; constructor <;> omega
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hc
      have hp := pt_first h (s := s) (by omega)
      rw [hp, linf_mv _ (by omega) (du_unit h)] at h1; omega
    · by_contra hc
      have hp := pt_last h (s := s) (by omega) hs
      rw [hp, linf_mv _ (by omega) (dv_unit h)] at h2; omega

theorem mem_corr {x : Hex} :
    x ∈ ε.corr ↔ ∃ s, 5 ≤ s ∧ s ≤ 20 * ε.k - 5 ∧ 1 ≤ ε.k ∧ x = ε.pt s := by
  unfold corr
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s + 5, by omega, by omega, by omega, rfl⟩
  · rintro ⟨s, h1, h2, h3, rfl⟩; exact ⟨s - 5, by omega, by rw [Nat.sub_add_cancel h1]⟩

end DEdge

end Embed

end Homm3
