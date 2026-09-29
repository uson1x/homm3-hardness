import Homm3.Theorem3

/-!
# Session 4, targets 2 and 4. Boards as data, a kernel checker for (I1)–(I4), a fixed yes-board

A board is shipped as `BoardData`: dimensions `W × H`, one big natural number `lab` whose byte
`i = x + W·y` labels the hex `(x, y)` (`0` impassable, `e + 1` region of element `e`,
`128 + g` the enemy hex of member `g`), one big natural number `dist` whose 16-bit field `i`
is a BFS distance of the hex from `p_e` inside its region (a connectivity certificate), the
deployment hexes `p`, the enemy hexes `z`, and the speed `σ`.  The kernel reads a label with
one shift and one `mod` (GMP-accelerated), so checking a `48 × 48` board is cheap.

* `BoardData.toBoard` — the abstract `X3CBoard` (regions = hexes with label `e + 1`,
  impassable = label `0`, dockings = the neighbour of `z_g` labelled `e + 1`).
* `BoardData.check` — a Bool checker, local per hex; **`BoardData.check_sound`**:
  `check D q CL = true → (toBoard D).Inv (toX3C q CL)`.  `wfOK_sound` does the same for
  `X3C.WF`.  So `decide +kernel` on the checker certifies (I1)–(I4) for a concrete board.
* `D1` — a `5 × 5` yes-board for `X = {0, 1, 2}`, `C = {{0, 1, 2}}` (the enemy gadget alone,
  each docking its own one-hex region and deployment hex), used by the total form.
* **`theorem3_total`**, **`cor31_total`**: total reductions on encodings `(q, C, board data)`:
  a well-formed instance with a board passing the checker maps to `G_3`, `q = 0` to the fixed
  yes-instance `G_3(D1)`, everything else to `Corridor.Gno`.  The source problem is thereby
  "`X3C` with a certified board" — what Lemma D.4 produces from a planar instance; Lemma D.4
  itself (that every planar instance has such a board, computable in polynomial time) is not
  formalized.
* `coverCheck` with **`exactCover_iff_check`**: exact cover decided over the sublists of `C`.
* The checker skips impassable hexes by their label byte (`labIdx`), so its cost is dominated
  by the free hexes.  `ofPacked` builds a board from its free hexes only (44-bit records
  `i·2^24 + label·2^16 + dist`, decoded by the kernel by halving, recursion depth `log k`);
  the boards of Lemma D.4's construction (up to `333 × 393`) are shipped this way.
* `YesV` / `NoV` with `yes_of` / `no_of`: the verdict package of the cross-checks — from a
  passing `check` and a `coverCheck` value, (I1)–(I4), the X3C answer, the game answer through
  `theorem3` at `hp 5, def 41` and at `G3pub`, Corollary 3.1, and all-ones uniqueness.
-/

namespace Homm3

/-- A board shipped as data. -/
structure BoardData where
  W : ℕ
  H : ℕ
  lab : ℕ
  dist : ℕ
  p : List (ℕ × ℕ)
  z : List (ℕ × ℕ)
  σ : ℕ

namespace BoardData

variable (D : BoardData)

def toHex (pr : ℕ × ℕ) : Hex := ⟨pr.1, pr.2⟩

def inB (h : Hex) : Bool :=
  decide (0 ≤ h.x) && decide (h.x < D.W) && decide (0 ≤ h.y) && decide (h.y < D.H)

def idx (h : Hex) : ℕ := h.x.toNat + D.W * h.y.toNat

/-- The label of a hex (`0` off the board). -/
def labAt (h : Hex) : ℕ := if D.inB h then (D.lab >>> (8 * D.idx h)) % 256 else 0

/-- The BFS certificate of a hex. -/
def distAt (h : Hex) : ℕ := (D.dist >>> (16 * D.idx h)) % 65536

def pHex (e : ℕ) : Hex := toHex (D.p.getD e (0, 0))
def zHex (g : ℕ) : Hex := toHex (D.z.getD g (0, 0))

/-- The docking `d_g^e`: the neighbour of `z_g` labelled `e + 1`. -/
def dHex (g e : ℕ) : Hex :=
  ((D.zHex g).nbrs.find? (fun h => D.labAt h == e + 1)).getD ⟨0, 0⟩

def hexOf (i : ℕ) : Hex := ⟨(i % D.W : ℕ), (i / D.W : ℕ)⟩

/-- The label of cell `i` read directly (the checker's fast path for impassable cells). -/
def labIdx (i : ℕ) : ℕ := (D.lab >>> (8 * i)) % 256

/-- The hexes of the board. -/
def rect : Finset Hex := ((Finset.range D.W) ×ˢ (Finset.range D.H)).image toHex

/-- The abstract board. -/
def toBoard : X3CBoard where
  width := D.W
  height := D.H
  obst := D.rect.filter (fun h => D.labAt h = 0)
  p := D.pHex
  z := D.zHex
  d := D.dHex
  R e := D.rect.filter (fun h => D.labAt h = e + 1)
  σ := D.σ

/-- The instance with members given as lists. -/
def toX3C (q : ℕ) (CL : List (List ℕ)) : X3C := ⟨q, CL.map List.toFinset⟩

def isEnemyLab (n l : ℕ) : Bool := decide (128 ≤ l) && decide (l < 128 + n)

/-- Closure, docking and certificate conditions at a region hex labelled `l`. -/
def regionOK (CL : List (List ℕ)) (h : Hex) (l : ℕ) : Bool :=
  h.nbrs.all (fun h' => D.labAt h' == 0 || D.labAt h' == l ||
      (isEnemyLab CL.length (D.labAt h') && (CL.getD (D.labAt h' - 128) []).contains (l - 1) &&
        D.dHex (D.labAt h' - 128) (l - 1) == h)) &&
    decide ((h.nbrs.filter (fun h' => isEnemyLab CL.length (D.labAt h'))).length ≤ 1) &&
    ((D.distAt h == 0 && h == D.pHex (l - 1)) ||
      h.nbrs.any (fun h' => D.labAt h' == l && D.distAt h' + 1 == D.distAt h))

/-- The local check at a hex. -/
def cellOK (q : ℕ) (CL : List (List ℕ)) (h : Hex) : Bool :=
  if D.labAt h = 0 then true
  else if D.labAt h ≤ 3 * q then D.regionOK CL h (D.labAt h)
  else isEnemyLab CL.length (D.labAt h) && h == D.zHex (D.labAt h - 128)

/-- The check at an enemy hex: its label, (I1), and the dockings. -/
def enemyOK (CL : List (List ℕ)) (g : ℕ) : Bool :=
  D.labAt (D.zHex g) == 128 + g &&
  (((D.zHex g).nbrs.filter (fun h => D.labAt h != 0)).length == 3 &&
    ((D.zHex g).nbrs.filter (fun h => D.labAt h != 0)).all (fun x =>
      ((D.zHex g).nbrs.filter (fun h => D.labAt h != 0)).all (fun y => !decide (Hex.Adj x y)))) &&
  (CL.getD g []).all (fun e => D.labAt (D.dHex g e) == e + 1 &&
    decide (Hex.Adj (D.dHex g e) (D.zHex g)))

/-- Well-formedness of the members. -/
def wfOK (q : ℕ) (CL : List (List ℕ)) : Bool :=
  CL.all (fun l => decide l.Nodup && l.length == 3 && l.all (fun e => decide (e < 3 * q)))

/-- **The board checker** (it includes `wfOK`). -/
def check (q : ℕ) (CL : List (List ℕ)) : Bool :=
  wfOK q CL && decide (3 * q < 128) && decide (D.W * D.H ≤ D.σ) &&
  (List.range (3 * q)).all (fun e => D.labAt (D.pHex e) == e + 1) &&
  (List.range CL.length).all (D.enemyOK CL) &&
  (List.range (D.W * D.H)).all (fun i => D.labIdx i == 0 || D.cellOK q CL (D.hexOf i))

/-! ## Soundness -/

variable {D}

theorem toX3C_n (q : ℕ) (CL : List (List ℕ)) : (toX3C q CL).n = CL.length := by
  simp [toX3C, X3C.n]

theorem toX3C_set {q : ℕ} {CL : List (List ℕ)} {g : ℕ} (hg : g < CL.length) :
    (toX3C q CL).set g = (CL.getD g []).toFinset := by
  simp [toX3C, X3C.set, hg]

theorem wfOK_sound {q : ℕ} {CL : List (List ℕ)} (h : wfOK q CL = true) : (toX3C q CL).WF := by
  simp only [wfOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨fun g hg => ?_, fun g hg e he => ?_⟩
  · rw [toX3C_n] at hg
    rw [toX3C_set hg]
    have hm : CL.getD g [] ∈ CL := by simp [hg]
    obtain ⟨⟨hnd, hl⟩, -⟩ := h _ hm
    rw [List.toFinset_card_of_nodup hnd, hl]
  · rw [toX3C_n] at hg
    rw [toX3C_set hg, List.mem_toFinset] at he
    have hm : CL.getD g [] ∈ CL := by simp [hg]
    exact (h _ hm).2 e he

theorem inB_iff {h : Hex} : D.inB h = true ↔ 0 ≤ h.x ∧ h.x < D.W ∧ 0 ≤ h.y ∧ h.y < D.H := by
  simp [inB, and_assoc]

theorem inB_of_labAt {h : Hex} (hl : D.labAt h ≠ 0) : D.inB h = true := by
  unfold labAt at hl; split_ifs at hl with hb
  · exact hb
  · exact absurd rfl hl

theorem mem_rect {h : Hex} : h ∈ D.rect ↔ D.inB h = true := by
  rw [inB_iff]
  simp only [rect, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists, toHex]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; simp only; omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h.x.toNat, h.y.toNat, ⟨by omega, by omega⟩, by ext <;> simp <;> omega⟩

theorem open_iff {h : Hex} : D.toBoard.Open h ↔ D.labAt h ≠ 0 := by
  simp only [X3CBoard.Open, toBoard, Finset.mem_filter, not_and]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact h5 (mem_rect.mpr (inB_iff.mpr ⟨h1, h2, h3, h4⟩))
  · intro hl
    obtain ⟨h1, h2, h3, h4⟩ := inB_iff.mp (inB_of_labAt hl)
    exact ⟨h1, h2, h3, h4, fun _ => hl⟩

theorem mem_R {e : ℕ} {h : Hex} : h ∈ D.toBoard.R e ↔ D.labAt h = e + 1 := by
  simp only [toBoard, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hl; exact ⟨mem_rect.mpr (inB_of_labAt (by omega)), hl⟩

theorem hexOf_idx {h : Hex} (hb : D.inB h = true) : D.hexOf (D.idx h) = h ∧ D.idx h < D.W * D.H := by
  obtain ⟨h1, h2, h3, h4⟩ := inB_iff.mp hb
  have hW : 0 < D.W := by omega
  refine ⟨?_, ?_⟩
  · simp only [hexOf, idx]
    ext
    · simp only
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; omega
    · simp only
      rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt (by omega)]; omega
  · simp only [idx]
    have : h.y.toNat + 1 ≤ D.H := by omega
    calc h.x.toNat + D.W * h.y.toNat < D.W + D.W * h.y.toNat := by omega
      _ = D.W * (h.y.toNat + 1) := by ring
      _ ≤ D.W * D.H := Nat.mul_le_mul_left _ this

section
variable {q : ℕ} {CL : List (List ℕ)} (hc : D.check q CL = true)
include hc

theorem check_wf : wfOK q CL = true := by
  simp only [check, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1

theorem check_parts : 3 * q < 128 ∧ D.W * D.H ≤ D.σ ∧
    (∀ e < 3 * q, D.labAt (D.pHex e) = e + 1) ∧ (∀ g < CL.length, D.enemyOK CL g = true) ∧
    ∀ i < D.W * D.H, D.labIdx i = 0 ∨ D.cellOK q CL (D.hexOf i) = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  exact ⟨h1, h2, h3, h4, h5⟩

theorem cellOK_of {h : Hex} (hl : D.labAt h ≠ 0) : D.cellOK q CL h = true := by
  have hb := inB_of_labAt hl
  obtain ⟨hh, hi⟩ := hexOf_idx hb
  rcases (check_parts hc).2.2.2.2 _ hi with h0 | h1
  · exfalso; apply hl
    unfold labAt; rw [if_pos hb]; exact h0
  · rwa [hh] at h1

theorem zlab {g : ℕ} (hg : g < CL.length) : D.labAt (D.zHex g) = 128 + g := by
  have := (check_parts hc).2.2.2.1 g hg
  simp only [enemyOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1

/-- A hex labelled as enemy `g` is `z_g`. -/
theorem eq_z {h : Hex} {g : ℕ} (hl : D.labAt h = 128 + g) :
    h = D.zHex g := by
  have h3 := (check_parts hc).1
  have hc' := cellOK_of hc (h := h) (by omega)
  simp only [cellOK, hl] at hc'
  rw [if_neg (by omega), if_neg (by omega)] at hc'
  simp only [Bool.and_eq_true, beq_iff_eq] at hc'
  have := hc'.2
  simpa using this

theorem z_iff {h : Hex} : (∃ g < CL.length, h = D.zHex g) ↔ isEnemyLab CL.length (D.labAt h) = true := by
  simp only [isEnemyLab, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨g, hg, rfl⟩; rw [zlab hc hg]; omega
  · rintro ⟨h1, h2⟩
    exact ⟨D.labAt h - 128, by omega, eq_z hc (by omega)⟩

theorem region_of {h : Hex} {e : ℕ} (he : e < 3 * q) (hl : D.labAt h = e + 1) :
    D.regionOK CL h (e + 1) = true := by
  have hc' := cellOK_of hc (h := h) (by omega)
  simp only [cellOK, hl] at hc'
  rwa [if_neg (by omega), if_pos (by omega)] at hc'

theorem region_parts {h : Hex} {e : ℕ} (he : e < 3 * q) (hl : D.labAt h = e + 1) :
    (∀ h' ∈ h.nbrs, D.labAt h' = 0 ∨ D.labAt h' = e + 1 ∨
      (isEnemyLab CL.length (D.labAt h') = true ∧ e ∈ CL.getD (D.labAt h' - 128) [] ∧
        D.dHex (D.labAt h' - 128) e = h)) ∧
    (h.nbrs.filter (fun h' => isEnemyLab CL.length (D.labAt h'))).length ≤ 1 ∧
    ((D.distAt h = 0 ∧ h = D.pHex e) ∨
      ∃ h' ∈ h.nbrs, D.labAt h' = e + 1 ∧ D.distAt h' + 1 = D.distAt h) := by
  have := region_of hc he hl
  simp only [regionOK, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem, Nat.add_sub_cancel] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨fun h' hh' => ?_, h2, h3⟩
  rcases h1 h' hh' with (h0 | h0) | ⟨⟨h4, h5⟩, h6⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr ⟨h4, h5, h6⟩)

theorem enemy_parts {g : ℕ} (hg : g < CL.length) :
    ((D.zHex g).nbrs.filter (fun h => D.labAt h != 0)).length = 3 ∧
    (∀ x ∈ (D.zHex g).nbrs.filter (fun h => D.labAt h != 0),
      ∀ y ∈ (D.zHex g).nbrs.filter (fun h => D.labAt h != 0), ¬ Hex.Adj x y) ∧
    ∀ e ∈ CL.getD g [], D.labAt (D.dHex g e) = e + 1 ∧ Hex.Adj (D.dHex g e) (D.zHex g) := by
  have := (check_parts hc).2.2.2.1 g hg
  simp only [enemyOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at this
  obtain ⟨⟨-, h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, h3⟩

end

theorem nbrs_nodup (h : Hex) : h.nbrs.Nodup := by
  rcases h with ⟨x, y⟩
  simp only [Hex.nbrs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or, Hex.mk.injEq]
  and_intros
  all_goals first | omega | simp

theorem length_ge_two {l : List Hex} {a b : Hex} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    2 ≤ l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb; exact absurd (ha.trans hb.symm) hne
  · simp

/-- **Soundness of the board checker**: a board passing `check` satisfies (I1)–(I4). -/
theorem check_sound {q : ℕ} {CL : List (List ℕ)} (hc : D.check q CL = true) :
    D.toBoard.Inv (toX3C q CL) := by
  obtain ⟨h128, hσ, hp, -, -⟩ := check_parts hc
  have hn : ∀ g, g < (toX3C q CL).n ↔ g < CL.length := fun g => by rw [toX3C_n]
  have hq : (toX3C q CL).q = q := rfl
  have hset : ∀ g < CL.length, ∀ e, e ∈ (toX3C q CL).set g ↔ e ∈ CL.getD g [] := by
    intro g hg e; rw [toX3C_set hg, List.mem_toFinset]
  have hzl := fun g (hg : g < CL.length) => zlab hc hg
  have hfn : ∀ g, D.toBoard.freeNbrs (D.zHex g) =
      ((D.zHex g).nbrs.filter (fun h => D.labAt h != 0)).toFinset := by
    intro g
    simp only [X3CBoard.freeNbrs]
    congr 1
    apply List.filter_congr
    intro x _
    simp only [open_iff]
    cases h : D.labAt x <;> simp
  -- a region hex is not an enemy hex
  have hnotz : ∀ e < 3 * q, ∀ h, D.labAt h = e + 1 → ∀ g < CL.length, h ≠ D.zHex g := by
    intro e he h hl g hg heq; rw [heq, hzl g hg] at hl; omega
  refine
    { zOpen := ?_, zInj := ?_, i1card := ?_, i1nonadj := ?_, rOpen := ?_, rCover := ?_,
      rDisj := ?_, rClosed := ?_, rConn := ?_, pMem := ?_, dMem := ?_, dAdj := ?_,
      dAlone := ?_, rDock := ?_, i4 := ?_ }
  · intro g hg; rw [hn] at hg; rw [open_iff]; show D.labAt (D.zHex g) ≠ 0; rw [hzl g hg]; omega
  · intro g hg g' hg' h; rw [hn] at hg hg'
    have := congrArg D.labAt h
    simp only [toBoard] at this
    rw [hzl g hg, hzl g' hg'] at this; omega
  · intro g hg; rw [hn] at hg
    simp only [toBoard] at *
    rw [hfn, List.toFinset_card_of_nodup ((nbrs_nodup _).filter _)]
    exact (enemy_parts hc hg).1
  · intro g hg x hx y hy; rw [hn] at hg
    simp only [toBoard] at *
    rw [hfn, List.mem_toFinset] at hx hy
    exact (enemy_parts hc hg).2.1 x hx y hy
  · intro e he h hh; rw [hq] at he
    rw [mem_R] at hh
    refine ⟨open_iff.mpr (by omega), fun g hg => ?_⟩
    rw [hn] at hg; exact hnotz e he h hh g hg
  · intro h ho hz
    rw [open_iff] at ho
    have hc' := cellOK_of hc ho
    simp only [cellOK, if_neg ho] at hc'
    split_ifs at hc' with hle
    · exact ⟨D.labAt h - 1, by rw [hq]; omega, mem_R.mpr (by omega)⟩
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      exfalso
      obtain ⟨g, hg, heq⟩ := (z_iff hc).mpr hc'.1
      exact hz g ((hn g).mpr hg) heq
  · intro e _ e' _ hne
    rw [Finset.disjoint_left]
    intro h h1 h2; rw [mem_R] at h1 h2; omega
  · intro e he h hh h' hadj ho hz
    rw [hq] at he
    rw [mem_R] at hh ⊢
    rw [open_iff] at ho
    rcases (region_parts hc he hh).1 h' hadj with h0 | h0 | ⟨hen, -, -⟩
    · exact absurd h0 ho
    · exact h0
    · obtain ⟨g, hg, heq⟩ := (z_iff hc).mpr hen
      exact absurd heq (hz g ((hn g).mpr hg))
  · intro e he h hh
    rw [hq] at he
    rw [mem_R] at hh
    simp only [toBoard]
    -- induction on the certificate
    suffices ∀ n, ∀ h, D.labAt h = e + 1 → D.distAt h = n →
        Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ D.toBoard.R e) (D.pHex e) h from
      this _ h hh rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h hl hd
      rcases (region_parts hc he hl).2.2 with ⟨h0, rfl⟩ | ⟨h', hh', hl', hd'⟩
      · exact .refl
      · have := ih (D.distAt h') (by omega) h' hl' rfl
        exact this.tail ⟨Hex.adj_symm hh', mem_R.mpr hl⟩
  · intro e he; rw [hq] at he; rw [mem_R]; exact hp e he
  · intro g hg e he
    rw [hn] at hg; rw [hset g hg] at he
    rw [mem_R]; exact ((enemy_parts hc hg).2.2 e he).1
  · intro g hg e he
    rw [hn] at hg; rw [hset g hg] at he
    exact ((enemy_parts hc hg).2.2 e he).2
  · intro g hg e he g' hg' hadj
    rw [hn] at hg hg'; rw [hset g hg] at he
    simp only [toBoard] at hadj ⊢
    have hl := ((enemy_parts hc hg).2.2 e he).1
    have hadj0 := ((enemy_parts hc hg).2.2 e he).2
    by_contra hne
    have heS : e < 3 * q :=
      (wfOK_sound (check_wf hc)).sub g ((hn g).mpr hg) e ((hset g hg e).mpr he)
    have h2 := (region_parts hc heS hl).2.1
    have hm1 : D.zHex g ∈ (D.dHex g e).nbrs.filter (fun h' => isEnemyLab CL.length (D.labAt h')) := by
      rw [List.mem_filter]
      exact ⟨hadj0, (z_iff hc).mp ⟨g, hg, rfl⟩⟩
    have hm2 : D.zHex g' ∈ (D.dHex g e).nbrs.filter (fun h' => isEnemyLab CL.length (D.labAt h')) := by
      rw [List.mem_filter]
      exact ⟨hadj, (z_iff hc).mp ⟨g', hg', rfl⟩⟩
    have hz' : D.zHex g ≠ D.zHex g' := by
      intro h; have := congrArg D.labAt h; rw [hzl g hg, hzl g' hg'] at this; omega
    have := length_ge_two hm1 hm2 hz'
    omega
  · intro e he h hh g hg hadj
    rw [hq] at he; rw [hn] at hg; rw [mem_R] at hh
    simp only [toBoard] at hadj ⊢
    rcases (region_parts hc he hh).1 _ hadj with h0 | h0 | ⟨-, hmem, hd⟩
    · rw [hzl g hg] at h0; omega
    · rw [hzl g hg] at h0; omega
    · rw [hzl g hg, show 128 + g - 128 = g by omega] at hmem hd
      exact ⟨(hset g hg e).mpr hmem, hd.symm⟩
  · intro e he
    simp only [toBoard]
    calc (D.rect.filter (fun h => D.labAt h = e + 1)).card ≤ D.rect.card :=
          Finset.card_filter_le _ _
      _ ≤ ((Finset.range D.W) ×ˢ (Finset.range D.H)).card := Finset.card_image_le
      _ = D.W * D.H := by simp
      _ ≤ D.σ := hσ

end BoardData

/-! ## The fixed yes-board `D1` -/

namespace BoardData

/-- `X = {0, 1, 2}`, `C = {{0, 1, 2}}`: the enemy gadget alone on a `5 × 5` board.  `z = (2, 2)`
(even row); the dockings `U = (2, 1)`, `R = (3, 2)`, `D = (2, 3)` are the alternating triple and
each is its own one-hex region and deployment hex. -/
def D1 : BoardData where
  W := 5
  H := 5
  lab := 1 * 2 ^ (8 * 7) + 128 * 2 ^ (8 * 12) + 2 * 2 ^ (8 * 13) + 3 * 2 ^ (8 * 17)
  dist := 0
  p := [(2, 1), (3, 2), (2, 3)]
  z := [(2, 2)]
  σ := 25

def CL1 : List (List ℕ) := [[0, 1, 2]]

theorem D1_check : D1.check 1 CL1 = true := by decide +kernel

theorem D1_inv : D1.toBoard.Inv (toX3C 1 CL1) := check_sound D1_check

theorem P1_wf : (toX3C 1 CL1).WF := wfOK_sound (check_wf D1_check)

theorem P1_cover : (toX3C 1 CL1).ExactCover := by
  refine ⟨{0}, fun g hg => by simp at hg; simp [hg, toX3C_n, CL1], by simp, fun e he => ⟨0, by simp, ?_⟩⟩
  rw [toX3C_set (by simp [CL1])]
  simp only [CL1, List.getD_cons_zero, List.mem_toFinset, List.mem_cons, List.not_mem_nil]
  simp [toX3C] at he
  omega

end BoardData

open BoardData T3

/-! ## Total forms -/

/-- **The total reduction of Theorem 3** on encodings `(q, C, board data)`: a board passing the
checker (which includes well-formedness of `C`) gives `G_3` at the paper's constants; `q = 0` is
rerouted to the fixed yes-instance `G_3(D1)` (so that `W > 0`); anything else is `G_no`. -/
def reduction3 (q : ℕ) (CL : List (List ℕ)) (D : BoardData) : Instance :=
  if D.check q CL then
    (if q = 0 then G3pub (toX3C 1 CL1) D1.toBoard else G3pub (toX3C q CL) D.toBoard)
  else Corridor.Gno

/-- The source problem of the total form: a certified board and an exact cover. -/
def X3CB (q : ℕ) (CL : List (List ℕ)) (D : BoardData) : Prop :=
  D.check q CL = true ∧ (toX3C q CL).ExactCover

/-- **Theorem 3, total form (modulo the embedding).** -/
theorem theorem3_total (q : ℕ) (CL : List (List ℕ)) (D : BoardData) :
    X3CB q CL D ↔ ArmyAllocation (reduction3 q CL D) := by
  unfold reduction3 X3CB
  by_cases hc : D.check q CL = true
  · rw [if_pos hc]
    split_ifs with hq
    · exact ⟨fun _ => (theorem3_pub _ _ P1_wf D1_inv).mp P1_cover,
        fun _ => ⟨hc, X3C.exactCover_of_q_zero hq⟩⟩
    · rw [← theorem3_pub _ _ (wfOK_sound (check_wf hc)) (check_sound hc)]
      exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h.1 hc, fun h => absurd h Corridor.Gno_no⟩

/-- The total reduction of Corollary 3.1: an instance with its given (all-ones) allocation. -/
def reduction31 (q : ℕ) (CL : List (List ℕ)) (D : BoardData) : Instance × (ℕ → SlotAlloc) :=
  if D.check q CL then
    (if q = 0 then (G3pub (toX3C 1 CL1) D1.toBoard, α1) else (G3pub (toX3C q CL) D.toBoard, α1))
  else (Corridor.Gno, αGno)

/-- **Corollary 3.1, total form (modulo the embedding).** -/
theorem cor31_total (q : ℕ) (CL : List (List ℕ)) (D : BoardData) :
    X3CB q CL D ↔ ThmF.BattlePlay (reduction31 q CL D).1 (reduction31 q CL D).2 := by
  unfold reduction31 X3CB
  by_cases hc : D.check q CL = true
  · rw [if_pos hc]
    split_ifs with hq
    · exact ⟨fun _ => (cor31 _ _ P1_wf D1_inv (by norm_num) (by norm_num)).mp P1_cover,
        fun _ => ⟨hc, X3C.exactCover_of_q_zero hq⟩⟩
    · rw [← cor31 _ _ (wfOK_sound (check_wf hc)) (check_sound hc) (by norm_num) (by norm_num)]
      exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  · rw [if_neg hc]
    refine ⟨fun h => absurd h.1 hc, fun ⟨s, hs, hdn, hW⟩ => absurd ?_ Corridor.Gno_no⟩
    exact ⟨αGno, αGno_feasible, s, hs, hdn, hW⟩

/-! ## Deciding exact cover (for concrete instances) -/

namespace BoardData

/-- Members `L` (indices) pairwise disjoint and covering `[0, 3q)`. -/
def coverOK (q : ℕ) (CL : List (List ℕ)) (L : List ℕ) : Bool :=
  L.all (fun g => L.all (fun g' => g == g' ||
    (CL.getD g []).all (fun e => !(CL.getD g' []).contains e))) &&
  (List.range (3 * q)).all (fun e => L.any (fun g => (CL.getD g []).contains e))

/-- Some sublist of the member indices is an exact cover. -/
def coverCheck (q : ℕ) (CL : List (List ℕ)) : Bool :=
  (List.range CL.length).sublists.any (coverOK q CL)

/-- **`coverCheck` decides exact cover.** -/
theorem exactCover_iff_check {q : ℕ} {CL : List (List ℕ)} :
    (toX3C q CL).ExactCover ↔ coverCheck q CL = true := by
  simp only [coverCheck, List.any_eq_true, List.mem_sublists, coverOK, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.any_eq_true, List.contains_iff_mem, List.mem_range]
  constructor
  · rintro ⟨K, hK, hdis, hcov⟩
    refine ⟨(List.range CL.length).filter (fun g => g ∈ K), List.filter_sublist, ⟨?_, ?_⟩⟩
    · intro g hg g' hg'
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hg hg'
      by_cases he : g = g'
      · exact Or.inl he
      · right
        intro e he1
        have hd := hdis g hg.2 g' hg'.2 he
        rw [toX3C_set hg.1, toX3C_set hg'.1] at hd
        rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
        intro he2
        exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr he1) (List.mem_toFinset.mpr he2)
    · intro e he
      obtain ⟨g, hg, heg⟩ := hcov e he
      have hgn := hK g hg
      rw [toX3C_n] at hgn
      rw [toX3C_set hgn, List.mem_toFinset] at heg
      exact ⟨g, by simp [hgn, hg], heg⟩
  · rintro ⟨L, hL, hdis, hcov⟩
    have hLn : ∀ g ∈ L, g < CL.length := fun g hg => List.mem_range.mp (hL.subset hg)
    refine ⟨L.toFinset, fun g hg => ?_, fun g hg g' hg' hne => ?_, fun e he => ?_⟩
    · rw [toX3C_n]; exact hLn g (List.mem_toFinset.mp hg)
    · rw [List.mem_toFinset] at hg hg'
      rw [toX3C_set (hLn g hg), toX3C_set (hLn g' hg'), Finset.disjoint_left]
      intro e he1 he2
      rcases hdis g hg g' hg' with h | h
      · exact hne h
      · have := h e (List.mem_toFinset.mp he1)
        rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at this
        exact this (List.mem_toFinset.mp he2)
    · obtain ⟨g, hg, heg⟩ := hcov e he
      exact ⟨g, List.mem_toFinset.mpr hg, by rw [toX3C_set (hLn g hg), List.mem_toFinset]; exact heg⟩

end BoardData

/-! ## Sparse boards and verdict packaging (for the cross-checks) -/

namespace BoardData

/-- Sum of `sel r` over the `k` 44-bit records `r` packed in `c` (lowest first), split in halves
so that the kernel's recursion depth is `log k`; `f` is fuel (`32` suffices for `k < 2^32`). -/
def unpack (sel : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, k, c =>
    if k == 0 then 0 else if k == 1 then sel (c % 2 ^ 44) else
      unpack sel f (k / 2) (c % 2 ^ (44 * (k / 2))) + unpack sel f (k - k / 2) (c >>> (44 * (k / 2)))

/-- A record `i·2^24 + label·2^16 + dist` places `label` at byte `i` of `lab` ... -/
def selLab (r : ℕ) : ℕ := (r / 2 ^ 16 % 256) <<< (8 * (r / 2 ^ 24))

/-- ... and `dist` at 16-bit field `i` of `dist`. -/
def selDist (r : ℕ) : ℕ := (r % 2 ^ 16) <<< (16 * (r / 2 ^ 24))

/-- A board from its `k` free cells, packed as 44-bit records `i·2^24 + label·2^16 + dist`
(`i = x + W·y`): the kernel assembles `lab` and `dist` (the boards of Lemma D.4 are mostly
impassable, so this is much shorter than the dense literals).  Nothing is trusted: `check`
reads the assembled numbers as before. -/
def ofPacked (W H k cells : ℕ) (p z : List (ℕ × ℕ)) (σ : ℕ) : BoardData where
  W := W
  H := H
  lab := unpack selLab 32 k cells
  dist := unpack selDist 32 k cells
  p := p
  z := z
  σ := σ

open T3

/-- Verdicts on a yes-board: (I1)–(I4), an exact cover, the game is yes at the historical
(`hp 5`, `def 41`) and the published (`hp 4`, `def 27`) constants, Corollary 3.1, and every
winning allocation is all-ones. -/
def YesV (D : BoardData) (q : ℕ) (CL : List (List ℕ)) : Prop :=
  D.toBoard.Inv (toX3C q CL) ∧ (toX3C q CL).ExactCover ∧
  ArmyAllocation (G3 5 41 (toX3C q CL) D.toBoard) ∧ ArmyAllocation (G3pub (toX3C q CL) D.toBoard) ∧
  ThmF.BattlePlay (G3 5 41 (toX3C q CL) D.toBoard) α1 ∧
  ∀ α, Feasible (G3 5 41 (toX3C q CL) D.toBoard) α → ∀ s, Reach (G3 5 41 (toX3C q CL) D.toBoard) α s →
    q ≤ destroyed (G3 5 41 (toX3C q CL) D.toBoard) s → ∀ j < 3 * q, (α j).count = 1

/-- Verdicts on a no-board. -/
def NoV (D : BoardData) (q : ℕ) (CL : List (List ℕ)) : Prop :=
  D.toBoard.Inv (toX3C q CL) ∧ ¬ (toX3C q CL).ExactCover ∧
  ¬ ArmyAllocation (G3 5 41 (toX3C q CL) D.toBoard) ∧
  ¬ ArmyAllocation (G3pub (toX3C q CL) D.toBoard) ∧
  ¬ ThmF.BattlePlay (G3 5 41 (toX3C q CL) D.toBoard) α1

theorem yes_of {D : BoardData} {q : ℕ} {CL : List (List ℕ)} (hc : D.check q CL = true)
    (hv : coverCheck q CL = true) : YesV D q CL := by
  have hI := check_sound hc
  have hP := wfOK_sound (check_wf hc)
  have hX := exactCover_iff_check.mpr hv
  exact ⟨hI, hX, (theorem3 _ _ hP hI (by norm_num) (by norm_num)).mp hX,
    (theorem3_pub _ _ hP hI).mp hX, (cor31 _ _ hP hI (by norm_num) (by norm_num)).mp hX,
    fun α hα s hs hW => winning_unique (P := toX3C q CL) (by norm_num) (by norm_num) hα hs hW⟩

theorem no_of {D : BoardData} {q : ℕ} {CL : List (List ℕ)} (hc : D.check q CL = true)
    (hv : coverCheck q CL = false) : NoV D q CL := by
  have hI := check_sound hc
  have hP := wfOK_sound (check_wf hc)
  have hX : ¬ (toX3C q CL).ExactCover := fun h => by
    have := exactCover_iff_check.mp h; rw [hv] at this; exact absurd this (by decide)
  exact ⟨hI, hX, fun h => hX ((theorem3 _ _ hP hI (by norm_num) (by norm_num)).mpr h),
    fun h => hX ((theorem3_pub _ _ hP hI).mpr h),
    fun h => hX ((cor31 _ _ hP hI (by norm_num) (by norm_num)).mpr h)⟩

end BoardData

end Homm3
