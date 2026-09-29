import Homm3.Embed

/-!
# Session 5, target 1. A kernel checker for drawings, and the total form with the drawing

* `OrthoDrawing.check q CL` — a Bool checker of `Valid (toX3C q CL)`, field by field;
  **`check_sound`**: `Dr.check q CL = true → Dr.Valid (toX3C q CL)`.  So `decide +kernel` on the
  checker certifies a concrete drawing (the corpus drawings, `CrossCheckDrawing*.lean`).
* **`theorem3_drawing_total`**: the total reduction on encodings `(q, C, drawing)` — a drawing
  passing the checker gives `G_3` on `build`, `q = 0` the fixed yes-instance, everything else
  `G_no`.  Its source problem is "`X3C` with a valid drawing of `G'`", which is what steps 0–3 of
  Lemma D.4 (planarity, degree reduction, packing, Tamassia–Tollis) produce from a planar instance.
-/

namespace Homm3

namespace Embed

open BoardData

namespace OrthoDrawing

variable (Dr : OrthoDrawing)

def inBoxB (a : GP) : Bool :=
  decide (0 ≤ a.1) && decide (a.1 < Dr.gw) && decide (0 ≤ a.2) && decide (a.2 < Dr.gh)

def kindB (q : ℕ) (CL : List (List ℕ)) (v : ℕ) : Bool :=
  match Dr.K v with
  | .set g => decide (g < CL.length)
  | .elem e _ => decide (e < 3 * q)

def pathB (v : ℕ) : Bool :=
  match Dr.K v with
  | .elem e (i + 1) => Dr.edges.any (fun ε => ε.v == v && Dr.K ε.u == .elem e i)
  | _ => true

def tgtB (CL : List (List ℕ)) (ε : DEdge) : Bool :=
  (!Dr.isSet ε.v && Dr.elemOf ε.v == Dr.elemOf ε.u) ||
  (match Dr.K ε.v with
   | .set g => (CL.getD g []).contains (Dr.elemOf ε.u)
   | .elem _ _ => false)

def edgeB (CL : List (List ℕ)) (ε : DEdge) : Bool :=
  decide (ε.u < Dr.nV) && decide (ε.v < Dr.nV) && !Dr.isSet ε.u && Dr.tgtB CL ε &&
  decide (2 ≤ ε.r.length) && (List.range ε.k).all (fun j => decide (IsUnit (ε.sd j))) &&
  decide ε.r.Nodup && ε.rp 0 == Dr.loc ε.u && ε.rp ε.k == Dr.loc ε.v && ε.r.all Dr.inBoxB &&
  (List.range Dr.nV).all (fun w => !ε.r.contains (Dr.loc w) || w == ε.u || w == ε.v)

def pairB (ε ε' : DEdge) : Bool :=
  ε == ε' ||
  ((!(ε.v == ε'.v && Dr.isSet ε.v && Dr.elemOf ε.u == Dr.elemOf ε'.u)) &&
   [ε.u, ε.v].all (fun w => !(ε.dirAt w == ε'.dirAt w && (ε.dirAt w).isSome)) &&
   ε.r.all (fun x => !ε'.r.contains x || (List.range Dr.nV).any (fun w =>
     x == Dr.loc w && (w == ε.u || w == ε.v) && (w == ε'.u || w == ε'.v))))

/-- **The drawing checker.** -/
def check (q : ℕ) (CL : List (List ℕ)) : Bool :=
  wfOK q CL && Dr.pos.length == Dr.nV && decide Dr.kind.Nodup &&
  (List.range Dr.nV).all (Dr.kindB q CL) &&
  (List.range CL.length).all (fun g => Dr.kind.contains (.set g)) &&
  (List.range (3 * q)).all (fun e => Dr.kind.contains (.elem e 0)) &&
  (List.range Dr.nV).all Dr.pathB &&
  Dr.edges.all (Dr.edgeB CL) &&
  (List.range CL.length).all (fun g => (CL.getD g []).all (fun e =>
    Dr.edges.any (fun ε => ε.v == Dr.setV g && Dr.elemOf ε.u == e))) &&
  decide Dr.pos.Nodup && Dr.pos.all Dr.inBoxB &&
  Dr.edges.all (fun ε => Dr.edges.all (Dr.pairB ε))

variable {Dr}

theorem inBoxB_iff {a : GP} : Dr.inBoxB a = true ↔ 0 ≤ a.1 ∧ a.1 < Dr.gw ∧ 0 ≤ a.2 ∧ a.2 < Dr.gh := by
  simp [inBoxB, and_assoc]

theorem K_lt_of_ne {v : ℕ} (hv : ¬ v < Dr.nV) : Dr.K v = .set 0 := by
  unfold K; rw [List.getD_eq_default]; unfold nV at hv; omega

/-- **Soundness of the drawing checker.** -/
theorem check_sound {q : ℕ} {CL : List (List ℕ)} (hc : Dr.check q CL = true) :
    Dr.Valid (toX3C q CL) := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, List.contains_iff_mem] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwf, hlen⟩, hnd⟩, hkind⟩, hset⟩, hroot⟩, hpath⟩, hedge⟩, hcov⟩, hpnd⟩, hpbox⟩,
    hpair⟩ := hc
  have hn : (toX3C q CL).n = CL.length := toX3C_n q CL
  have hmem : ∀ g < CL.length, ∀ e, e ∈ (toX3C q CL).set g ↔ e ∈ CL.getD g [] := by
    intro g hg e; rw [toX3C_set hg, List.mem_toFinset]
  -- the edge conditions, unpacked
  have hE : ∀ ε ∈ Dr.edges, ε.u < Dr.nV ∧ ε.v < Dr.nV ∧ Dr.isSet ε.u = false ∧ Dr.tgtB CL ε = true ∧
      2 ≤ ε.r.length ∧ (∀ j < ε.k, IsUnit (ε.sd j)) ∧ ε.r.Nodup ∧ ε.rp 0 = Dr.loc ε.u ∧
      ε.rp ε.k = Dr.loc ε.v ∧ (∀ a ∈ ε.r, Dr.inBoxB a = true) ∧
      ∀ w < Dr.nV, Dr.loc w ∈ ε.r → w = ε.u ∨ w = ε.v := by
    intro ε hε
    have := hedge ε hε
    simp only [edgeB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
      List.all_eq_true, List.mem_range, Bool.or_eq_true] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := this
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun w hw hx => ?_⟩
    rcases h11 w hw with (h | h) | h
    · simp at h; exact absurd hx (by simpa using h)
    · exact Or.inl h
    · exact Or.inr h
  -- the pair conditions, unpacked
  have hP : ∀ ε ∈ Dr.edges, ∀ ε' ∈ Dr.edges, ε ≠ ε' →
      ¬ (ε.v = ε'.v ∧ Dr.isSet ε.v = true ∧ Dr.elemOf ε.u = Dr.elemOf ε'.u) ∧
      (∀ w ∈ [ε.u, ε.v], ¬ (ε.dirAt w = ε'.dirAt w ∧ (ε.dirAt w).isSome = true)) ∧
      ∀ x ∈ ε.r, x ∈ ε'.r → ∃ w < Dr.nV, x = Dr.loc w ∧ (w = ε.u ∨ w = ε.v) ∧
        (w = ε'.u ∨ w = ε'.v) := by
    intro ε hε ε' hε' hne
    have := hpair ε hε ε' hε'
    simp only [pairB, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true, List.any_eq_true, List.mem_range] at this
    rcases this with h | ⟨⟨h1, h2⟩, h3⟩
    · exact absurd h hne
    · refine ⟨?_, ?_, ?_⟩
      · rintro ⟨a, b, c⟩
        rw [a, c] at h1; rw [a] at b; simp [b] at h1
      · intro w hw ⟨a, b⟩
        have := h2 w hw
        rw [a] at this b; simp [b] at this
      · intro x hx hx'
        rcases h3 x hx with h | ⟨w, hw, ⟨⟨hxw, hwe⟩, hwe'⟩⟩
        · simp at h; exact absurd hx' (by simpa using h)
        · refine ⟨w, hw, hxw, ?_, ?_⟩
          · simpa [Bool.or_eq_true, beq_iff_eq] using hwe
          · simpa [Bool.or_eq_true, beq_iff_eq] using hwe'
  refine
    { wf := wfOK_sound hwf, len := hlen, kindNodup := hnd, kindSet := ?_, kindElem := ?_,
      setEx := ?_, rootEx := ?_, pathEx := ?_, eEnds := fun ε hε => ⟨(hE ε hε).1, (hE ε hε).2.1⟩,
      eSrc := fun ε hε => (hE ε hε).2.2.1, eTgt := ?_, setDist := ?_, setCov := ?_,
      posNodup := hpnd, posBox := fun a ha => inBoxB_iff.mp (hpbox a ha),
      route := fun ε hε => ⟨(hE ε hε).2.2.2.2.1, (hE ε hε).2.2.2.2.2.1, (hE ε hε).2.2.2.2.2.2.1⟩,
      rHead := fun ε hε => (hE ε hε).2.2.2.2.2.2.2.1,
      rLast := fun ε hε => (hE ε hε).2.2.2.2.2.2.2.2.1,
      rBox := fun ε hε a ha => inBoxB_iff.mp ((hE ε hε).2.2.2.2.2.2.2.2.2.1 a ha),
      ports := ?_, noThrough := fun ε hε => (hE ε hε).2.2.2.2.2.2.2.2.2.2, noCross := ?_ }
  · intro v hv g hg
    have := hkind v hv
    rw [kindB, hg] at this; rw [hn]; simpa using this
  · intro v hv e i he
    have := hkind v hv
    rw [kindB, he] at this; show e < 3 * q; simpa using this
  · intro g hg; rw [hn] at hg; exact hset g hg
  · intro e he; exact hroot e he
  · intro v hv e i hK
    have := hpath v hv
    rw [pathB, hK] at this
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · intro ε hε
    have := (hE ε hε).2.2.2.1
    unfold tgtB at this
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this with h | h
    · exact Or.inl h
    · right
      cases hK : Dr.K ε.v with
      | elem _ _ => rw [hK] at h; simp at h
      | set g =>
        rw [hK] at h
        simp only [List.contains_iff_mem] at h
        have hg : g < CL.length := by
          by_contra hlt
          rw [List.getD_eq_default _ _ (by omega)] at h; simp at h
        exact ⟨g, rfl, (hmem g hg _).mpr h⟩
  · intro ε hε ε' hε' hv hs he
    by_contra hne
    exact (hP ε hε ε' hε' hne).1 ⟨hv, hs, he⟩
  · intro g hg e he
    rw [hn] at hg
    have := hcov g hg e ((hmem g hg e).mp he)
    simpa [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] using this
  · intro ε hε ε' hε' w d hd hd'
    by_contra hne
    have hw : w ∈ [ε.u, ε.v] := by
      rcases dirAt_some hd with ⟨rfl, -⟩ | ⟨rfl, -, -⟩ <;> simp
    exact (hP ε hε ε' hε' hne).2.1 w hw ⟨by rw [hd, hd'], by rw [hd]; rfl⟩
  · intro ε hε ε' hε' hne x hx hx'
    exact (hP ε hε ε' hε' hne).2.2 x hx hx'

end OrthoDrawing

open OrthoDrawing T3

/-! ## The total form -/

/-- **The total reduction with the drawing on the input**: encodings `(q, C, drawing)`. -/
def reductionD (q : ℕ) (CL : List (List ℕ)) (Dr : OrthoDrawing) : Instance :=
  if Dr.check q CL then
    (if q = 0 then G3pub (toX3C 1 CL1) D1.toBoard else G3pub (toX3C q CL) (build (toX3C q CL) Dr))
  else Corridor.Gno

/-- The source problem: an `X3C` instance with a valid drawing of `G'`, and an exact cover. -/
def X3CD (q : ℕ) (CL : List (List ℕ)) (Dr : OrthoDrawing) : Prop :=
  Dr.check q CL = true ∧ (toX3C q CL).ExactCover

/-- **Theorem 3, total form, with the drawing on the input** (no embedding hypothesis left:
(I1)–(I4) come from `lemmaD4`). -/
theorem theorem3_drawing_total (q : ℕ) (CL : List (List ℕ)) (Dr : OrthoDrawing) :
    X3CD q CL Dr ↔ ArmyAllocation (reductionD q CL Dr) := by
  unfold reductionD X3CD
  by_cases hc : Dr.check q CL = true
  · rw [if_pos hc]
    split_ifs with hq
    · exact ⟨fun _ => (theorem3_pub _ _ P1_wf D1_inv).mp P1_cover,
        fun _ => ⟨hc, X3C.exactCover_of_q_zero hq⟩⟩
    · rw [← theorem3_drawing (check_sound hc)]
      exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h.1 hc, fun h => absurd h Corridor.Gno_no⟩

/-! ## The board as data (for the cross-check with `build_board_lemma`) -/

/-- A hex as a pair of naturals (board hexes have non-negative coordinates). -/
def hexNat (h : Hex) : ℕ × ℕ := (h.x.toNat, h.y.toNat)

/-- The label number of the built board, in the format of `BoardData.lab`: byte `x + W·y` is
`e + 1` on the hexes of `R_e`, `128 + g` on `z_g`, `0` elsewhere (bitwise or over the features;
a hex claimed twice with different labels would corrupt the number, so equality with the Python
number also certifies that no hex is claimed by two owners). -/
def labNum (q : ℕ) (CL : List (List ℕ)) (Dr : OrthoDrawing) : ℕ :=
  ((List.range (3 * q)).flatMap (fun e => (Dr.region e).map
      (fun h => (e + 1) <<< (8 * ((hexNat h).1 + Dr.width * (hexNat h).2)))) ++
    (List.range CL.length).map (fun g =>
      (128 + g) <<< (8 * ((hexNat (Dr.zHex g)).1 + Dr.width * (hexNat (Dr.zHex g)).2)))).foldl
    (· ||| ·) 0

/-- **The Lean board equals a given board as data**: dimensions, the label of every hex, the
deployment hexes, the enemy hexes, and the dockings `(g, e, x, y)` in the order of `C`. -/
def SameBoard (Dr : OrthoDrawing) (q : ℕ) (CL : List (List ℕ)) (D : BoardData)
    (K : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  Dr.width = D.W ∧ Dr.height = D.H ∧ labNum q CL Dr = D.lab ∧
  (List.range (3 * q)).map (fun e => hexNat (Dr.pHex e)) = D.p ∧
  (List.range CL.length).map (fun g => hexNat (Dr.zHex g)) = D.z ∧
  (List.range CL.length).flatMap
    (fun g => (CL.getD g []).map (fun e => (g, e, hexNat (Dr.dHex g e)))) = K

instance (Dr : OrthoDrawing) (q : ℕ) (CL : List (List ℕ)) (D : BoardData)
    (K : List (ℕ × ℕ × ℕ × ℕ)) : Decidable (SameBoard Dr q CL D K) := by
  unfold SameBoard; infer_instance

end Embed

end Homm3
