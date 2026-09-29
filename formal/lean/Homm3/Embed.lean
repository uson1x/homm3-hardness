import Homm3.EmbedGeom
import Homm3.BoardCheck

/-!
# Session 5. Lemma D.4 with the drawing on the input: the construction of steps 4–6

Paper: Appendix D.4 (`main.md:1408–1594`), D.6 (`main.md:1733–1765`).

**Design.**  The orthogonal drawing of `G'` is part of the input.  Planarity testing, the
rotation-preserving degree reduction (step 1), the packing of components (step 2) and the drawing
theorem of Tamassia–Tollis (step 3) stay citations, as the NP-hardness of the source problem does;
what is formalized is steps 4–6 for **every** valid drawing.

* `OrthoDrawing`: the vertices of `G'` with their kinds (`set g` for `S_g ∈ C`, `elem e i` for the
  path vertex `v_e^{i+1}`), their grid points, the edges `u → v` (source an element-path vertex) with
  their routes as unit-step grid paths, and the grid bounding box `gw × gh`.
* `OrthoDrawing.Valid P`: the drawing properties (D1)–(D3) of step 3 (`main.md:1445–1460`), the
  bounding box, and the facts about `G'` that step 1 guarantees and steps 4–6 use.
* `build P Dr : X3CBoard` — steps 4–6 literally: the scaling `φ` (`λ = 20`, `ω = 6`), corridors
  truncated at the boxes, the Lemma D.3 adapter in every set box (arms assigned by port), a "plus"
  in every element box, the deployment stub at `v_e^1`, and every other hex impassable; `σ` is the
  hex count.
* **`lemmaD4`**: `Dr.Valid P → (build P Dr).Inv P` — all of (I1)–(I4).
-/

namespace Homm3

namespace Embed

open Gadgets

/-! ## The drawing -/

/-- Vertex kinds of `G'`: the set vertex of member `g`, or the path vertex `v_e^{i+1}` of
element `e` (step 1). -/
inductive VK where
  | set (g : ℕ)
  | elem (e i : ℕ)
deriving DecidableEq, Repr

/-- **An orthogonal grid drawing of `G'`** (step 3's output, with step 1's labels): vertex kinds,
vertex grid points, edges with their routes, and the grid bounding box `[0, gw) × [0, gh)`. -/
structure OrthoDrawing where
  gw : ℕ
  gh : ℕ
  kind : List VK
  pos : List GP
  edges : List DEdge
deriving Repr

namespace DEdge

/-- The direction in which the route leaves the vertex `w` (if `w` is an end). -/
def dirAt (ε : DEdge) (w : ℕ) : Option GP :=
  if ε.u = w then some ε.du else if ε.v = w then some ε.dv else none

end DEdge

/-- The board hex of the local cell `l` of the `9 × 9` box around the grid point `c`: the local
frame translated by `(20 c.1 + 2, 20 c.2 + 2)`, an even row shift (step 5's parity argument). -/
def boxHex (c : GP) (l : ℕ × ℕ) : Hex := shift (20 * c.1 + 2) (10 * c.2 + 1) (cell l)

namespace OrthoDrawing

variable (Dr : OrthoDrawing)

def nV : ℕ := Dr.kind.length
/-- The kind of vertex `v`. -/
def K (v : ℕ) : VK := Dr.kind.getD v (.set 0)
/-- The grid point of vertex `v`. -/
def loc (v : ℕ) : GP := Dr.pos.getD v (0, 0)
def isSet (v : ℕ) : Bool := match Dr.K v with
  | .set _ => true
  | .elem _ _ => false
/-- The element of an element-path vertex. -/
def elemOf (v : ℕ) : ℕ := match Dr.K v with
  | .elem e _ => e
  | .set _ => 0
/-- The set vertex of member `g`. -/
def setV (g : ℕ) : ℕ := Dr.kind.idxOf (.set g)
/-- The first path vertex `v_e^1` of element `e`. -/
def root (e : ℕ) : ℕ := Dr.kind.idxOf (.elem e 0)

/-- The directions used at `w` by its incident routes. -/
def usedDirs (w : ℕ) : List GP := Dr.edges.filterMap (·.dirAt w)

/-- The **plus** of an element vertex (step 5): the centre and the axis runs of length `ρ = 4`
towards the used ports. -/
def plus (w : ℕ) : List Hex :=
  φ (Dr.loc w) :: (Dr.usedDirs w).flatMap
    (fun d => (List.range 5).map (fun t : ℕ => mv (φ (Dr.loc w)) (t : ℤ) d))

/-- The stub direction at `v_e^1`: the first of right, down, left, up not used (as
`embed_lemma.py` chooses it). -/
def stubDir (w : ℕ) : GP :=
  (([1, 2, 3, 0].map dirV).find? (fun d => decide (d ∉ Dr.usedDirs w))).getD (dirV 1)

/-- The deployment hex `p_e`: two hexes from the centre of `v_e^1` along the stub direction. -/
def pHex (e : ℕ) : Hex := mv (φ (Dr.loc (Dr.root e))) 2 (Dr.stubDir (Dr.root e))

/-- The two stub hexes. -/
def stub (e : ℕ) : List Hex :=
  [mv (φ (Dr.loc (Dr.root e))) 1 (Dr.stubDir (Dr.root e)), Dr.pHex e]

/-- The missing direction of a set vertex (the first unused port). -/
def missing (w : ℕ) : ℕ := ((List.range 4).find? (fun p => decide (dirV p ∉ Dr.usedDirs w))).getD 0

/-- The adapter of a set vertex. -/
def arms (w : ℕ) : List (ℕ × List (ℕ × ℕ)) := armsOf (Dr.missing w)

/-- The edge arriving at port `p` of `w`. -/
def portEdge (w p : ℕ) : Option DEdge := Dr.edges.find? (fun ε => ε.dirAt w == some (dirV p))

/-- The element that owns the arm at port `p` of the set vertex `w`: the element of the edge
arriving there. -/
def armOwner (w p : ℕ) : ℕ := match Dr.portEdge w p with
  | some ε => Dr.elemOf ε.u
  | none => 0

/-- **The region `R_e`** as a list: the pluses of `e`'s path vertices, the stub, the corridors of
the edges of `e` (path edges and incidence edges), and the adapter arms owned by `e`. -/
def region (e : ℕ) : List Hex :=
  ((List.range Dr.nV).filter (fun v => !Dr.isSet v && Dr.elemOf v == e)).flatMap Dr.plus ++
  Dr.stub e ++
  (Dr.edges.filter (fun ε => Dr.elemOf ε.u == e)).flatMap DEdge.corr ++
  ((List.range Dr.nV).filter Dr.isSet).flatMap (fun w =>
    ((Dr.arms w).filter (fun a => Dr.armOwner w a.1 == e)).flatMap
      (fun a => a.2.map (boxHex (Dr.loc w))))

/-- The enemy hex `z_g`: the centre of `g`'s set box. -/
def zHex (g : ℕ) : Hex := φ (Dr.loc (Dr.setV g))

/-- The docking `d_g^e`: the last hex of the arm owned by `e` in `g`'s box. -/
def dHex (g e : ℕ) : Hex :=
  match (Dr.arms (Dr.setV g)).find? (fun a => Dr.armOwner (Dr.setV g) a.1 == e) with
  | some a => boxHex (Dr.loc (Dr.setV g)) (a.2.getLastD (0, 0))
  | none => ⟨0, 0⟩

/-- Board dimensions: `λ·(g − 1) + 2ω + 1` for a grid side `g`. -/
def width : ℕ := 20 * Dr.gw - 7
def height : ℕ := 20 * Dr.gh - 7

/-- A free hex: in some region or an enemy hex. -/
def Free (P : X3C) (h : Hex) : Prop :=
  (∃ e < 3 * P.q, h ∈ Dr.region e) ∨ (∃ g < P.n, h = Dr.zHex g)

instance (P : X3C) : DecidablePred (Dr.Free P) := fun h => by unfold Free; infer_instance

end OrthoDrawing

/-- The hexes of a `W × H` board. -/
def rectF (W H : ℕ) : Finset Hex :=
  ((Finset.range W) ×ˢ (Finset.range H)).image (fun pr => (⟨pr.1, pr.2⟩ : Hex))

open OrthoDrawing in
/-- **The board of Lemma D.4, steps 4–6**, built from the drawing. -/
def build (P : X3C) (Dr : OrthoDrawing) : X3CBoard where
  width := Dr.width
  height := Dr.height
  obst := (rectF Dr.width Dr.height).filter (fun h => ¬ Dr.Free P h)
  p := Dr.pHex
  z := Dr.zHex
  d := Dr.dHex
  R e := (Dr.region e).toFinset
  σ := Dr.width * Dr.height

namespace OrthoDrawing

variable (Dr : OrthoDrawing)

/-- **Validity of a drawing for the instance `P`.**

* `G'` (step 1): member `g` has one set vertex, element `e` has path vertices `elem e i` with
  `elem e 0` present and `elem e (i+1)` joined to `elem e i` by a path edge; every edge leaves an
  element vertex of some `e` and ends at an element vertex of the same `e` or at the set vertex of a
  member containing `e`; at a set vertex the three edges come from the three elements of the member.
* (D1): distinct vertex points.
* (D2): every route is a unit-step grid path without repeated points from `pos u` to `pos v`, and
  each (vertex, direction) pair is used by at most one route.
* (D3): a route meets a vertex point only at its own ends, and two routes meet only at the point of
  a common end.
* (D4), made explicit: all points lie in the bounding box `[0, gw) × [0, gh)`. -/
structure Valid (P : X3C) : Prop where
  wf : P.WF
  len : Dr.pos.length = Dr.nV
  kindNodup : Dr.kind.Nodup
  kindSet : ∀ v < Dr.nV, ∀ g, Dr.K v = .set g → g < P.n
  kindElem : ∀ v < Dr.nV, ∀ e i, Dr.K v = .elem e i → e < 3 * P.q
  setEx : ∀ g < P.n, VK.set g ∈ Dr.kind
  rootEx : ∀ e < 3 * P.q, VK.elem e 0 ∈ Dr.kind
  pathEx : ∀ v < Dr.nV, ∀ e i, Dr.K v = .elem e (i + 1) →
    ∃ ε ∈ Dr.edges, ε.v = v ∧ Dr.K ε.u = .elem e i
  eEnds : ∀ ε ∈ Dr.edges, ε.u < Dr.nV ∧ ε.v < Dr.nV
  eSrc : ∀ ε ∈ Dr.edges, Dr.isSet ε.u = false
  eTgt : ∀ ε ∈ Dr.edges, (Dr.isSet ε.v = false ∧ Dr.elemOf ε.v = Dr.elemOf ε.u) ∨
    (∃ g, Dr.K ε.v = .set g ∧ Dr.elemOf ε.u ∈ P.set g)
  setDist : ∀ ε ∈ Dr.edges, ∀ ε' ∈ Dr.edges, ε.v = ε'.v → Dr.isSet ε.v = true →
    Dr.elemOf ε.u = Dr.elemOf ε'.u → ε = ε'
  setCov : ∀ g < P.n, ∀ e ∈ P.set g, ∃ ε ∈ Dr.edges, ε.v = Dr.setV g ∧ Dr.elemOf ε.u = e
  /-- (D1) -/
  posNodup : Dr.pos.Nodup
  posBox : ∀ a ∈ Dr.pos, 0 ≤ a.1 ∧ a.1 < Dr.gw ∧ 0 ≤ a.2 ∧ a.2 < Dr.gh
  /-- (D2) -/
  route : ∀ ε ∈ Dr.edges, ε.OK
  rHead : ∀ ε ∈ Dr.edges, ε.rp 0 = Dr.loc ε.u
  rLast : ∀ ε ∈ Dr.edges, ε.rp ε.k = Dr.loc ε.v
  rBox : ∀ ε ∈ Dr.edges, ∀ a ∈ ε.r, 0 ≤ a.1 ∧ a.1 < Dr.gw ∧ 0 ≤ a.2 ∧ a.2 < Dr.gh
  ports : ∀ ε ∈ Dr.edges, ∀ ε' ∈ Dr.edges, ∀ w d, ε.dirAt w = some d → ε'.dirAt w = some d → ε = ε'
  /-- (D3) -/
  noThrough : ∀ ε ∈ Dr.edges, ∀ w < Dr.nV, Dr.loc w ∈ ε.r → w = ε.u ∨ w = ε.v
  noCross : ∀ ε ∈ Dr.edges, ∀ ε' ∈ Dr.edges, ε ≠ ε' → ∀ x ∈ ε.r, x ∈ ε'.r →
    ∃ w < Dr.nV, x = Dr.loc w ∧ (w = ε.u ∨ w = ε.v) ∧ (w = ε'.u ∨ w = ε'.v)

variable {Dr} {P : X3C}

/-! ## Basic facts about a valid drawing -/

section Basic

variable (V : Dr.Valid P)
include V

omit V in
theorem K_mem {v : ℕ} (hv : v < Dr.nV) : Dr.K v ∈ Dr.kind := by
  unfold K nV at *; rw [List.getD_eq_getElem _ _ hv]; exact List.getElem_mem _

theorem K_inj {v w : ℕ} (hv : v < Dr.nV) (hw : w < Dr.nV) (h : Dr.K v = Dr.K w) : v = w := by
  unfold K nV at *
  rw [List.getD_eq_getElem _ _ hv, List.getD_eq_getElem _ _ hw] at h
  exact (V.kindNodup.getElem_inj_iff).mp h

theorem P_inj {v w : ℕ} (hv : v < Dr.nV) (hw : w < Dr.nV) (h : Dr.loc v = Dr.loc w) : v = w := by
  have hl := V.len
  unfold loc nV at *
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
  exact (V.posNodup.getElem_inj_iff).mp h

theorem P_box {v : ℕ} (hv : v < Dr.nV) :
    0 ≤ (Dr.loc v).1 ∧ (Dr.loc v).1 < Dr.gw ∧ 0 ≤ (Dr.loc v).2 ∧ (Dr.loc v).2 < Dr.gh := by
  have hl := V.len
  apply V.posBox
  unfold loc nV at *; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _

theorem setV_spec {g : ℕ} (hg : g < P.n) : Dr.setV g < Dr.nV ∧ Dr.K (Dr.setV g) = .set g := by
  have hm := V.setEx g hg
  have hlt : Dr.setV g < Dr.nV := List.idxOf_lt_length_iff.mpr hm
  refine ⟨hlt, ?_⟩
  unfold K; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_idxOf hlt

theorem root_spec {e : ℕ} (he : e < 3 * P.q) : Dr.root e < Dr.nV ∧ Dr.K (Dr.root e) = .elem e 0 := by
  have hm := V.rootEx e he
  have hlt : Dr.root e < Dr.nV := List.idxOf_lt_length_iff.mpr hm
  refine ⟨hlt, ?_⟩
  unfold K; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_idxOf hlt

theorem eq_setV {v g : ℕ} (hv : v < Dr.nV) (h : Dr.K v = .set g) : v = Dr.setV g := by
  have hg := V.kindSet v hv g h
  exact K_inj V hv (setV_spec V hg).1 (by rw [h, (setV_spec V hg).2])

theorem eq_root {v e : ℕ} (hv : v < Dr.nV) (h : Dr.K v = .elem e 0) : v = Dr.root e := by
  have he := V.kindElem v hv e 0 h
  exact K_inj V hv (root_spec V he).1 (by rw [h, (root_spec V he).2])

theorem setV_inj {g g' : ℕ} (hg : g < P.n) (hg' : g' < P.n) (h : Dr.setV g = Dr.setV g') : g = g' := by
  have h1 := (setV_spec V hg).2
  rw [h, (setV_spec V hg').2] at h1
  injection h1 with h1; exact h1.symm

end Basic

theorem isSet_iff {v : ℕ} : Dr.isSet v = true ↔ ∃ g, Dr.K v = .set g := by
  unfold isSet; cases Dr.K v <;> simp

theorem isSet_false_iff {v : ℕ} : Dr.isSet v = false ↔ ∃ i, Dr.K v = .elem (Dr.elemOf v) i := by
  unfold isSet elemOf; cases Dr.K v <;> simp

theorem isSet_of_K {v g : ℕ} (h : Dr.K v = .set g) : Dr.isSet v = true := by
  unfold isSet; rw [h]

theorem notSet_of_K {v e i : ℕ} (h : Dr.K v = .elem e i) : Dr.isSet v = false ∧ Dr.elemOf v = e := by
  unfold isSet elemOf; rw [h]; exact ⟨rfl, rfl⟩

/-! ## Directions -/

theorem dirAt_some {ε : DEdge} {w : ℕ} {d : GP} (h : ε.dirAt w = some d) :
    (w = ε.u ∧ d = ε.du) ∨ (w = ε.v ∧ w ≠ ε.u ∧ d = ε.dv) := by
  unfold DEdge.dirAt at h
  split_ifs at h with h1 h2
  · exact Or.inl ⟨h1.symm, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨h2.symm, fun h => h1 h.symm, (Option.some.inj h).symm⟩

theorem dirAt_u (ε : DEdge) : ε.dirAt ε.u = some ε.du := by simp [DEdge.dirAt]

theorem dirAt_v {ε : DEdge} (h : ε.u ≠ ε.v) : ε.dirAt ε.v = some ε.dv := by
  simp [DEdge.dirAt, h]

theorem mem_usedDirs {w : ℕ} {d : GP} : d ∈ Dr.usedDirs w ↔ ∃ ε ∈ Dr.edges, ε.dirAt w = some d := by
  simp [usedDirs, List.mem_filterMap]

section Edges

variable (V : Dr.Valid P)
include V

theorem u_ne_v {ε : DEdge} (hε : ε ∈ Dr.edges) : ε.u ≠ ε.v := by
  intro h
  have hk := DEdge.k_pos (V.route ε hε)
  have := DEdge.rp_inj (V.route ε hε) (i := 0) (j := ε.k) (by omega) le_rfl
    (by rw [V.rHead ε hε, V.rLast ε hε, h])
  omega

theorem dirAt_unit {ε : DEdge} (hε : ε ∈ Dr.edges) {w : ℕ} {d : GP} (h : ε.dirAt w = some d) :
    IsUnit d := by
  rcases dirAt_some h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · exact DEdge.du_unit (V.route ε hε)
  · exact DEdge.dv_unit (V.route ε hε)

theorem usedDirs_unit {w : ℕ} {d : GP} (h : d ∈ Dr.usedDirs w) : IsUnit d := by
  obtain ⟨ε, hε, h⟩ := mem_usedDirs.mp h
  exact dirAt_unit V hε h

/-- The grid point of an end `w` of `ε` is the route's first or last point. -/
theorem end_pt {ε : DEdge} (hε : ε ∈ Dr.edges) {w : ℕ} (hw : w = ε.u ∨ w = ε.v) :
    (w = ε.u ∧ Dr.loc w = ε.rp 0) ∨ (w = ε.v ∧ w ≠ ε.u ∧ Dr.loc w = ε.rp ε.k) := by
  rcases hw with rfl | rfl
  · exact Or.inl ⟨rfl, (V.rHead ε hε).symm⟩
  · exact Or.inr ⟨rfl, (u_ne_v V hε).symm, (V.rLast ε hε).symm⟩

/-- **A corridor point on a segment ending at the point of a vertex `w`** is on the run from `w`'s
image in the direction the route leaves `w`, at parameter `≥ 5`. -/
theorem cor_at {ε : DEdge} (hε : ε ∈ Dr.edges) {s j t : ℕ} (hs1 : 5 ≤ s) (hs2 : s ≤ 20 * ε.k - 5)
    (hj : j < ε.k) (ht : t ≤ 20) (hst : s = 20 * j + t)
    {w : ℕ} (hw : w < Dr.nV) (hx : Dr.loc w = ε.rp j ∨ Dr.loc w = ε.rp (j + 1)) :
    ∃ τ : ℤ, ∃ d, 5 ≤ τ ∧ τ ≤ 20 ∧ ε.dirAt w = some d ∧ ε.pt s = mv (φ (Dr.loc w)) τ d := by
  have hR := V.route ε hε
  have hmem : Dr.loc w ∈ ε.r := by
    rcases hx with hx | hx
    · rw [hx]; exact DEdge.rp_mem hR (by omega)
    · rw [hx]; exact DEdge.rp_mem hR (by omega)
  rcases end_pt V hε (V.noThrough ε hε w hw hmem) with ⟨rfl, hp⟩ | ⟨rfl, hne, hp⟩
  · rw [hp] at hx ⊢
    obtain ⟨h20, hpt⟩ := DEdge.near_u hR hj hst ht (by rcases hx with h | h <;> [left; right] <;> exact h)
    exact ⟨s, ε.du, by omega, by omega, dirAt_u ε, hpt⟩
  · rw [hp] at hx ⊢
    obtain ⟨h1, h2, hpt⟩ := DEdge.near_v hR hj hst ht (by rcases hx with h | h <;> [left; right] <;> exact h)
    exact ⟨((20 * ε.k - s : ℕ) : ℤ), ε.dv, by omega, by omega, dirAt_v (u_ne_v V hε), hpt⟩

/-- A corridor point is either `≥ 20` from the image of a vertex, or on the run from it. -/
theorem cor_far_or_near {ε : DEdge} (hε : ε ∈ Dr.edges) {s : ℕ} (hs1 : 5 ≤ s)
    (hs2 : s ≤ 20 * ε.k - 5) {w : ℕ} (hw : w < Dr.nV) :
    20 ≤ linf (ε.pt s) (φ (Dr.loc w)) ∨
      ∃ τ : ℤ, ∃ d, 5 ≤ τ ∧ τ ≤ 20 ∧ ε.dirAt w = some d ∧ ε.pt s = mv (φ (Dr.loc w)) τ d := by
  have hR := V.route ε hε
  obtain ⟨j, hj, t, ht, hst, hpt⟩ := DEdge.pt_seg hR (s := s) (by omega)
  by_cases hx : Dr.loc w = ε.rp j ∨ Dr.loc w = ε.rp (j + 1)
  · exact Or.inr (cor_at V hε hs1 hs2 hj ht hst hw hx)
  · push Not at hx
    left; rw [hpt]; exact DEdge.pt_far hR hj ht hx.1 hx.2

end Edges

/-! ## The features of a region -/

theorem linf_self (a : Hex) : linf a a = 0 := by simp [linf]

theorem linf_chain (a b c d : Hex) : linf a d ≤ linf a b + linf b c + linf c d := by
  have h1 := linf_triangle a b d
  have h2 := linf_triangle b c d
  linarith

theorem boxHex_x (a : GP) (c : ℕ × ℕ) : (boxHex a c).x = (c.1 : ℤ) + 20 * a.1 + 2 := by
  simp only [boxHex, shift, cell]; ring
theorem boxHex_y (a : GP) (c : ℕ × ℕ) : (boxHex a c).y = (c.2 : ℤ) + 20 * a.2 + 2 := by
  simp only [boxHex, shift, cell]; ring

theorem boxHex_near {a : GP} {c : ℕ × ℕ} (h1 : c.1 < 9) (h2 : c.2 < 9) :
    linf (boxHex a c) (φ a) ≤ 4 := by
  rw [linf_le, boxHex_x, boxHex_y]; simp only [φ_x, φ_y]; omega

theorem boxHex_inj {a : GP} {c c' : ℕ × ℕ} (h : boxHex a c = boxHex a c') : c = c' := by
  have hx := congrArg Hex.x h
  have hy := congrArg Hex.y h
  rw [boxHex_x, boxHex_x] at hx; rw [boxHex_y, boxHex_y] at hy
  ext <;> omega

theorem boxHex_adj {a : GP} {c c' : ℕ × ℕ} :
    Hex.Adj (boxHex a c) (boxHex a c') ↔ Hex.Adj (cell c) (cell c') := adj_shift

theorem missing_lt (w : ℕ) : Dr.missing w < 4 := by
  unfold missing
  cases h : (List.range 4).find? (fun p => decide (dirV p ∉ Dr.usedDirs w)) with
  | none => simp
  | some p => simpa using List.mem_of_find?_eq_some h

theorem stubDir_unit (w : ℕ) : IsUnit (Dr.stubDir w) := by
  unfold stubDir
  cases h : ([1, 2, 3, 0].map dirV).find? (fun d => decide (d ∉ Dr.usedDirs w)) with
  | none => exact isUnit_dirV 1
  | some d =>
    rw [Option.getD_some]
    have := List.mem_of_find?_eq_some h
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl <;> exact isUnit_dirV _

theorem mem_plus {w : ℕ} {h : Hex} : h ∈ Dr.plus w ↔
    h = φ (Dr.loc w) ∨ ∃ d ∈ Dr.usedDirs w, ∃ t < 5, h = mv (φ (Dr.loc w)) (t : ℕ) d := by
  simp only [plus, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro (h | ⟨d, hd, t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, hd, t, ht, rfl⟩
  · rintro (h | ⟨d, hd, t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨d, hd, t, ht, rfl⟩

theorem mem_region {e : ℕ} {h : Hex} : h ∈ Dr.region e ↔
    ((∃ v < Dr.nV, Dr.isSet v = false ∧ Dr.elemOf v = e ∧ h ∈ Dr.plus v) ∨ h ∈ Dr.stub e) ∨
    (∃ ε ∈ Dr.edges, Dr.elemOf ε.u = e ∧ h ∈ ε.corr) ∨
    (∃ w < Dr.nV, Dr.isSet w = true ∧ ∃ a ∈ Dr.arms w, Dr.armOwner w a.1 = e ∧
      ∃ c ∈ a.2, h = boxHex (Dr.loc w) c) := by
  simp only [region, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
    Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.mem_map]
  constructor
  · rintro (((⟨v, ⟨hv, h1, h2⟩, hp⟩ | hs) | ⟨ε, ⟨hε, h1⟩, hc⟩) | ⟨w, ⟨hw, h1⟩, a, ⟨ha, h2⟩, c, hc, rfl⟩)
    · exact Or.inl (Or.inl ⟨v, hv, h1, h2, hp⟩)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr (Or.inl ⟨ε, hε, h1, hc⟩)
    · exact Or.inr (Or.inr ⟨w, hw, h1, a, ha, h2, c, hc, rfl⟩)
  · rintro ((⟨v, hv, h1, h2, hp⟩ | hs) | ⟨ε, hε, h1, hc⟩ | ⟨w, hw, h1, a, ha, h2, c, hc, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨v, ⟨hv, h1, h2⟩, hp⟩))
    · exact Or.inl (Or.inl (Or.inr hs))
    · exact Or.inl (Or.inr ⟨ε, ⟨hε, h1⟩, hc⟩)
    · exact Or.inr ⟨w, ⟨hw, h1⟩, a, ⟨ha, h2⟩, c, hc, rfl⟩

/-- A hex of an element box of `e`. -/
def EBox (e : ℕ) (h : Hex) : Prop :=
  ∃ v < Dr.nV, Dr.isSet v = false ∧ Dr.elemOf v = e ∧ linf h (φ (Dr.loc v)) ≤ 4

/-- A corridor hex of an edge of `e`. -/
def ECor (e : ℕ) (h : Hex) : Prop :=
  ∃ ε ∈ Dr.edges, Dr.elemOf ε.u = e ∧ ∃ s, 5 ≤ s ∧ s ≤ 20 * ε.k - 5 ∧ 1 ≤ ε.k ∧ h = ε.pt s

/-- A hex of an adapter arm owned by `e`. -/
def EArm (e : ℕ) (h : Hex) : Prop :=
  ∃ w < Dr.nV, Dr.isSet w = true ∧ ∃ a ∈ Dr.arms w, Dr.armOwner w a.1 = e ∧
    ∃ c ∈ a.2, h = boxHex (Dr.loc w) c

section Prox

variable (V : Dr.Valid P)
include V

theorem plus_near {w : ℕ} {h : Hex} (hh : h ∈ Dr.plus w) : linf h (φ (Dr.loc w)) ≤ 4 := by
  rcases mem_plus.mp hh with rfl | ⟨d, hd, t, ht, rfl⟩
  · rw [linf_le]; omega
  · rw [linf_mv _ (by omega) (usedDirs_unit V hd)]; omega

theorem feat {e : ℕ} (he : e < 3 * P.q) {h : Hex} (hh : h ∈ Dr.region e) :
    Dr.EBox e h ∨ Dr.ECor e h ∨ Dr.EArm e h := by
  rcases mem_region.mp hh with (⟨v, hv, h1, h2, hp⟩ | hs) | ⟨ε, hε, h1, hc⟩ | ha
  · exact Or.inl ⟨v, hv, h1, h2, plus_near V hp⟩
  · obtain ⟨hr, hK⟩ := root_spec V he
    obtain ⟨h1, h2⟩ := notSet_of_K hK
    refine Or.inl ⟨Dr.root e, hr, h1, h2, ?_⟩
    simp only [stub, pHex, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · rw [linf_mv _ (by norm_num) (stubDir_unit _)]; norm_num
    · rw [linf_mv _ (by norm_num) (stubDir_unit _)]; norm_num
  · obtain ⟨s, hs1, hs2, hk, rfl⟩ := DEdge.mem_corr.mp hc
    exact Or.inr (Or.inl ⟨ε, hε, h1, s, hs1, hs2, hk, rfl⟩)
  · exact Or.inr (Or.inr ha)

omit V in
theorem arm_near {w : ℕ} {a : ℕ × List (ℕ × ℕ)} (ha : a ∈ Dr.arms w) {c : ℕ × ℕ} (hc : c ∈ a.2) :
    linf (boxHex (Dr.loc w) c) (φ (Dr.loc w)) ≤ 4 := by
  obtain ⟨h1, h2, -⟩ := arms_cells _ (missing_lt w) a ha c hc
  exact boxHex_near h1 h2

/-- Two boxes of distinct vertices are `≥ 12` apart. -/
theorem box_box {v w : ℕ} (hv : v < Dr.nV) (hw : w < Dr.nV) (hne : v ≠ w) {h h' : Hex}
    (h1 : linf h (φ (Dr.loc v)) ≤ 4) (h2 : linf h' (φ (Dr.loc w)) ≤ 4) : 12 ≤ linf h h' := by
  have hs := sep_vv (fun he => hne (P_inj V hv hw he))
  have := linf_chain (φ (Dr.loc v)) h h' (φ (Dr.loc w))
  rw [linf_comm] at h1
  linarith

/-- The arm at port `p` belongs to the element of the edge arriving there. -/
theorem armOwner_eq {ε : DEdge} (hε : ε ∈ Dr.edges) {w p : ℕ} (h : ε.dirAt w = some (dirV p)) :
    Dr.armOwner w p = Dr.elemOf ε.u := by
  unfold armOwner portEdge
  cases hf : Dr.edges.find? (fun ε => ε.dirAt w == some (dirV p)) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf ε hε
    simp [h] at this
  | some ε' =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [beq_iff_eq] at h1
    rw [V.ports ε' h2 ε hε w _ h1 h]

theorem prox_box_cor {e e' : ℕ} {h h' : Hex} (h1 : Dr.EBox e h) (h2 : Dr.ECor e' h')
    (hl : linf h h' ≤ 1) : e = e' := by
  obtain ⟨v, hv, hs, rfl, hb⟩ := h1
  obtain ⟨ε, hε, rfl, s, hs1, hs2, -, rfl⟩ := h2
  rcases cor_far_or_near V hε hs1 hs2 hv with hfar | ⟨τ, d, hτ, -, hd, -⟩
  · exfalso
    have := linf_chain (ε.pt s) h (φ (Dr.loc v)) (φ (Dr.loc v))
    rw [linf_comm (ε.pt s) h] at this
    rw [linf_self] at this
    linarith
  · rcases dirAt_some hd with ⟨rfl, -⟩ | ⟨rfl, -, -⟩
    · rfl
    · rcases V.eTgt ε hε with ⟨-, h⟩ | ⟨g, hK, -⟩
      · exact h
      · rw [isSet_of_K hK] at hs; exact absurd hs (by decide)

theorem prox_box_box {e e' : ℕ} {h h' : Hex} (h1 : Dr.EBox e h) (h2 : Dr.EBox e' h')
    (hl : linf h h' ≤ 1) : e = e' := by
  obtain ⟨v, hv, -, rfl, hb⟩ := h1
  obtain ⟨w, hw, -, rfl, hb'⟩ := h2
  by_cases hvw : v = w
  · rw [hvw]
  · have := box_box V hv hw hvw hb hb'; linarith

theorem prox_box_arm {e e' : ℕ} {h h' : Hex} (h1 : Dr.EBox e h) (h2 : Dr.EArm e' h')
    (hl : linf h h' ≤ 1) : False := by
  obtain ⟨v, hv, hs, -, hb⟩ := h1
  obtain ⟨w, hw, hs', a, ha, -, c, hc, rfl⟩ := h2
  have hne : v ≠ w := by rintro rfl; rw [hs] at hs'; exact absurd hs' (by decide)
  have := box_box V hv hw hne hb (arm_near ha hc); linarith

theorem prox_cor_cor {e e' : ℕ} {h h' : Hex} (h1 : Dr.ECor e h) (h2 : Dr.ECor e' h')
    (hl : linf h h' ≤ 1) : e = e' := by
  obtain ⟨ε, hε, rfl, s, hs1, hs2, hk, rfl⟩ := h1
  obtain ⟨ε', hε', rfl, s', hs1', hs2', hk', rfl⟩ := h2
  by_cases hee : ε = ε'
  · rw [hee]
  exfalso
  have hR := V.route ε hε
  have hR' := V.route ε' hε'
  obtain ⟨j, hj, t, ht, hst, hpt⟩ := DEdge.pt_seg hR (s := s) (by omega)
  obtain ⟨j', hj', t', ht', hst', hpt'⟩ := DEdge.pt_seg hR' (s := s') (by omega)
  by_cases hsh : ∃ x, (x = ε.rp j ∨ x = ε.rp (j + 1)) ∧ (x = ε'.rp j' ∨ x = ε'.rp (j' + 1))
  · obtain ⟨x, hx, hx'⟩ := hsh
    have hxm : x ∈ ε.r := by
      rcases hx with rfl | rfl <;> exact DEdge.rp_mem hR (by omega)
    have hxm' : x ∈ ε'.r := by
      rcases hx' with rfl | rfl <;> exact DEdge.rp_mem hR' (by omega)
    obtain ⟨w, hw, rfl, -, -⟩ := V.noCross ε hε ε' hε' hee _ hxm hxm'
    obtain ⟨τ, d, hτ, -, hd, hp⟩ := cor_at V hε hs1 hs2 hj ht hst hw hx
    obtain ⟨τ', d', hτ', -, hd', hp'⟩ := cor_at V hε' hs1' hs2' hj' ht' hst' hw hx'
    by_cases hdd : d = d'
    · subst hdd; exact hee (V.ports ε hε ε' hε' w d hd hd')
    · have := sep_rays (c := φ (Dr.loc w)) (dirAt_unit V hε hd) (dirAt_unit V hε' hd') hdd hτ hτ'
      rw [← hp, ← hp'] at this; linarith
  · have hn : ∀ x, (x = ε.rp j ∨ x = ε.rp (j + 1)) → (x = ε'.rp j' ∨ x = ε'.rp (j' + 1)) → False :=
      fun x hx hx' => hsh ⟨x, hx, hx'⟩
    have := sep_seg (hR.unit j hj) (hR'.unit j' hj') (t := t) (t' := t') (by positivity)
      (by exact_mod_cast ht) (by positivity) (by exact_mod_cast ht')
      (fun he => hn _ (Or.inl rfl) (Or.inl he))
      (fun he => hn _ (Or.inl rfl) (Or.inr (by rw [DEdge.rp_succ]; exact he)))
      (fun he => hn _ (Or.inr rfl) (Or.inl (by rw [DEdge.rp_succ]; exact he)))
      (fun he => hn _ (Or.inr rfl) (Or.inr (by rw [DEdge.rp_succ, DEdge.rp_succ]; exact he)))
    rw [← hpt, ← hpt'] at this; linarith

theorem prox_cor_arm {e e' : ℕ} {h h' : Hex} (h1 : Dr.ECor e h) (h2 : Dr.EArm e' h')
    (hl : linf h h' ≤ 1) : e = e' := by
  obtain ⟨ε, hε, rfl, s, hs1, hs2, hk, rfl⟩ := h1
  obtain ⟨w, hw, hsw, a, ha, rfl, c, hc, rfl⟩ := h2
  have hb := arm_near ha hc
  rcases cor_far_or_near V hε hs1 hs2 hw with hfar | ⟨τ, d, hτ, -, hd, hp⟩
  · exfalso
    have := linf_chain (ε.pt s) (boxHex (Dr.loc w) c) (φ (Dr.loc w)) (φ (Dr.loc w))
    rw [linf_self] at this; linarith
  · rw [hp] at hl
    obtain ⟨hside, -⟩ := box_ray (dirAt_unit V hε hd) hτ hb (by rwa [linf_comm] at hl)
    obtain ⟨p, hp4, rfl⟩ := (isUnit_iff d).mp (dirAt_unit V hε hd)
    rw [boxHex_x, boxHex_y, φ_x, φ_y] at hside
    have e1 : ((c.1 : ℤ) + 20 * (Dr.loc w).1 + 2 - (20 * (Dr.loc w).1 + 6)) = (c.1 : ℤ) - 4 := by ring
    have e2 : ((c.2 : ℤ) + 20 * (Dr.loc w).2 + 2 - (20 * (Dr.loc w).2 + 6)) = (c.2 : ℤ) - 4 := by ring
    rw [e1, e2] at hside
    have := arms_side _ (missing_lt w) a ha c hc p hp4 hside
    rw [this, armOwner_eq V hε hd]

theorem prox_arm_arm {e e' : ℕ} {h h' : Hex} (h1 : Dr.EArm e h) (h2 : Dr.EArm e' h')
    (hl : h = h' ∨ Hex.Adj h h') : e = e' := by
  obtain ⟨w, hw, -, a, ha, rfl, c, hc, rfl⟩ := h1
  obtain ⟨w', hw', -, a', ha', rfl, c', hc', rfl⟩ := h2
  by_cases hww : w = w'
  · subst hww
    by_cases hp : a.1 = a'.1
    · rw [hp]
    · exfalso
      obtain ⟨hne, hna⟩ := arms_apart _ (missing_lt w) a ha a' ha' hp c hc c' hc'
      rcases hl with h | h
      · exact hne (boxHex_inj h)
      · exact hna (boxHex_adj.mp h)
  · exfalso
    have := box_box V hw hw' hww (arm_near ha hc) (arm_near ha' hc')
    have := linf_le_one_of_adj hl; linarith

/-- **The separation lemma for regions**: hexes of `R_e` and `R_{e'}` that coincide or are
adjacent have `e = e'`.  Three feature classes (element boxes with the stub, corridors, adapter
arms), six pairs: distinct boxes by (SEP′); a box and a corridor meet only at a port of an incident
edge; two corridors meet only near a common end, where the ports differ (D2); arms of one adapter
do not touch (Lemma D.3). -/
theorem prox {e e' : ℕ} (he : e < 3 * P.q) (he' : e' < 3 * P.q) {h h' : Hex}
    (hh : h ∈ Dr.region e) (hh' : h' ∈ Dr.region e') (hl : h = h' ∨ Hex.Adj h h') : e = e' := by
  have hl1 := linf_le_one_of_adj hl
  have hl1' : linf h' h ≤ 1 := by rwa [linf_comm]
  rcases feat V he hh with f | f | f <;> rcases feat V he' hh' with f' | f' | f'
  · exact prox_box_box V f f' hl1
  · exact prox_box_cor V f f' hl1
  · exact (prox_box_arm V f f' hl1).elim
  · exact (prox_box_cor V f' f hl1').symm
  · exact prox_cor_cor V f f' hl1
  · exact prox_cor_arm V f f' hl1
  · exact (prox_box_arm V f' f hl1').elim
  · exact (prox_cor_arm V f' f hl1').symm
  · exact prox_arm_arm V f f' hl

/-! ## The set vertices: three ports, the adapter's arms, the dockings -/

/-- An edge leaving a set vertex's point arrives there from an element of the member. -/
theorem edge_at_set {g : ℕ} (hg : g < P.n) {ε : DEdge} (hε : ε ∈ Dr.edges) {d : GP}
    (h : ε.dirAt (Dr.setV g) = some d) :
    ε.v = Dr.setV g ∧ d = ε.dv ∧ Dr.elemOf ε.u ∈ P.set g := by
  obtain ⟨-, hK⟩ := setV_spec V hg
  rcases dirAt_some h with ⟨hu, -⟩ | ⟨hv, -, hd⟩
  · have := V.eSrc ε hε
    rw [← hu, isSet_of_K hK] at this; exact absurd this (by decide)
  · refine ⟨hv.symm, hd, ?_⟩
    rcases V.eTgt ε hε with ⟨h1, -⟩ | ⟨g', hK', hm⟩
    · rw [← hv, isSet_of_K hK] at h1; exact absurd h1 (by decide)
    · rw [← hv, hK] at hK'; injection hK' with hg'; rw [hg']; exact hm

omit V in
theorem missing_unused {w : ℕ} (hex : ∃ p < 4, dirV p ∉ Dr.usedDirs w) :
    dirV (Dr.missing w) ∉ Dr.usedDirs w := by
  unfold missing
  cases hf : (List.range 4).find? (fun p => decide (dirV p ∉ Dr.usedDirs w)) with
  | none =>
    exfalso
    obtain ⟨p, hp, hu⟩ := hex
    have := List.find?_eq_none.mp hf p (List.mem_range.mpr hp)
    simp [hu] at this
  | some m =>
    have := List.find?_some hf
    simpa using this

/-- **At a set vertex exactly the ports other than the missing one are used** (a counting
argument: three edges from the three elements of the member, with pairwise different directions
by (D2)). -/
theorem set_ports {g : ℕ} (hg : g < P.n) {p : ℕ} (hp : p < 4) :
    p ≠ Dr.missing (Dr.setV g) ↔ ∃ ε ∈ Dr.edges, ε.dirAt (Dr.setV g) = some (dirV p) := by
  set w := Dr.setV g with hw_def
  obtain ⟨hwlt, hK⟩ := setV_spec V hg
  have hcard := V.wf.card g hg
  obtain ⟨e1, e2, e3, h12, h13, h23, hS⟩ := Finset.card_eq_three.mp hcard
  have hedge : ∀ e ∈ P.set g, ∃ ε ∈ Dr.edges, ∃ p < 4, ε.v = w ∧ Dr.elemOf ε.u = e ∧
      ε.dirAt w = some (dirV p) := by
    intro e he
    obtain ⟨ε, hε, hv, he'⟩ := V.setCov g hg e he
    rw [← hw_def] at hv
    have hd : ε.dirAt w = some ε.dv := by rw [← hv]; exact dirAt_v (u_ne_v V hε)
    obtain ⟨p, hp, hpd⟩ := (isUnit_iff _).mp (dirAt_unit V hε hd)
    exact ⟨ε, hε, p, hp, hv, he', by rw [hpd]; exact hd⟩
  obtain ⟨ε1, hε1, p1, hp1, hv1, he1, hd1⟩ := hedge e1 (by rw [hS]; simp)
  obtain ⟨ε2, hε2, p2, hp2, hv2, he2, hd2⟩ := hedge e2 (by rw [hS]; simp)
  obtain ⟨ε3, hε3, p3, hp3, hv3, he3, hd3⟩ := hedge e3 (by rw [hS]; simp)
  have hdist : ∀ {a b : ℕ} {εa εb : DEdge}, εa ∈ Dr.edges → εb ∈ Dr.edges → a < 4 → b < 4 →
      εa.dirAt w = some (dirV a) → εb.dirAt w = some (dirV b) → Dr.elemOf εa.u ≠ Dr.elemOf εb.u →
      a ≠ b := by
    intro a b εa εb ha hb _ _ hda hdb hne hab
    subst hab
    exact hne (by rw [V.ports εa ha εb hb w _ hda hdb])
  have q12 := hdist hε1 hε2 hp1 hp2 hd1 hd2 (by rw [he1, he2]; exact h12)
  have q13 := hdist hε1 hε3 hp1 hp3 hd1 hd3 (by rw [he1, he3]; exact h13)
  have q23 := hdist hε2 hε3 hp2 hp3 hd2 hd3 (by rw [he2, he3]; exact h23)
  -- every used port is one of `p1, p2, p3`
  have hall : ∀ p < 4, ∀ ε ∈ Dr.edges, ε.dirAt w = some (dirV p) → p = p1 ∨ p = p2 ∨ p = p3 := by
    intro p hp ε hε hd
    obtain ⟨hv, -, hm⟩ := edge_at_set V hg hε hd
    rw [hS] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hset : Dr.isSet ε.v = true := by rw [hv]; exact isSet_of_K hK
    rcases hm with hm | hm | hm
    · have := V.setDist ε hε ε1 hε1 (by rw [hv, hv1]) hset (by rw [hm, he1]); subst this
      exact Or.inl (dirV_inj hp hp1 (Option.some.inj (hd.symm.trans hd1)))
    · have := V.setDist ε hε ε2 hε2 (by rw [hv, hv2]) hset (by rw [hm, he2]); subst this
      exact Or.inr (Or.inl (dirV_inj hp hp2 (Option.some.inj (hd.symm.trans hd2))))
    · have := V.setDist ε hε ε3 hε3 (by rw [hv, hv3]) hset (by rw [hm, he3]); subst this
      exact Or.inr (Or.inr (dirV_inj hp hp3 (Option.some.inj (hd.symm.trans hd3))))
  have hused : ∀ p < 4, dirV p ∈ Dr.usedDirs w → p = p1 ∨ p = p2 ∨ p = p3 := by
    intro p hp hu
    obtain ⟨ε, hε, hd⟩ := mem_usedDirs.mp hu
    exact hall p hp ε hε hd
  have hex : ∃ p < 4, dirV p ∉ Dr.usedDirs w := by
    by_contra hc
    push Not at hc
    have h0 := hused 0 (by norm_num) (hc 0 (by norm_num))
    have h1 := hused 1 (by norm_num) (hc 1 (by norm_num))
    have h2 := hused 2 (by norm_num) (hc 2 (by norm_num))
    have h3 := hused 3 (by norm_num) (hc 3 (by norm_num))
    omega
  have hm := missing_unused hex
  have hml := missing_lt (Dr := Dr) w
  have hmne : ∀ p < 4, dirV p ∈ Dr.usedDirs w → p ≠ Dr.missing w := by
    intro p _ hu he; rw [he] at hu; exact hm hu
  have hm1 := hmne p1 hp1 (mem_usedDirs.mpr ⟨ε1, hε1, hd1⟩)
  have hm2 := hmne p2 hp2 (mem_usedDirs.mpr ⟨ε2, hε2, hd2⟩)
  have hm3 := hmne p3 hp3 (mem_usedDirs.mpr ⟨ε3, hε3, hd3⟩)
  constructor
  · intro hpm
    have : p = p1 ∨ p = p2 ∨ p = p3 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨ε1, hε1, hd1⟩
    · exact ⟨ε2, hε2, hd2⟩
    · exact ⟨ε3, hε3, hd3⟩
  · rintro ⟨ε, hε, hd⟩
    exact hmne p hp (mem_usedDirs.mpr ⟨ε, hε, hd⟩)

omit V in
theorem arm_port {g : ℕ} {a : ℕ × List (ℕ × ℕ)} (ha : a ∈ Dr.arms (Dr.setV g)) :
    a.1 < 4 ∧ a.1 ≠ Dr.missing (Dr.setV g) := by
  have := arms_ports _ (missing_lt (Dr := Dr) (Dr.setV g))
  have hm : a.1 ∈ (armsOf (Dr.missing (Dr.setV g))).map Prod.fst := List.mem_map_of_mem ha
  unfold arms at ha
  rw [this, List.mem_filter, List.mem_range] at hm
  exact ⟨hm.1, by simpa using hm.2⟩

/-- Every arm of a set box has its edge. -/
theorem arm_edge {g : ℕ} (hg : g < P.n) {a : ℕ × List (ℕ × ℕ)} (ha : a ∈ Dr.arms (Dr.setV g)) :
    ∃ ε ∈ Dr.edges, ε.dirAt (Dr.setV g) = some (dirV a.1) := by
  obtain ⟨h1, h2⟩ := arm_port ha
  exact (set_ports V hg h1).mp h2

/-- Every element of the member owns an arm of its box. -/
theorem arm_of_elem {g : ℕ} (hg : g < P.n) {e : ℕ} (he : e ∈ P.set g) :
    ∃ a ∈ Dr.arms (Dr.setV g), Dr.armOwner (Dr.setV g) a.1 = e := by
  obtain ⟨ε, hε, hv, he'⟩ := V.setCov g hg e he
  have hd : ε.dirAt (Dr.setV g) = some ε.dv := by rw [← hv]; exact dirAt_v (u_ne_v V hε)
  obtain ⟨p, hp, hpd⟩ := (isUnit_iff _).mp (dirAt_unit V hε hd)
  rw [← hpd] at hd
  have hpm := (set_ports V hg hp).mpr ⟨ε, hε, hd⟩
  have hmem : p ∈ (armsOf (Dr.missing (Dr.setV g))).map Prod.fst := by
    rw [arms_ports _ (missing_lt _), List.mem_filter, List.mem_range]; simpa [hp] using hpm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
  exact ⟨a, ha, by rw [armOwner_eq V hε hd, he']⟩

/-- Distinct arms of a set box have distinct owners. -/
theorem arm_owner_inj {g : ℕ} (hg : g < P.n) {a a' : ℕ × List (ℕ × ℕ)}
    (ha : a ∈ Dr.arms (Dr.setV g)) (ha' : a' ∈ Dr.arms (Dr.setV g))
    (h : Dr.armOwner (Dr.setV g) a.1 = Dr.armOwner (Dr.setV g) a'.1) : a = a' := by
  obtain ⟨ε, hε, hd⟩ := arm_edge V hg ha
  obtain ⟨ε', hε', hd'⟩ := arm_edge V hg ha'
  obtain ⟨hv, -, -⟩ := edge_at_set V hg hε hd
  obtain ⟨hv', -, -⟩ := edge_at_set V hg hε' hd'
  rw [armOwner_eq V hε hd, armOwner_eq V hε' hd'] at h
  have hset : Dr.isSet ε.v = true := by rw [hv]; exact isSet_of_K (setV_spec V hg).2
  have := V.setDist ε hε ε' hε' (by rw [hv, hv']) hset h
  subst this
  have hp := dirV_inj (arm_port ha).1 (arm_port ha').1 (Option.some.inj (hd.symm.trans hd'))
  have hnd : ((armsOf (Dr.missing (Dr.setV g))).map Prod.fst).Nodup := by
    rw [arms_ports _ (missing_lt _)]; exact List.nodup_range.filter _
  exact List.inj_on_of_nodup_map hnd ha ha' hp

theorem dHex_spec {g : ℕ} (hg : g < P.n) {a : ℕ × List (ℕ × ℕ)} (ha : a ∈ Dr.arms (Dr.setV g)) :
    Dr.dHex g (Dr.armOwner (Dr.setV g) a.1) = boxHex (Dr.loc (Dr.setV g)) (a.2.getLastD (0, 0)) := by
  unfold dHex
  cases hf : (Dr.arms (Dr.setV g)).find?
      (fun b => Dr.armOwner (Dr.setV g) b.1 == Dr.armOwner (Dr.setV g) a.1) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf a ha
    simp at this
  | some b =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [beq_iff_eq] at h1
    rw [arm_owner_inj V hg h2 ha h1]

omit V in
theorem φ_eq_boxHex (a : GP) : φ a = boxHex a (4, 4) := by
  ext
  · rw [boxHex_x]; simp; ring
  · rw [boxHex_y]; simp; ring

/-- **The enemy hexes and the dockings**: a hex of `R_e` equal or adjacent to `z_g` is not `z_g`,
`e ∈ S_g`, and it is the docking `d_g^e`. -/
theorem near_z {e : ℕ} (he : e < 3 * P.q) {g : ℕ} (hg : g < P.n) {h : Hex} (hh : h ∈ Dr.region e)
    (hz : h = Dr.zHex g ∨ Hex.Adj h (Dr.zHex g)) :
    h ≠ Dr.zHex g ∧ e ∈ P.set g ∧ h = Dr.dHex g e := by
  obtain ⟨hw, hK⟩ := setV_spec V hg
  have hl : linf h (φ (Dr.loc (Dr.setV g))) ≤ 1 := linf_le_one_of_adj hz
  have hz0 : linf (φ (Dr.loc (Dr.setV g))) (φ (Dr.loc (Dr.setV g))) ≤ 4 := by rw [linf_self]; norm_num
  rcases feat V he hh with ⟨v, hv, hs, -, hb⟩ | ⟨ε, hε, rfl, s, hs1, hs2, -, rfl⟩ |
      ⟨w, hw', hsw, a, ha, rfl, c, hc, rfl⟩
  · exfalso
    have hne : v ≠ Dr.setV g := by rintro rfl; rw [isSet_of_K hK] at hs; exact absurd hs (by decide)
    have := box_box V hv hw hne hb hz0; linarith
  · exfalso
    rcases cor_far_or_near V hε hs1 hs2 hw with hfar | ⟨τ, d, hτ, -, hd, hp⟩
    · linarith
    · rw [hp, linf_mv _ (by omega) (dirAt_unit V hε hd)] at hl; linarith
  · by_cases hww : w = Dr.setV g
    · subst hww
      have hzb := φ_eq_boxHex (Dr.loc (Dr.setV g))
      have hne : boxHex (Dr.loc (Dr.setV g)) c ≠ Dr.zHex g := by
        intro heq
        unfold zHex at heq
        rw [hzb] at heq
        exact (arms_cells _ (missing_lt _) a ha c hc).2.2 (boxHex_inj heq)
      refine ⟨hne, ?_, ?_⟩
      · obtain ⟨ε, hε, hd⟩ := arm_edge V hg ha
        rw [armOwner_eq V hε hd]; exact (edge_at_set V hg hε hd).2.2
      · rcases hz with hz | hz
        · exact absurd hz hne
        · unfold zHex at hz; rw [hzb, boxHex_adj] at hz
          have hlast := arms_zadj _ (missing_lt _) a ha c hc hz
          rw [dHex_spec V hg ha, List.getLastD_eq_getLast?, hlast]; rfl
    · exfalso
      have := box_box V hw' hw hww (arm_near ha hc) hz0; linarith

/-! ## The board: bounds, free hexes, (I1) -/

omit V in
theorem mem_rectF {W H : ℕ} {h : Hex} : h ∈ rectF W H ↔ 0 ≤ h.x ∧ h.x < W ∧ 0 ≤ h.y ∧ h.y < H := by
  simp only [rectF, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; simp only; omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h.x.toNat, h.y.toNat, ⟨by omega, by omega⟩, by ext <;> simp <;> omega⟩

/-- The rectangle of the board: `[0, λ(g − 1) + 2ω + 1)` on both axes. -/
def InB (h : Hex) : Prop := 0 ≤ h.x ∧ h.x < Dr.width ∧ 0 ≤ h.y ∧ h.y < Dr.height

omit V in
theorem box_in {a : GP} (ha : 0 ≤ a.1 ∧ a.1 < Dr.gw ∧ 0 ≤ a.2 ∧ a.2 < Dr.gh) {h : Hex}
    (hb : linf h (φ a) ≤ 4) : Dr.InB h := by
  rw [linf_le] at hb; simp only [φ_x, φ_y] at hb
  unfold InB width height; omega

theorem cor_in {ε : DEdge} (hε : ε ∈ Dr.edges) {s : ℕ} (hs : s ≤ 20 * ε.k) : Dr.InB (ε.pt s) := by
  have hR := V.route ε hε
  obtain ⟨j, hj, t, ht, -, hpt⟩ := DEdge.pt_seg hR hs
  have h1 := V.rBox ε hε _ (DEdge.rp_mem hR (j := j) (by omega))
  have h2 := V.rBox ε hε _ (DEdge.rp_mem hR (j := j + 1) (by omega))
  rw [DEdge.rp_succ] at h2
  rw [hpt]
  unfold InB width height
  rcases hR.unit j hj with hd | hd | hd | hd <;> rw [hd] at h2 ⊢ <;>
    simp only [Prod.fst_add, Prod.snd_add, mv_x, mv_y, φ_x, φ_y] at h1 h2 ⊢ <;> omega

theorem region_in {e : ℕ} (he : e < 3 * P.q) {h : Hex} (hh : h ∈ Dr.region e) : Dr.InB h := by
  rcases feat V he hh with ⟨v, hv, -, -, hb⟩ | ⟨ε, hε, -, s, -, hs2, -, rfl⟩ |
      ⟨w, hw, -, a, ha, -, c, hc, rfl⟩
  · exact box_in (P_box V hv) hb
  · exact cor_in V hε (by omega)
  · exact box_in (P_box V hw) (arm_near ha hc)

theorem free_in {h : Hex} (hf : Dr.Free P h) : Dr.InB h := by
  rcases hf with ⟨e, he, hh⟩ | ⟨g, hg, rfl⟩
  · exact region_in V he hh
  · exact box_in (P_box V (setV_spec V hg).1) (by rw [zHex, linf_self]; norm_num)

/-- **The free hexes of the board are exactly the regions and the enemy hexes.** -/
theorem open_iff {h : Hex} : (build P Dr).Open h ↔ Dr.Free P h := by
  simp only [X3CBoard.Open, build, Finset.mem_filter, not_and, not_not]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact h5 (mem_rectF.mpr ⟨h1, h2, h3, h4⟩)
  · intro hf
    obtain ⟨h1, h2, h3, h4⟩ := free_in V hf
    exact ⟨h1, h2, h3, h4, fun _ => hf⟩

omit V in
theorem not_adj_self (h : Hex) : ¬ Hex.Adj h h := fun ha => by
  have := adj_linf ha; rw [linf_self] at this; exact absurd this (by norm_num)

/-- The three docking hexes of `g`'s box. -/
def dock3 (g : ℕ) : List Hex := docks.map (boxHex (Dr.loc (Dr.setV g)))

theorem dock_free {g : ℕ} (hg : g < P.n) {dk : ℕ × ℕ} (hdk : dk ∈ docks) :
    ∃ e < 3 * P.q, e ∈ P.set g ∧ boxHex (Dr.loc (Dr.setV g)) dk ∈ Dr.region e := by
  obtain ⟨a, ha, hl⟩ := arms_docks _ (missing_lt (Dr := Dr) (Dr.setV g)) dk hdk
  obtain ⟨ε, hε, hd⟩ := arm_edge V hg ha
  have hm := (edge_at_set V hg hε hd).2.2
  refine ⟨Dr.armOwner (Dr.setV g) a.1, ?_, ?_, ?_⟩
  · rw [armOwner_eq V hε hd]; exact V.wf.sub g hg _ hm
  · rw [armOwner_eq V hε hd]; exact hm
  · rw [mem_region]
    exact Or.inr (Or.inr ⟨Dr.setV g, (setV_spec V hg).1, isSet_of_K (setV_spec V hg).2, a, ha, rfl,
      dk, List.mem_of_getLast? hl, rfl⟩)

/-- **(I1), first half**: the free neighbours of `z_g` are the three dockings of the adapter. -/
theorem freeNbrs_z {g : ℕ} (hg : g < P.n) :
    (build P Dr).freeNbrs (Dr.zHex g) = (Dr.dock3 g).toFinset := by
  obtain ⟨hw, hK⟩ := setV_spec V hg
  have hzb : Dr.zHex g = boxHex (Dr.loc (Dr.setV g)) (4, 4) := φ_eq_boxHex _
  ext x
  simp only [X3CBoard.freeNbrs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, open_iff V,
    dock3, List.mem_map]
  constructor
  · rintro ⟨hn, hf⟩
    have hadj : Hex.Adj x (Dr.zHex g) := Hex.adj_symm hn
    rcases hf with ⟨e, he, hx⟩ | ⟨g', hg', rfl⟩
    · obtain ⟨-, hes, hxd⟩ := near_z V he hg hx (Or.inr hadj)
      obtain ⟨a, ha, hown⟩ := arm_of_elem V hg hes
      rw [hxd, ← hown, dHex_spec V hg ha]
      obtain ⟨c, hc, hl⟩ := arms_last _ (missing_lt (Dr := Dr) (Dr.setV g)) a ha
      exact ⟨c, hc, by rw [List.getLastD_eq_getLast?, hl]; rfl⟩
    · exfalso
      by_cases hgg : g' = g
      · subst hgg; exact not_adj_self _ hadj
      · have hne : Dr.setV g' ≠ Dr.setV g := fun h => hgg (setV_inj V hg' hg h)
        have := sep_vv (fun h => hne (P_inj V (setV_spec V hg').1 hw h))
        unfold zHex at hadj; rw [adj_linf hadj] at this; norm_num at this
  · rintro ⟨dk, hdk, rfl⟩
    refine ⟨?_, ?_⟩
    · show Hex.Adj (Dr.zHex g) _
      rw [hzb, boxHex_adj]
      revert dk; decide
    · obtain ⟨e, he, -, hx⟩ := dock_free V hg hdk
      exact Or.inl ⟨e, he, hx⟩

omit V in
theorem dock3_card (g : ℕ) : (Dr.dock3 g).toFinset.card = 3 := by
  rw [List.toFinset_card_of_nodup]
  · simp [dock3, docks]
  · unfold dock3
    exact List.Nodup.map (fun _ _ h => boxHex_inj h) (by decide)

omit V in
theorem dock3_nonadj (g : ℕ) : ∀ x ∈ (Dr.dock3 g).toFinset, ∀ y ∈ (Dr.dock3 g).toFinset,
    ¬ Hex.Adj x y := by
  intro x hx y hy
  simp only [dock3, List.mem_toFinset, List.mem_map] at hx hy
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨c', hc', rfl⟩ := hy
  rw [boxHex_adj]
  revert c'; revert c; decide

/-! ## Connectivity -/

omit V in
theorem center_mem {v : ℕ} (hv : v < Dr.nV) (hs : Dr.isSet v = false) :
    φ (Dr.loc v) ∈ Dr.region (Dr.elemOf v) :=
  mem_region.mpr (Or.inl (Or.inl ⟨v, hv, hs, rfl, mem_plus.mpr (Or.inl rfl)⟩))

omit V in
theorem run_mem {v : ℕ} (hv : v < Dr.nV) (hs : Dr.isSet v = false) {d : GP}
    (hd : d ∈ Dr.usedDirs v) {t : ℕ} (ht : t ≤ 4) :
    mv (φ (Dr.loc v)) t d ∈ Dr.region (Dr.elemOf v) :=
  mem_region.mpr (Or.inl (Or.inl ⟨v, hv, hs, rfl, mem_plus.mpr (Or.inr ⟨d, hd, t, by omega, rfl⟩)⟩))

/-- The scaled route of an edge of `e`, up to the target box, lies in `R_e`. -/
theorem route_mem {ε : DEdge} (hε : ε ∈ Dr.edges) {s : ℕ} (hs : s ≤ 20 * ε.k - 5) :
    ε.pt s ∈ Dr.region (Dr.elemOf ε.u) := by
  have hR := V.route ε hε
  have hk := DEdge.k_pos hR
  rcases Nat.lt_or_ge s 5 with h5 | h5
  · rw [DEdge.pt_first hR (by omega), V.rHead ε hε]
    exact run_mem (V.eEnds ε hε).1 (V.eSrc ε hε)
      (mem_usedDirs.mpr ⟨ε, hε, dirAt_u ε⟩) (by omega)
  · exact mem_region.mpr (Or.inr (Or.inl ⟨ε, hε, rfl, DEdge.mem_corr.mpr ⟨s, h5, hs, hk, rfl⟩⟩))

/-- A path edge's whole scaled route lies in `R_e`. -/
theorem route_mem_full {ε : DEdge} (hε : ε ∈ Dr.edges) (hv : Dr.isSet ε.v = false)
    (hve : Dr.elemOf ε.v = Dr.elemOf ε.u) {s : ℕ} (hs : s ≤ 20 * ε.k) :
    ε.pt s ∈ Dr.region (Dr.elemOf ε.u) := by
  have hR := V.route ε hε
  have hk := DEdge.k_pos hR
  rcases Nat.lt_or_ge s (20 * ε.k - 4) with h5 | h5
  · exact route_mem V hε (by omega)
  · rw [DEdge.pt_last hR (by omega) hs, V.rLast ε hε, ← hve]
    exact run_mem (V.eEnds ε hε).2 hv
      (mem_usedDirs.mpr ⟨ε, hε, dirAt_v (u_ne_v V hε)⟩) (by omega)

theorem lnk_route {A : Finset Hex} {ε : DEdge} (hε : ε ∈ Dr.edges) :
    ∀ S : ℕ, S ≤ 20 * ε.k → (∀ s ≤ S, ε.pt s ∈ A) → Lnk A (ε.pt S) (ε.pt 0)
  | 0, _, h => Lnk.refl (h 0 le_rfl)
  | S + 1, hS, h => by
    have ih := lnk_route hε S (by omega) (fun s hs => h s (by omega))
    have ha := DEdge.pt_adj (V.route ε hε) (s := S) (by omega)
    exact (Lnk.step (h _ le_rfl) (h S (by omega)) (Hex.adj_symm ha)).trans ih

/-- Every path vertex of `e` is linked to `v_e^1` inside `R_e` (induction along the path). -/
theorem lnk_root {e : ℕ} (he : e < 3 * P.q) :
    ∀ i v, v < Dr.nV → Dr.K v = .elem e i →
      Lnk (Dr.region e).toFinset (φ (Dr.loc v)) (φ (Dr.loc (Dr.root e)))
  | 0, v, hv, hK => by
    rw [← eq_root V hv hK]
    obtain ⟨hs, rfl⟩ := notSet_of_K hK
    exact Lnk.refl (List.mem_toFinset.mpr (center_mem hv hs))
  | i + 1, v, hv, hK => by
    obtain ⟨ε, hε, hεv, hKu⟩ := V.pathEx v hv e i hK
    obtain ⟨hsu, heu⟩ := notSet_of_K hKu
    obtain ⟨hsv, hev⟩ := notSet_of_K hK
    have ih := lnk_root he i ε.u (V.eEnds ε hε).1 hKu
    have hR := V.route ε hε
    have hw := lnk_route V (A := (Dr.region e).toFinset) hε (20 * ε.k) le_rfl (fun s hs =>
      List.mem_toFinset.mpr (heu ▸ route_mem_full V hε (hεv ▸ hsv) (by rw [hεv, hev, heu]) hs))
    rw [DEdge.pt_end, DEdge.pt_zero, V.rLast ε hε, V.rHead ε hε, hεv] at hw
    exact hw.trans ih

omit V in
theorem lnk_arm {A : Finset Hex} {a : GP} :
    ∀ (L : List (ℕ × ℕ)) (c0 : ℕ × ℕ), ChainAdj (c0 :: L) → (∀ c ∈ c0 :: L, boxHex a c ∈ A) →
      ∀ c ∈ c0 :: L, Lnk A (boxHex a c) (boxHex a c0)
  | [], c0, _, hA, c, hc => by
    simp only [List.mem_singleton] at hc; subst hc; exact Lnk.refl (hA _ (by simp))
  | c1 :: L, c0, hch, hA, c, hc => by
    obtain ⟨hadj, hch'⟩ := hch
    have ih := lnk_arm L c1 hch' (fun c hc => hA c (List.mem_cons_of_mem _ hc))
    have h10 : Lnk A (boxHex a c1) (boxHex a c0) :=
      Lnk.step (hA _ (by simp)) (hA _ (by simp)) (boxHex_adj.mpr (Hex.adj_symm hadj))
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Lnk.refl (hA _ (by simp))
    · exact (ih c hc).trans h10

/-- **(I2), connectivity**: every hex of `R_e` is linked to `v_e^1`'s centre inside `R_e`. -/
theorem lnk_center {e : ℕ} (he : e < 3 * P.q) {h : Hex} (hh : h ∈ Dr.region e) :
    Lnk (Dr.region e).toFinset h (φ (Dr.loc (Dr.root e))) := by
  set A := (Dr.region e).toFinset with hA
  have memA : ∀ {x}, x ∈ Dr.region e → x ∈ A := fun hx => List.mem_toFinset.mpr hx
  -- corridor hexes of an edge of `e`
  have hcor : ∀ ε ∈ Dr.edges, Dr.elemOf ε.u = e → ∀ s ≤ 20 * ε.k - 5,
      Lnk A (ε.pt s) (φ (Dr.loc (Dr.root e))) := by
    intro ε hε heu s hs
    have hw := lnk_route V (A := A) hε s (by omega)
      (fun s' hs' => memA (heu ▸ route_mem V hε (by omega)))
    rw [DEdge.pt_zero, V.rHead ε hε] at hw
    obtain ⟨i, hKi⟩ := isSet_false_iff.mp (V.eSrc ε hε)
    rw [heu] at hKi
    exact hw.trans (lnk_root V he i ε.u (V.eEnds ε hε).1 hKi)
  rcases mem_region.mp hh with (⟨v, hv, hs, rfl, hp⟩ | hst) | ⟨ε, hε, heu, hc⟩ |
      ⟨w, hw, hsw, a, ha, hown, c, hc, rfl⟩
  · obtain ⟨i, hKi⟩ := isSet_false_iff.mp hs
    have hr := lnk_root V he i v hv hKi
    rcases mem_plus.mp hp with rfl | ⟨d, hd, t, ht, rfl⟩
    · exact hr
    · have hu := usedDirs_unit V hd
      exact (lnk_run _ hu t (fun τ hτ => memA (run_mem hv hs hd (by omega)))).trans hr
  · obtain ⟨hr, hK⟩ := root_spec V he
    obtain ⟨hs, he'⟩ := notSet_of_K hK
    have hu := stubDir_unit (Dr := Dr) (Dr.root e)
    have hst' : ∀ τ : ℕ, τ ≤ 2 → mv (φ (Dr.loc (Dr.root e))) τ (Dr.stubDir (Dr.root e)) ∈ A := by
      intro τ hτ
      apply memA
      interval_cases τ
      · have := center_mem hr hs
        rw [he'] at this
        rw [Nat.cast_zero, mv_zero]; exact this
      · exact mem_region.mpr (Or.inl (Or.inr (by simp [stub])))
      · exact mem_region.mpr (Or.inl (Or.inr (by simp [stub, pHex])))
    simp only [stub, pHex, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl
    · exact lnk_run _ hu 1 (fun τ hτ => hst' τ (by omega))
    · exact lnk_run _ hu 2 hst'
  · obtain ⟨s, hs1, hs2, -, rfl⟩ := DEdge.mem_corr.mp hc
    exact hcor ε hε heu s hs2
  · obtain ⟨g, hKg⟩ := isSet_iff.mp hsw
    have hg := V.kindSet w hw g hKg
    have hwg := eq_setV V hw hKg
    subst hwg
    obtain ⟨ε, hε, hd⟩ := arm_edge V hg ha
    obtain ⟨hv, hdv, -⟩ := edge_at_set V hg hε hd
    have heu : Dr.elemOf ε.u = e := by rw [← armOwner_eq V hε hd, hown]
    have hR := V.route ε hε
    have hk := DEdge.k_pos hR
    obtain ⟨hp4, -⟩ := arm_port ha
    -- the arm, back to its port cell
    obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp (arms_head _ (missing_lt _) a ha)
    have hchain := arms_chain _ (missing_lt (Dr := Dr) (Dr.setV g)) a ha
    rw [hrest] at hchain
    have harmA : ∀ c ∈ portCell a.1 :: rest, boxHex (Dr.loc (Dr.setV g)) c ∈ A := by
      intro c hc'
      rw [← hrest] at hc'
      exact memA (mem_region.mpr (Or.inr (Or.inr ⟨_, hw, hsw, a, ha, hown, c, hc', rfl⟩)))
    have h1 := lnk_arm rest (portCell a.1) hchain harmA c (by rw [← hrest]; exact hc)
    -- the port cell is next to the corridor hex at parameter `20k − 5`
    have hport : boxHex (Dr.loc (Dr.setV g)) (portCell a.1) =
        mv (φ (Dr.loc (Dr.setV g))) 4 (dirV a.1) := by
      obtain ⟨e1, e2⟩ := portCell_eq a.1 hp4
      ext
      · rw [boxHex_x, e1]; simp; ring
      · rw [boxHex_y, e2]; simp; ring
    have hcp : ε.pt (20 * ε.k - 5) = mv (φ (Dr.loc (Dr.setV g))) 5 (dirV a.1) := by
      rw [DEdge.pt_last hR (by omega) (by omega), V.rLast ε hε, hv, ← hdv]
      congr 1; omega
    have hpA : ε.pt (20 * ε.k - 5) ∈ A := memA (heu ▸ route_mem V hε le_rfl)
    have hadj : Hex.Adj (boxHex (Dr.loc (Dr.setV g)) (portCell a.1)) (ε.pt (20 * ε.k - 5)) := by
      rw [hport, hcp]
      have := adj_mv_succ (φ (Dr.loc (Dr.setV g))) 4 (isUnit_dirV a.1)
      norm_num at this; exact this
    have h2 := Lnk.step (harmA _ (by simp)) hpA hadj
    exact h1.trans (h2.trans (hcor ε hε heu _ le_rfl))

end Prox

end OrthoDrawing

theorem φ_inj {a b : GP} (h : φ a = φ b) : a = b := by
  have hx := congrArg Hex.x h
  have hy := congrArg Hex.y h
  simp only [φ_x, φ_y] at hx hy
  ext <;> omega

open OrthoDrawing in
/-- **Lemma D.4 (Embedding), steps 4–6, for every valid drawing**: the board built from a valid
orthogonal drawing of `G'` satisfies all of (I1)–(I4). -/
theorem lemmaD4 {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) : (build P Dr).Inv P where
  zOpen g hg := (open_iff V).mpr (Or.inr ⟨g, hg, rfl⟩)
  zInj g hg g' hg' h := setV_inj V hg hg'
    (P_inj V (setV_spec V hg).1 (setV_spec V hg').1 (φ_inj h))
  i1card g hg := by
    show ((build P Dr).freeNbrs (Dr.zHex g)).card = 3
    rw [freeNbrs_z V hg]; exact dock3_card g
  i1nonadj g hg := by
    show ∀ x ∈ (build P Dr).freeNbrs (Dr.zHex g), ∀ y ∈ (build P Dr).freeNbrs (Dr.zHex g), _
    rw [freeNbrs_z V hg]; exact dock3_nonadj g
  rOpen e he h hh := by
    have hh' : h ∈ Dr.region e := List.mem_toFinset.mp hh
    exact ⟨(open_iff V).mpr (Or.inl ⟨e, he, hh'⟩),
      fun g hg heq => (near_z V he hg hh' (Or.inl heq)).1 heq⟩
  rCover h ho hz := by
    rcases (open_iff V).mp ho with ⟨e, he, hh⟩ | ⟨g, hg, rfl⟩
    · exact ⟨e, he, List.mem_toFinset.mpr hh⟩
    · exact absurd rfl (hz g hg)
  rDisj e he e' he' hne := by
    rw [Finset.disjoint_left]
    intro h hh hh'
    exact hne (prox V he he' (List.mem_toFinset.mp hh) (List.mem_toFinset.mp hh') (Or.inl rfl))
  rClosed e he h hh h' hadj ho hz := by
    rcases (open_iff V).mp ho with ⟨e', he', hh'⟩ | ⟨g, hg, rfl⟩
    · have := prox V he he' (List.mem_toFinset.mp hh) hh' (Or.inr hadj)
      subst this; exact List.mem_toFinset.mpr hh'
    · exact absurd rfl (hz g hg)
  rConn e he h hh := by
    have hp : Dr.pHex e ∈ Dr.region e :=
      mem_region.mpr (Or.inl (Or.inr (by simp [stub])))
    exact ((lnk_center V he hp).trans (lnk_center V he (List.mem_toFinset.mp hh)).symm).2.2
  pMem e he := by
    show Dr.pHex e ∈ (Dr.region e).toFinset
    exact List.mem_toFinset.mpr (mem_region.mpr (Or.inl (Or.inr (by simp [stub]))))
  dMem g hg e he := by
    obtain ⟨a, ha, rfl⟩ := arm_of_elem V hg he
    show Dr.dHex g _ ∈ (Dr.region _).toFinset
    rw [dHex_spec V hg ha, List.mem_toFinset, mem_region]
    obtain ⟨c, -, hl⟩ := arms_last _ (missing_lt (Dr := Dr) (Dr.setV g)) a ha
    refine Or.inr (Or.inr ⟨Dr.setV g, (setV_spec V hg).1, isSet_of_K (setV_spec V hg).2, a, ha, rfl,
      c, List.mem_of_getLast? hl, ?_⟩)
    rw [List.getLastD_eq_getLast?, hl]; rfl
  dAdj g hg e he := by
    obtain ⟨a, ha, rfl⟩ := arm_of_elem V hg he
    show Hex.Adj (Dr.dHex g _) (Dr.zHex g)
    rw [dHex_spec V hg ha, zHex, φ_eq_boxHex, boxHex_adj]
    obtain ⟨c, hc, hl⟩ := arms_last _ (missing_lt (Dr := Dr) (Dr.setV g)) a ha
    rw [List.getLastD_eq_getLast?, hl, Option.getD_some]
    have key : ∀ c ∈ docks, Hex.Adj (cell c) (cell (4, 4)) := by decide
    exact key c hc
  dAlone g hg e he g' hg' hadj := by
    by_contra hne
    obtain ⟨a, ha, rfl⟩ := arm_of_elem V hg he
    change Hex.Adj (Dr.dHex g _) (Dr.zHex g') at hadj
    rw [dHex_spec V hg ha] at hadj
    obtain ⟨c, -, hl⟩ := arms_last _ (missing_lt (Dr := Dr) (Dr.setV g)) a ha
    have hb := arm_near ha (List.mem_of_getLast? hl)
    rw [← Option.getD_some (a := c) (b := (0, 0)), ← hl, ← List.getLastD_eq_getLast?] at hb
    have hne' : Dr.setV g ≠ Dr.setV g' := fun h => hne (setV_inj V hg hg' h).symm
    have := box_box V (setV_spec V hg).1 (setV_spec V hg').1 hne' hb
      (by rw [zHex, linf_self]; norm_num : linf (Dr.zHex g') (φ (Dr.loc (Dr.setV g'))) ≤ 4)
    rw [adj_linf hadj] at this; norm_num at this
  rDock e he h hh g hg hadj := by
    obtain ⟨-, h1, h2⟩ := near_z V he hg (List.mem_toFinset.mp hh) (Or.inr hadj)
    exact ⟨h1, h2⟩
  i4 e he := by
    show (Dr.region e).toFinset.card ≤ Dr.width * Dr.height
    calc (Dr.region e).toFinset.card ≤ (rectF Dr.width Dr.height).card := by
          apply Finset.card_le_card
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := region_in V he (List.mem_toFinset.mp hh)
          exact mem_rectF.mpr ⟨h1, h2, h3, h4⟩
      _ ≤ ((Finset.range Dr.width) ×ˢ (Finset.range Dr.height)).card := Finset.card_image_le
      _ = Dr.width * Dr.height := by simp

/-- **Theorem 3 with the drawing on the input**: for a valid drawing, the instance built by steps
4–6 is a yes-instance of `ARMY-ALLOCATION` exactly when `P` has an exact cover (any `hp(P) ≥ 1`,
`def(Q) ≥ 2`). -/
theorem theorem3_drawing' {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) :
    P.ExactCover ↔ ArmyAllocation (G3 hpP defQ P (build P Dr)) :=
  theorem3 P _ V.wf (lemmaD4 V) hhp hdef

/-- **Theorem 3 with the drawing on the input**, at the paper's constants. -/
theorem theorem3_drawing {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) :
    P.ExactCover ↔ ArmyAllocation (G3pub P (build P Dr)) :=
  theorem3_pub P _ V.wf (lemmaD4 V)

/-- **Corollary 3.1 with the drawing on the input.** -/
theorem cor31_drawing {P : X3C} {Dr : OrthoDrawing} (V : Dr.Valid P) :
    P.ExactCover ↔ ThmF.BattlePlay (G3pub P (build P Dr)) T3.α1 :=
  cor31 P _ V.wf (lemmaD4 V) (by norm_num) (by norm_num)

/-- **Polynomial size**: the board is `(20 gw − 7) × (20 gh − 7)` for a drawing in the grid box
`gw × gh`, and the speed `σ` (the only unary number that grows with the board) is its hex count. -/
theorem build_size (P : X3C) (Dr : OrthoDrawing) :
    (build P Dr).width = 20 * Dr.gw - 7 ∧ (build P Dr).height = 20 * Dr.gh - 7 ∧
    (build P Dr).σ = (build P Dr).width * (build P Dr).height ∧
    (build P Dr).σ ≤ 400 * (Dr.gw * Dr.gh) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show (20 * Dr.gw - 7) * (20 * Dr.gh - 7) ≤ 400 * (Dr.gw * Dr.gh)
  calc (20 * Dr.gw - 7) * (20 * Dr.gh - 7) ≤ (20 * Dr.gw) * (20 * Dr.gh) :=
        Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    _ = 400 * (Dr.gw * Dr.gh) := by ring

end Embed

end Homm3
