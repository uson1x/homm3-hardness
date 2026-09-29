import Homm3.EmbedCheck

/-!
# Session 5, target 6 (stretch). Step 1 of Lemma D.4: the degree reduction, combinatorially

Paper: D.4 step 1 (`main.md:1446–1469`).  Element `e` of degree `d_e` becomes a path
`v_e^1 — ⋯ — v_e^{d_e}`; the `i`-th incidence edge of `e` in the rotation's order, cut at some
point, goes to `v_e^i`.  The embedding half of the claim (planarity is preserved) is not
formalized; the combinatorial half is:

* `vkinds P ord`, `pairs P ord`: the vertices and edges of `G'` for a cut rotation `ord e` (the
  members containing `e`, in order), in the order `embed_lemma.build_board_lemma` builds them;
* **`card_V`**: `|V(G')| = 4|C|`; **`card_E`**: `|E(G')| = 6|C| − |X|` when every element lies in
  some member (step 0 has sent the rest to `G_no`);
* `IsStep1 P Dr ord`: the drawing's vertex kinds and edge ends are exactly step 1's; checked in
  the kernel on the 44 corpus drawings (`CrossCheckDrawing.lean`, `s1NN`), with `ord` read off
  the drawing (`ordOf`).
-/

namespace Homm3

namespace Embed

namespace Step1

variable (P : X3C) (ord : ℕ → List ℕ)

/-- The vertex kinds of `G'`: the set vertices, then the path vertices element by element. -/
def vkinds : List VK :=
  (List.range P.n).map VK.set ++
    (List.range (3 * P.q)).flatMap (fun e => (List.range (ord e).length).map (VK.elem e))

/-- The index of a vertex kind. -/
def vidx (k : VK) : ℕ := (vkinds P ord).idxOf k

/-- The edges of `G'` (source first): for each element, its incidence edges in order, then its
path edges. -/
def pairs : List (ℕ × ℕ) :=
  (List.range (3 * P.q)).flatMap (fun e =>
    (List.range (ord e).length).map (fun i =>
      (vidx P ord (.elem e i), vidx P ord (.set ((ord e).getD i 0)))) ++
    (List.range ((ord e).length - 1)).map (fun i =>
      (vidx P ord (.elem e i), vidx P ord (.elem e (i + 1)))))

/-- `ord e` lists the members containing `e`, each once. -/
structure OrdOK : Prop where
  nodup : ∀ e < 3 * P.q, (ord e).Nodup
  mem : ∀ e < 3 * P.q, ∀ g, g ∈ ord e ↔ g < P.n ∧ e ∈ P.set g

theorem lsum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, lsum_range f n,
      Finset.sum_range_succ]; simp

variable {P ord}

/-- The degrees of the elements add up to `3|C|` (double counting). -/
theorem sum_deg (hP : P.WF) (ho : OrdOK P ord) :
    ∑ e ∈ Finset.range (3 * P.q), (ord e).length = 3 * P.n := by
  have h1 : ∀ e ∈ Finset.range (3 * P.q), (ord e).length =
      ∑ g ∈ Finset.range P.n, if e ∈ P.set g then 1 else 0 := by
    intro e he
    rw [Finset.mem_range] at he
    rw [← List.toFinset_card_of_nodup (ho.nodup e he), ← Finset.card_filter]
    congr 1
    ext g
    simp [ho.mem e he]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ g ∈ Finset.range P.n, (∑ e ∈ Finset.range (3 * P.q), if e ∈ P.set g then 1 else 0) = 3 := by
    intro g hg
    rw [Finset.mem_range] at hg
    rw [← Finset.card_filter]
    refine Eq.trans ?_ (hP.card g hg)
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    exact hP.sub g hg e
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- **`|V(G')| = 4|C|`.** -/
theorem card_V (hP : P.WF) (ho : OrdOK P ord) : (vkinds P ord).length = 4 * P.n := by
  rw [vkinds, List.length_append, List.length_map, List.length_range, List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [lsum_range (fun e => (ord e).length), sum_deg hP ho]; ring

/-- **`|E(G')| = 6|C| − |X|`** when every element lies in a member. -/
theorem card_E (hP : P.WF) (ho : OrdOK P ord) (hcov : ∀ e < 3 * P.q, ∃ g < P.n, e ∈ P.set g) :
    (pairs P ord).length + 3 * P.q = 6 * P.n := by
  rw [pairs, List.length_flatMap]
  simp only [List.length_append, List.length_map, List.length_range]
  rw [lsum_range (fun e => (ord e).length + ((ord e).length - 1))]
  have hpos : ∀ e ∈ Finset.range (3 * P.q), (ord e).length + ((ord e).length - 1) + 1 =
      2 * (ord e).length := by
    intro e he
    rw [Finset.mem_range] at he
    obtain ⟨g, hg, heg⟩ := hcov e he
    have : g ∈ ord e := (ho.mem e he g).mpr ⟨hg, heg⟩
    have := List.length_pos_of_mem this
    omega
  have := Finset.sum_congr rfl hpos
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_deg hP ho] at this
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at this
  omega

/-- The drawing's `G'` is step 1's for the cut rotation `ord`. -/
def IsStep1 (P : X3C) (Dr : OrthoDrawing) (ord : ℕ → List ℕ) : Prop :=
  OrdOK P ord ∧ Dr.kind = vkinds P ord ∧ Dr.edges.map (fun ε => (ε.u, ε.v)) = pairs P ord

/-- The cut rotation read off a drawing: the member at the incidence edge of `v_e^{i+1}`, for
`i = 0, 1, …`. -/
def ordOf (Dr : OrthoDrawing) (e : ℕ) : List ℕ :=
  (List.range Dr.edges.length).filterMap (fun i => Dr.edges.findSome? (fun ε =>
    match Dr.K ε.u, Dr.K ε.v with
    | .elem e' i', .set g => if e' = e ∧ i' = i then some g else none
    | _, _ => none))

/-- A Bool form of `OrdOK` for concrete instances. -/
def ordOKB (q : ℕ) (CL : List (List ℕ)) (ord : ℕ → List ℕ) : Bool :=
  (List.range (3 * q)).all (fun e => decide (ord e).Nodup &&
    (ord e).all (fun g => decide (g < CL.length) && (CL.getD g []).contains e) &&
    (List.range CL.length).all (fun g => !(CL.getD g []).contains e || (ord e).contains g))

theorem ordOK_of {q : ℕ} {CL : List (List ℕ)} {ord : ℕ → List ℕ} (h : ordOKB q CL ord = true) :
    OrdOK (BoardData.toX3C q CL) ord := by
  simp only [ordOKB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
  have hn : (BoardData.toX3C q CL).n = CL.length := BoardData.toX3C_n q CL
  refine ⟨fun e he => (h e he).1.1, fun e he g => ?_⟩
  rw [hn]
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := (h e he).1.2 g hg
    exact ⟨h1, by rw [BoardData.toX3C_set h1, List.mem_toFinset]; exact h2⟩
  · rintro ⟨hg, hm⟩
    rw [BoardData.toX3C_set hg, List.mem_toFinset] at hm
    rcases (h e he).2 g hg with h1 | h1
    · exact absurd (List.contains_iff_mem.mpr hm) (by rw [h1]; decide)
    · exact h1

end Step1

end Embed

end Homm3
