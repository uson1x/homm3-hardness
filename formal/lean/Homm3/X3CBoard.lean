import Homm3.X3C
import Homm3.Walk

/-!
# Session 4, targets 1–2. The board over an `X3C` instance, (I1)–(I4), `G_3`, Lemma D.1

Paper: §3.3 ("*The board.* Four invariants carry the whole correctness argument, and nothing
below refers to the layout"), Appendix D.1 (the instance), D.2 (Lemma D.1).

**Design: Theorem 3 modulo the embedding.**  `X3CBoard` is an abstract board — dimensions,
impassable hexes, deployment hexes `p e`, enemy hexes `z g`, dockings `d g e`, regions `R e`,
player speed `σ` — and `B.Inv P` states (I1)–(I4) as hypotheses.  Every correctness
statement below is proved for **every** board satisfying them.  Lemma D.4 (that such a board
exists, is polynomial and is computable for every planar instance) stays a hand proof, as in
the paper (§1.2 item 7, D.6); the boards the artifact actually builds are checked against
`Inv` in the kernel (`BoardCheck.lean`, `CrossCheckX3C*.lean`, `CrossCheckLemma*.lean`).

* (I1) `i1card`, `i1nonadj`: every `z g` has exactly three free neighbours, pairwise
  non-adjacent.
* (I2) `rOpen`, `rCover`, `rDisj`, `rClosed`, `rConn`: the free non-enemy hexes fall into the
  `3q` regions `R e`; each is closed under adjacency among free non-enemy hexes and connected
  from `p e` — i.e. exactly the connected components.
* (I3) `pMem`, `dMem`, `dAdj`, `dAlone`, `rDock`: `R e` holds `p e` and exactly the dockings
  `d g e` for `e ∈ S_g` as its hexes adjacent to an enemy, each adjacent to `z g` alone.
* (I4) `i4`: `σ ≥ |R e|`.

`G3 hpP defQ P B` is `G_3(X, C)` with the player's hit points and the enemy's defence as
parameters: the paper's constants are `G3 4 27` (`G3pub`), the historical constants of
`verify_x3c.py` are `hp 5`, `def 41`.

* `mem_reach_of_rtg` — a walk inside a finite set `A` of hexes free for the mover, from its
  hex, ends in the BFS reach within `|A|` layers (BFS stabilization); `reach_sub_of_closed` —
  the reach stays inside a set closed under free steps.
* **Lemma D.1** (`lemmaD1`): while every `E_S` with `S ∋ e` is alive and `R_e` holds no other
  living stack, slot `e`'s stack strikes exactly the `E_S` with `S ∋ e`, and only from
  `d_S^e`.  Its confinement half (`reach_sub_region`) needs neither the "alone" hypothesis
  nor (I4).
-/

namespace Homm3

open Function

/-! ## BFS reach: closure and walks -/

section ReachWalk

variable {f : Hex → Prop} [DecidablePred f]

theorem reach_mono_pred {g : Hex → Prop} [DecidablePred g] (hfg : ∀ h, f h → g h) (p : Hex) :
    ∀ t, reach f p t ⊆ reach g p t
  | 0 => le_rfl
  | t + 1 => by
    intro q hq
    simp only [reach, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq] at hq ⊢
    rcases hq with hq | ⟨h, hh, hadj, hf⟩
    · exact Or.inl (reach_mono_pred hfg p t hq)
    · exact Or.inr ⟨h, reach_mono_pred hfg p t hh, hadj, hfg _ hf⟩

/-- The reach stays inside a set containing the start and closed under free steps. -/
theorem reach_sub_of_closed {A : Finset Hex} {p : Hex} (hp : p ∈ A)
    (hcl : ∀ h ∈ A, ∀ h', Hex.Adj h h' → f h' → h' ∈ A) : ∀ t, reach f p t ⊆ A
  | 0 => by intro q hq; simp only [reach, Finset.mem_singleton] at hq; subst hq; exact hp
  | t + 1 => by
    intro q hq
    simp only [reach, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq] at hq
    rcases hq with hq | ⟨h, hh, hadj, hf⟩
    · exact reach_sub_of_closed hp hcl t hq
    · exact hcl h (reach_sub_of_closed hp hcl t hh) q hadj hf

theorem reach_succ_eq (p : Hex) (t : ℕ) : reach f p (t + 1) =
    reach f p t ∪ (reach f p t).biUnion (fun h => (h.nbrs.filter (fun q => decide (f q))).toFinset) :=
  rfl

/-- Once a BFS layer repeats, the reach is stable. -/
theorem reach_stable {p : Hex} {u : ℕ} (hu : reach f p (u + 1) = reach f p u) :
    ∀ v, reach f p (u + v) = reach f p u
  | 0 => rfl
  | v + 1 => by
    have ih := reach_stable hu v
    rw [show u + (v + 1) = (u + v) + 1 by omega, reach_succ_eq, ih, ← reach_succ_eq, hu]

/-- Either some layer `≤ t` repeats, or layer `t` has at least `t + 1` hexes. -/
theorem reach_grow (p : Hex) :
    ∀ t, (∃ u ≤ t, reach f p (u + 1) = reach f p u) ∨ t + 1 ≤ (reach f p t).card
  | 0 => Or.inr (by simp [reach])
  | t + 1 => by
    rcases reach_grow p t with ⟨u, hu, he⟩ | hc
    · exact Or.inl ⟨u, by omega, he⟩
    · by_cases he : reach f p (t + 1) = reach f p t
      · exact Or.inl ⟨t, by omega, he⟩
      · right
        have hsub : reach f p t ⊂ reach f p (t + 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨reach_mono p (Nat.le_succ t), fun h => he h.symm⟩
        have := Finset.card_lt_card hsub
        omega

theorem closed_of_stable {p : Hex} {u : ℕ} (hu : reach f p (u + 1) = reach f p u) {h h' : Hex}
    (hh : h ∈ reach f p u) (hadj : Hex.Adj h h') (hf : f h') : h' ∈ reach f p u :=
  hu ▸ reach_succ hh hadj hf

/-- **A walk inside `A` ends in the BFS reach within `|A|` layers**, when every hex of `A` is
free for the mover. -/
theorem mem_reach_of_rtg {A : Finset Hex} {p h : Hex} (hp : p ∈ A)
    (hw : Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ A) p h)
    (hA : ∀ x ∈ A, f x) {s : ℕ} (hs : A.card ≤ s) : h ∈ reach f p s := by
  have hsubA : ∀ t, reach (· ∈ A) p t ⊆ A :=
    reach_sub_of_closed hp (fun _ _ _ _ hh' => hh')
  obtain ⟨u, hu, he⟩ : ∃ u ≤ A.card, reach (· ∈ A) p (u + 1) = reach (· ∈ A) p u := by
    rcases reach_grow (f := (· ∈ A)) p A.card with h | h
    · exact h
    · exact absurd (Finset.card_le_card (hsubA A.card)) (by omega)
  have hmem : h ∈ reach (· ∈ A) p u := by
    induction hw with
    | refl => exact start_mem_reach p u
    | tail _ hab ih => exact closed_of_stable he ih hab.1 hab.2
  exact reach_mono_pred hA p s (reach_mono p (by omega : u ≤ s) hmem)

/-- Walks inside `A` reverse (adjacency is symmetric). -/
theorem rtg_symm_in {A : Finset Hex} {x y : Hex} (hx : x ∈ A)
    (hw : Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ A) x y) :
    Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ A) y x := by
  induction hw with
  | refl => exact .refl
  | @tail b c hxb hbc ih =>
    have hb : b ∈ A := by
      rcases Relation.ReflTransGen.cases_tail hxb with h | ⟨_, _, h⟩
      · exact h ▸ hx
      · exact h.2
    exact Relation.ReflTransGen.head ⟨Hex.adj_symm hbc.1, hb⟩ ih

end ReachWalk

/-! ## The board -/

/-- A board over an `X3C` instance (Appendix D.1): dimensions, impassable hexes, deployment
hexes `p e`, enemy hexes `z g`, dockings `d g e`, regions `R e`, player speed `σ`. -/
structure X3CBoard where
  width : ℕ
  height : ℕ
  obst : Finset Hex
  p : ℕ → Hex
  z : ℕ → Hex
  d : ℕ → ℕ → Hex
  R : ℕ → Finset Hex
  σ : ℕ

namespace X3CBoard

variable (B : X3CBoard)

/-- A free (passable) hex: on the board and not impassable. -/
def Open (h : Hex) : Prop :=
  0 ≤ h.x ∧ h.x < B.width ∧ 0 ≤ h.y ∧ h.y < B.height ∧ h ∉ B.obst

instance : DecidablePred B.Open := fun h => by unfold Open; infer_instance

/-- The free neighbours of a hex. -/
def freeNbrs (h : Hex) : Finset Hex := (h.nbrs.filter (fun x => decide (B.Open x))).toFinset

/-- **The invariants (I1)–(I4)** of §3.3, for the instance `P`. -/
structure Inv (P : X3C) : Prop where
  zOpen : ∀ g < P.n, B.Open (B.z g)
  zInj : ∀ g < P.n, ∀ g' < P.n, B.z g = B.z g' → g = g'
  /-- (I1) exactly three free neighbours ... -/
  i1card : ∀ g < P.n, (B.freeNbrs (B.z g)).card = 3
  /-- (I1) ... pairwise non-adjacent. -/
  i1nonadj : ∀ g < P.n, ∀ x ∈ B.freeNbrs (B.z g), ∀ y ∈ B.freeNbrs (B.z g), ¬ Hex.Adj x y
  /-- (I2) regions consist of free non-enemy hexes ... -/
  rOpen : ∀ e < 3 * P.q, ∀ h ∈ B.R e, B.Open h ∧ ∀ g < P.n, h ≠ B.z g
  /-- (I2) ... cover them ... -/
  rCover : ∀ h, B.Open h → (∀ g < P.n, h ≠ B.z g) → ∃ e < 3 * P.q, h ∈ B.R e
  /-- (I2) ... one per element ... -/
  rDisj : ∀ e < 3 * P.q, ∀ e' < 3 * P.q, e ≠ e' → Disjoint (B.R e) (B.R e')
  /-- (I2) ... and are the connected components: closed ... -/
  rClosed : ∀ e < 3 * P.q, ∀ h ∈ B.R e, ∀ h', Hex.Adj h h' → B.Open h' →
    (∀ g < P.n, h' ≠ B.z g) → h' ∈ B.R e
  /-- (I2) ... and connected. -/
  rConn : ∀ e < 3 * P.q, ∀ h ∈ B.R e,
    Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ B.R e) (B.p e) h
  /-- (I3) `R_e` holds `p_e` ... -/
  pMem : ∀ e < 3 * P.q, B.p e ∈ B.R e
  /-- (I3) ... and the dockings `d_S^e`, `S ∋ e` ... -/
  dMem : ∀ g < P.n, ∀ e ∈ P.set g, B.d g e ∈ B.R e
  dAdj : ∀ g < P.n, ∀ e ∈ P.set g, Hex.Adj (B.d g e) (B.z g)
  /-- (I3) ... each adjacent to `z_S` alone ... -/
  dAlone : ∀ g < P.n, ∀ e ∈ P.set g, ∀ g' < P.n, Hex.Adj (B.d g e) (B.z g') → g' = g
  /-- (I3) ... and these are exactly its hexes adjacent to an enemy. -/
  rDock : ∀ e < 3 * P.q, ∀ h ∈ B.R e, ∀ g < P.n, Hex.Adj h (B.z g) →
    e ∈ P.set g ∧ h = B.d g e
  /-- (I4) -/
  i4 : ∀ e < 3 * P.q, (B.R e).card ≤ B.σ

/-- **The part of (I1)–(I4) the correctness proof consumes.**  (I1) (both clauses), the
"adjacent to `z_S` alone" clause of (I3) (`dAlone`), the covering clause of (I2) (`rCover`) and
the facts about the enemy hexes themselves (`zOpen`, `zInj`) are not used: Theorem 3 holds for
every board satisfying `InvCore` (`theorem3_core`). -/
structure InvCore (P : X3C) : Prop where
  rOpen : ∀ e < 3 * P.q, ∀ h ∈ B.R e, B.Open h ∧ ∀ g < P.n, h ≠ B.z g
  rDisj : ∀ e < 3 * P.q, ∀ e' < 3 * P.q, e ≠ e' → Disjoint (B.R e) (B.R e')
  rClosed : ∀ e < 3 * P.q, ∀ h ∈ B.R e, ∀ h', Hex.Adj h h' → B.Open h' →
    (∀ g < P.n, h' ≠ B.z g) → h' ∈ B.R e
  rConn : ∀ e < 3 * P.q, ∀ h ∈ B.R e,
    Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ B.R e) (B.p e) h
  pMem : ∀ e < 3 * P.q, B.p e ∈ B.R e
  dMem : ∀ g < P.n, ∀ e ∈ P.set g, B.d g e ∈ B.R e
  dAdj : ∀ g < P.n, ∀ e ∈ P.set g, Hex.Adj (B.d g e) (B.z g)
  rDock : ∀ e < 3 * P.q, ∀ h ∈ B.R e, ∀ g < P.n, Hex.Adj h (B.z g) →
    e ∈ P.set g ∧ h = B.d g e
  i4 : ∀ e < 3 * P.q, (B.R e).card ≤ B.σ

variable {B} in
theorem Inv.core {P : X3C} (h : B.Inv P) : B.InvCore P :=
  ⟨h.rOpen, h.rDisj, h.rClosed, h.rConn, h.pMem, h.dMem, h.dAdj, h.rDock, h.i4⟩

end X3CBoard

/-! ## The instance `G_3(X, C)` -/

/-- Player type `P`: `att 1`, `def 1`, flat damage `1`, `hp`, speed `σ`, value `0`. -/
def ptype (hpP σ : ℕ) : CType := ⟨1, 1, 1, hpP, σ, 0⟩
/-- Enemy type `Q`: `att 1`, `def`, flat damage `1`, `hp 3`, speed `1`, value `1`. -/
def qtype (defQ : ℕ) : CType := ⟨1, defQ, 1, 3, 1, 1⟩

/-- **`G_3(X, C)`** (Appendix D.1) on the board `B`, with player `hp` and enemy `def` as
parameters: stock `3q` of `P`, slots `p_e` (`e < 3q`), one creature of `Q` on each `z_g`,
`R = 1`, `W = q`. -/
def G3 (hpP defQ : ℕ) (P : X3C) (B : X3CBoard) : Instance where
  width := B.width
  height := B.height
  obstacles := B.obst
  slots := (List.range (3 * P.q)).map B.p
  army := [(ptype hpP B.σ, 3 * P.q)]
  enemies := (List.range P.n).map (fun g => ⟨qtype defQ, 1, B.z g⟩)
  R := 1
  W := P.q

/-- The paper's constants: `hp(P) = 4`, `def(Q) = 27`. -/
abbrev G3pub (P : X3C) (B : X3CBoard) : Instance := G3 4 27 P B

namespace G3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

@[simp] theorem k_eq : (G3 hpP defQ P B).k = 3 * P.q := by simp [G3, Instance.k]
@[simp] theorem n_eq : (G3 hpP defQ P B).n = P.n := by simp [G3, Instance.n, X3C.n]
@[simp] theorem N_eq : (G3 hpP defQ P B).N = 3 * P.q + P.n := by
  simp [Instance.N]
@[simp] theorem R_eq : (G3 hpP defQ P B).R = 1 := rfl
@[simp] theorem W_eq : (G3 hpP defQ P B).W = P.q := rfl
@[simp] theorem army_len : (G3 hpP defQ P B).army.length = 1 := rfl

theorem slotHex_eq {j : ℕ} (hj : j < 3 * P.q) : (G3 hpP defQ P B).slotHex j = B.p j := by
  simp [Instance.slotHex, G3, hj]

theorem enemy_eq {g : ℕ} (hg : g < P.n) :
    (G3 hpP defQ P B).enemy g = ⟨qtype defQ, 1, B.z g⟩ := by
  simp [Instance.enemy, G3, X3C.n] at hg ⊢
  simp [hg]

/-- A feasible allocation names type `0` in every occupied slot. -/
theorem type_zero {α : ℕ → SlotAlloc} (hα : Feasible (G3 hpP defQ P B) α) {j : ℕ}
    (hj : j < 3 * P.q) (hc : 0 < (α j).count) : (α j).type = 0 := by
  have := hα.1 j (by simpa using hj) hc
  simpa using this

theorem slotType_eq {α : ℕ → SlotAlloc} (hα : Feasible (G3 hpP defQ P B) α) {j : ℕ}
    (hj : j < 3 * P.q) (hc : 0 < (α j).count) :
    (G3 hpP defQ P B).slotType α j = ptype hpP B.σ := by
  simp [Instance.slotType, hc, type_zero hα hj hc, G3]

/-- Feasibility: the slots hold at most `3q` creatures. -/
theorem sum_count_le {α : ℕ → SlotAlloc} (hα : Feasible (G3 hpP defQ P B) α) :
    ∑ j ∈ Finset.range (3 * P.q), (α j).count ≤ 3 * P.q := by
  have h := hα.2 0 (by simp)
  rw [Finset.sum_filter_of_ne] at h
  · rw [k_eq] at h; simpa [G3] using h
  · intro j hj hne
    exact type_zero hα (by simpa using Finset.mem_range.mp hj) (Nat.pos_of_ne_zero hne)

theorem init_player {α : ℕ → SlotAlloc} (hα : Feasible (G3 hpP defQ P B) α) {j : ℕ}
    (hj : j < 3 * P.q) (hc : 0 < (α j).count) :
    initUnits (G3 hpP defQ P B) α j =
      ⟨.player, j, ptype hpP B.σ, B.p j, (α j).count * hpP, (α j).count, 1, false⟩ := by
  rw [initUnits_player (by simpa using hj), slotType_eq hα hj hc, slotHex_eq hj]
  rfl

theorem init_enemy {α : ℕ → SlotAlloc} {g : ℕ} (hg : g < P.n) :
    initUnits (G3 hpP defQ P B) α (3 * P.q + g) =
      ⟨.enemy, g, qtype defQ, B.z g, 3, 1, 1, false⟩ := by
  have := initUnits_enemy (I := G3 hpP defQ P B) (α := α) (j := g) (by simpa using hg)
  rw [k_eq, enemy_eq hg] at this
  rw [this]; simp [qtype]

/-- `free` on `G_3` is "free on the board and not occupied by another living stack". -/
theorem free_iff {us : ℕ → Stack} {i : ℕ} {h : Hex} :
    free (G3 hpP defQ P B) us i h ↔ B.Open h ∧
      ∀ i' < 3 * P.q + P.n, i' ≠ i → (us i').alive → (us i').hex ≠ h := by
  simp only [free, Instance.inBounds, X3CBoard.Open, N_eq]
  simp only [G3]
  tauto

/-- A stack alive in a reachable position that is a player slot holds `P` and `c ≥ 1`. -/
theorem player_of_alive {α : ℕ → SlotAlloc} (hα : Feasible (G3 hpP defQ P B) α) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) {j : ℕ} (hj : j < 3 * P.q) (ha : (s.units j).alive) :
    0 < (α j).count ∧ (s.units j).type = ptype hpP B.σ := by
  have hf := Reach.frame hs
  have hpl := hf.pool j
  have hc : 0 < (α j).count := by
    by_contra h0
    have h0 : (α j).count = 0 := by omega
    rw [initUnits_player (by simpa using hj), h0] at hpl
    unfold Stack.alive at ha; simp at hpl; omega
  exact ⟨hc, by rw [hf.type, init_player hα hj hc]⟩

/-- Enemies stay on their hexes. -/
theorem hex_enemy {α : ℕ → SlotAlloc} {s : State} (hs : Reach (G3 hpP defQ P B) α s) {g : ℕ}
    (hg : g < P.n) : (s.units (3 * P.q + g)).hex = B.z g := by
  have hf := Reach.frame hs
  have := hf.ehex (3 * P.q + g) (by rw [init_enemy hg])
  rw [this, init_enemy hg]

theorem side_enemy {α : ℕ → SlotAlloc} {s : State} (hs : Reach (G3 hpP defQ P B) α s) {g : ℕ}
    (hg : g < P.n) : (s.units (3 * P.q + g)).side = .enemy := by
  rw [(Reach.frame hs).side, init_enemy hg]

end G3

/-! ## Lemma D.1 (reach) -/

namespace X3CBoard

variable {B : X3CBoard} {P : X3C} {hpP defQ : ℕ}

/-- **Lemma D.1, confinement half.** A stack standing on a hex of `R_e`, while every `E_S`
with `S ∋ e` is alive, cannot leave `R_e`: its BFS reach lies inside `R_e`.  (Neither the
"alone" hypothesis nor (I4) is needed for this half.) -/
theorem reach_sub_region (hI : B.InvCore P) {us : ℕ → Stack} {i e : ℕ} (hi : i < 3 * P.q)
    (he : e < 3 * P.q) (hstart : (us i).hex ∈ B.R e)
    (henemy : ∀ g < P.n, (us (3 * P.q + g)).hex = B.z g)
    (halive : ∀ g < P.n, e ∈ P.set g → (us (3 * P.q + g)).alive) :
    reachOf (G3 hpP defQ P B) us i ⊆ B.R e := by
  unfold reachOf
  apply reach_sub_of_closed hstart
  intro h hh h' hadj hfree
  rw [G3.free_iff] at hfree
  obtain ⟨hopen, hocc⟩ := hfree
  by_cases hz : ∃ g < P.n, h' = B.z g
  · obtain ⟨g, hg, rfl⟩ := hz
    obtain ⟨heg, -⟩ := hI.rDock e he h hh g hg hadj
    exact absurd (henemy g hg) (hocc (3 * P.q + g) (by omega) (by omega) (halive g hg heg))
  · push Not at hz
    exact hI.rClosed e he h hh h' hadj hopen hz

/-- The approach hexes of a confined stack: a hex of its reach adjacent to `z_g` is the
docking `d_g^e`, and `e ∈ S_g`. -/
theorem dock_of_confined (hI : B.InvCore P) {us : ℕ → Stack} {i e : ℕ} (hi : i < 3 * P.q)
    (he : e < 3 * P.q) (hstart : (us i).hex ∈ B.R e)
    (henemy : ∀ g < P.n, (us (3 * P.q + g)).hex = B.z g)
    (halive : ∀ g < P.n, e ∈ P.set g → (us (3 * P.q + g)).alive) {dest : Hex}
    (hd : dest ∈ reachOf (G3 hpP defQ P B) us i) {g : ℕ} (hg : g < P.n)
    (hadj : Hex.Adj dest (B.z g)) : e ∈ P.set g ∧ dest = B.d g e :=
  hI.rDock e he dest (reach_sub_region hI hi he hstart henemy halive hd) g hg hadj

/-- **Lemma D.1 (Reach).** In a reachable position, let slot `e`'s stack be alive on a hex of
`R_e`, let every `E_S` with `S ∋ e` be alive, and let no other living stack stand in `R_e`.
Then it can strike exactly the `E_S` with `S ∋ e`, and for each such `S` its only legal
approach hex is `d_S^e`.  (The starting position is the special case, `p_e` being in `R_e`.) -/
theorem lemmaD1 (hI : B.InvCore P) {α : ℕ → SlotAlloc} (hα : Feasible (G3 hpP defQ P B) α)
    {s : State} (hs : Reach (G3 hpP defQ P B) α s) {e : ℕ} (he : e < 3 * P.q)
    (hhex : (s.units e).hex ∈ B.R e) (hal : (s.units e).alive)
    (halive : ∀ g < P.n, e ∈ P.set g → (s.units (3 * P.q + g)).alive)
    (hsole : ∀ i < 3 * P.q + P.n, i ≠ e → (s.units i).alive → (s.units i).hex ∉ B.R e) :
    (∀ t, CanStrike (G3 hpP defQ P B) s.units e t ↔ ∃ g < P.n, e ∈ P.set g ∧ t = 3 * P.q + g) ∧
    ∀ g < P.n, e ∈ P.set g → ∀ dest,
      (dest ∈ reachOf (G3 hpP defQ P B) s.units e ∧ Hex.Adj dest (B.z g)) ↔ dest = B.d g e := by
  have henemy : ∀ g < P.n, (s.units (3 * P.q + g)).hex = B.z g := fun g hg => G3.hex_enemy hs hg
  have hsub := reach_sub_region (hpP := hpP) (defQ := defQ) hI he he hhex henemy halive
  -- the whole region is in the reach
  obtain ⟨-, hty⟩ := G3.player_of_alive hα hs he hal
  have hfull : B.R e ⊆ reachOf (G3 hpP defQ P B) s.units e := by
    intro h hh
    unfold reachOf
    rw [hty]
    have hw : Relation.ReflTransGen (fun a b => Hex.Adj a b ∧ b ∈ B.R e) (s.units e).hex h :=
      (rtg_symm_in (hI.pMem e he) (hI.rConn e he _ hhex)).trans (hI.rConn e he h hh)
    refine mem_reach_of_rtg hhex hw (fun x hx => ?_) (hI.i4 e he)
    rw [G3.free_iff]
    exact ⟨(hI.rOpen e he x hx).1, fun i hi hne hia hx' => hsole i hi hne hia (hx' ▸ hx)⟩
  refine ⟨fun t => ⟨?_, ?_⟩, fun g hg heg dest => ⟨fun ⟨hd, hadj⟩ => ?_, ?_⟩⟩
  · rintro ⟨ht, hts, hta, dest, hd, hadj⟩
    have hf := Reach.frame hs
    obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
    simp only [G3.k_eq, G3.n_eq] at hg hadj ⊢
    rw [henemy g hg] at hadj
    exact ⟨g, hg, (hI.rDock e he dest (hsub hd) g hg hadj).1, rfl⟩
  · rintro ⟨g, hg, heg, rfl⟩
    refine ⟨by simp; omega, G3.side_enemy hs hg, halive g hg heg, B.d g e,
      hfull (hI.dMem g hg e heg), ?_⟩
    rw [henemy g hg]; exact hI.dAdj g hg e heg
  · exact (hI.rDock e he dest (hsub hd) g hg hadj).2
  · rintro rfl
    exact ⟨hfull (hI.dMem g hg e heg), hI.dAdj g hg e heg⟩

end X3CBoard

end Homm3
