import Homm3.Accounting
import Homm3.Theorem1

/-!
# Session 3, target 1. Theorem 2: allocation-driven strong hardness (`G_{3P}(a, T)`)

Paper: §3.2 and Appendix E, "Theorem 2" — the instance `G_{3P}(a, T)`, Lemmas E.11–E.14,
totality.

* `G3P a T` — three rows, `8m + 2` columns, no obstacles; group `g` (0-indexed here, the
  paper's `g + 1`) has its enemy at `e_g = (X_g, 1)`, `X_g = 8g + 1`, and three slots
  `q_g^1 = (X_g − 1, 1)`, `q_g^2 = (X_g, 0)`, `q_g^3 = (X_g, 2)`, listed group by group (slot
  `3g + r` is `q_g^{r+1}`); player types `C_i = (1, 1, a_i, hp 5, spd 2, value 0)` of stock one;
  enemies one creature `(1, 1, 1, hp T, spd 1, value 1)`; `R = 1`, `W = m`.  It is
  `famInst (Thm2.layout m) a T` of `Accounting.lean`, and field by field the instance of
  `brute_force.build_3partition_instance` (`CrossCheck.threePart`).
* **Lemma E.11**: `Thm2.seat_adj` (each seat is a neighbour of its enemy), `Thm2.seat_inj`
  (the `3m` seats are distinct), `Thm2.sep` (`dist(q_g^r, e_{g'}) ≥ 7` for `g' ≠ g`),
  `Thm2.sep_tight` (`= 7` at `q_{g+1}^1` against `e_g`), `Thm2.contain` and **`Thm2.flower`**
  (in every position of round 1, a slot that has not acted can strike exactly its own group's
  enemy, whenever that enemy is alive).
* **Lemma E.12**: `Thm2.lemmaE12` — the ledger of `Accounting.lean` with the geometric clause
  "a slot strikes only its own group's enemy": striker sets pairwise disjoint, at most three
  strikers per enemy, absorbed damage at most the strikers' nominal `Σ a_i`, dead only if
  `Σ_{i ∈ S_g} a_i ≥ T`.
* **Lemma E.13**: `Thm2.yes` — the witness: seat the triple `g` in the slots of group `g`, every
  stack strikes from its own hex in the `NORMAL` phase, every enemy dies.
* **Lemma E.14**: `Fam.fam_no` (geometry-free; see `Accounting.lean`).
* **`theorem2`**: `Promise3P a T → (THREE_PARTITION a T ↔ ArmyAllocation (G3P a T))`;
  **`theorem2_total`**: the total reduction on integer encodings (`G_no` for an encoding outside
  the domain, `G_{3P}((1,1,1), 3)` for the empty one).
-/

namespace Homm3

open Function

namespace Thm2

/-- `e_g = (X_g, 1)` with `X_g = 8g + 1`. -/
def ehex (g : ℕ) : Hex := ⟨8 * (g : ℤ) + 1, 1⟩

/-- `q_g^{r+1}`: `(X_g − 1, 1)`, `(X_g, 0)`, `(X_g, 2)` for `r = 0, 1, 2`. -/
def seat (g r : ℕ) : Hex :=
  if r = 0 then ⟨8 * (g : ℤ), 1⟩ else if r = 1 then ⟨8 * (g : ℤ) + 1, 0⟩ else ⟨8 * (g : ℤ) + 1, 2⟩

/-- The layout of `G_{3P}` with `m` groups. -/
def layout (m : ℕ) : Layout where
  width := 8 * m + 2
  height := 3
  slots := (List.range (3 * m)).map (fun j => seat (j / 3) (j % 3))
  ehex := (List.range m).map ehex
  spd := 2

end Thm2

/-- **The instance `G_{3P}(a, T)`.** -/
def G3P (a : List ℕ) (T : ℕ) : Instance := famInst (Thm2.layout (a.length / 3)) a T

namespace Thm2

variable {a : List ℕ} {T : ℕ}

@[simp] theorem slots_len (m : ℕ) : (layout m).slots.length = 3 * m := by simp [layout]
@[simp] theorem ehex_len (m : ℕ) : (layout m).ehex.length = m := by simp [layout]

theorem k_eq : (G3P a T).k = 3 * (a.length / 3) := by simp [G3P]
theorem n_eq : (G3P a T).n = a.length / 3 := by simp [G3P]
theorem W_eq : (G3P a T).W = a.length / 3 := by simp [G3P]

theorem slotHex_eq {j : ℕ} (hj : j < 3 * (a.length / 3)) :
    (G3P a T).slotHex j = seat (j / 3) (j % 3) := by
  simp [G3P, Fam.slotHex_eq, layout, hj]

theorem enemy_hex {g : ℕ} (hg : g < a.length / 3) : ((G3P a T).enemy g).hex = ehex g := by
  unfold G3P; rw [Fam.enemy_eq (by simpa using hg)]; simp [layout, hg]

/-! ## Lemma E.11 -/

/-- Each seat of group `g` is a neighbour of `e_g` (row 1 is odd). -/
theorem seat_adj (g : ℕ) {r : ℕ} (hr : r < 3) : Hex.Adj (seat g r) (ehex g) := by
  interval_cases r <;> simp [seat, ehex, Hex.Adj, Hex.nbrs]

/-- The `3m` seats are pairwise distinct. -/
theorem seat_inj {g r g' r' : ℕ} (hr : r < 3) (hr' : r' < 3) (h : seat g r = seat g' r') :
    g = g' ∧ r = r' := by
  interval_cases r <;> interval_cases r' <;> simp [seat] at h <;> omega

theorem seat_ne_ehex (g r g' : ℕ) (hr : r < 3) : seat g r ≠ ehex g' := by
  interval_cases r <;> simp [seat, ehex] <;> omega

/-- **Lemma E.11, separation**: `dist(q_g^r, e_{g'}) ≥ 7` for `g' ≠ g`. -/
theorem sep {g r g' : ℕ} (hr : r < 3) (hne : g' ≠ g) : 7 ≤ Hex.dist (seat g r) (ehex g') := by
  have hne' : (g' : ℤ) ≠ g := by exact_mod_cast hne
  interval_cases r <;>
    simp only [seat, ehex, Hex.dist, Hex.axial, Hex.gauge_val, Hex.gaugeIf, max_def] <;>
    norm_num <;> split_ifs <;> omega

/-- The bound is tight: `dist(q_{g+1}^1, e_g) = 7`. -/
theorem sep_tight (g : ℕ) : Hex.dist (seat (g + 1) 0) (ehex g) = 7 := by
  simp only [seat, ehex, Hex.dist, Hex.axial, Hex.gauge_val, Hex.gaugeIf, max_def]
  norm_num
  split_ifs <;> omega

/-- The board is wide enough: every seat and every enemy hex is on the `3 × (8m + 2)` board. -/
theorem inBounds_seat {g r : ℕ} (hg : g < a.length / 3) (hr : r < 3) :
    (G3P a T).inBounds (seat g r) := by
  simp only [Instance.inBounds, G3P, famInst, layout]
  interval_cases r <;> simp [seat] <;> omega

theorem inBounds_ehex {g : ℕ} (hg : g < a.length / 3) : (G3P a T).inBounds (ehex g) := by
  simp only [Instance.inBounds, G3P, famInst, layout, ehex]; omega

theorem spd_of_mem {x : CType × ℕ} (hx : x ∈ (G3P a T).army) : x.1.spd = 2 := by
  simp only [G3P, famInst, List.mem_map] at hx
  obtain ⟨ai, -, rfl⟩ := hx; rfl

variable {α : ℕ → SlotAlloc} {s : State}

theorem hex_of_Q (h : Reach (G3P a T) α s) {i : ℕ} (hi : i < 3 * (a.length / 3)) (hiQ : i ∈ s.Q) :
    (s.units i).hex = seat (i / 3) (i % 3) := by
  obtain ⟨-, -, hhex⟩ := lemmaE1 rfl h
  rw [hhex i hiQ, initUnits_player (by rw [k_eq]; exact hi)]
  exact slotHex_eq hi

theorem hex_enemy (h : Reach (G3P a T) α s) {g : ℕ} (hg : g < a.length / 3) :
    (s.units ((G3P a T).k + g)).hex = ehex g := by
  have hf := h.frame
  have hg' : g < (G3P a T).n := by rw [n_eq]; exact hg
  rw [hf.ehex _ (by rw [initUnits_enemy hg']), initUnits_enemy hg']
  exact enemy_hex hg

/-- **Lemma E.11, containment**: in every position of round 1, a slot that has not taken its
terminal action can strike no enemy but its own group's. -/
theorem contain (hα : Feasible (G3P a T) α) (h : Reach (G3P a T) α s) {i : ℕ}
    (hi : i < 3 * (a.length / 3)) (hiQ : i ∈ s.Q) {t : ℕ}
    (hc : CanStrike (G3P a T) s.units i t) : t = (G3P a T).k + i / 3 := by
  obtain ⟨ht, hts, -, dest, hd, hadj⟩ := hc
  have hf := h.frame
  obtain ⟨-, hal⟩ := h.mem_Q rfl hiQ
  obtain ⟨x, hx, hty⟩ := slotType_mem hα (by rw [k_eq]; exact hi) hal
  obtain ⟨g', hg', rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
  rw [n_eq] at hg'
  have hspd : (s.units i).type.spd = 2 := by
    rw [hf.type, initUnits_player (by rw [k_eq]; exact hi)]; simp only; rw [hty]
    exact spd_of_mem hx
  unfold reachOf at hd
  rw [hex_of_Q h hi hiQ, hspd] at hd
  rw [hex_enemy h hg'] at hadj
  have hr := strike_radius _ 2 hd hadj
  by_contra hne
  have := sep (g := i / 3) (r := i % 3) (g' := g') (Nat.mod_lt _ (by norm_num))
    (fun e => hne (by rw [e]))
  push_cast at hr
  omega

/-- **Lemma E.11, the flower**: in every position of round 1, a slot that has not acted can
strike exactly its own group's enemy, and can strike it whenever it is alive. -/
theorem flower (hα : Feasible (G3P a T) α) (h : Reach (G3P a T) α s) {i : ℕ}
    (hi : i < 3 * (a.length / 3)) (hiQ : i ∈ s.Q) (t : ℕ) :
    CanStrike (G3P a T) s.units i t ↔ t = (G3P a T).k + i / 3 ∧ (s.units t).alive := by
  constructor
  · intro hc; exact ⟨contain hα h hi hiQ hc, hc.2.2.1⟩
  · rintro ⟨rfl, hal⟩
    have hg : i / 3 < a.length / 3 := by omega
    have hf := h.frame
    refine ⟨by unfold Instance.N; rw [n_eq, k_eq]; omega, ?_, hal, (s.units i).hex,
      start_mem_reach _ _, ?_⟩
    · rw [hf.side, initUnits_enemy (by rw [n_eq]; exact hg)]
    · rw [hex_of_Q h hi hiQ, hex_enemy h hg]
      exact seat_adj _ (Nat.mod_lt _ (by norm_num))

/-! ## Lemma E.12 -/

/-- **Lemma E.12 (damage accounting)**: along every play of round 1 under every feasible
allocation there is a strike record in which only the three slots of group `g` strike `E_g`,
striker sets are pairwise disjoint (`Ledger.disjoint`), the absorbed damage is
`min(T, delivered)` with every blow at most nominal, and `E_g` is dead only if its strikers'
types sum to at least `T`. -/
theorem lemmaE12 (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x) (hα : Feasible (G3P a T) α)
    (h : Reach (G3P a T) α s) :
    ∃ τ β, Ledger (G3P a T) α (fun i g => g = i / 3) s τ β ∧
      (∀ g, strikers (G3P a T) τ g ⊆ {3 * g, 3 * g + 1, 3 * g + 2}) ∧
      (∀ g, (strikers (G3P a T) τ g).card ≤ 3) ∧
      ∀ g < a.length / 3, (s.units ((G3P a T).k + g)).pool = 0 →
        T ≤ ∑ i ∈ Fam.typesOf α (strikers (G3P a T) τ g), a.getD i 0 := by
  obtain ⟨τ, β, hL⟩ := ledger (I := G3P a T) (Fam.acctHyp (L := layout (a.length / 3)) hT ha) hα
    (P := fun i g => g = i / 3) (fun s hs i hi hiQ g _ hc => by
      have := contain hα hs (by rw [← k_eq]; exact hi) hiQ hc
      omega) h
  have hsub : ∀ g, strikers (G3P a T) τ g ⊆ {3 * g, 3 * g + 1, 3 * g + 2} := by
    intro g j hj
    simp only [strikers, Finset.mem_filter] at hj
    have := (hL.acted j g hj.2).2.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine ⟨τ, β, hL, hsub, fun g => (Finset.card_le_card (hsub g)).trans Finset.card_le_three,
    fun g hg h0 => ?_⟩
  have hd := hL.dead (by rw [n_eq]; exact hg) h0
  unfold G3P at hd ⊢
  rw [Fam.enemy_eq (by simpa using hg)] at hd
  rw [Fam.sum_typesOf hα (fun j hj => by
    simp only [strikers, Finset.mem_filter] at hj; simpa using hj.1)]
  exact hd

/-! ## Lemma E.13: the witness -/

/-- The witness allocation: slot `3g + r` holds the `r`-th element of triple `g`. -/
def αP (S : ℕ → Finset ℕ) (j : ℕ) : SlotAlloc := ⟨ThreeP.pick S (j / 3) (j % 3), 1⟩

variable {S : ℕ → Finset ℕ}

theorem αP_feasible (hS : ThreeP.Parts a T S) : Feasible (G3P a T) (αP S) := by
  refine ⟨fun j hj _ => ?_, fun t ht => ?_⟩
  · rw [k_eq] at hj
    simp only [αP, G3P, Fam.army_len]
    exact hS.pick_lt (by omega) (Nat.mod_lt _ (by norm_num))
  · -- a type sits in at most one slot
    have ht' : t < a.length := by simpa [G3P, Fam.army_len] using ht
    have h1 : ((G3P a T).army.getD t default).2 = 1 := by
      unfold G3P; rw [Fam.army_getD ht']
    rw [h1]
    simp only [αP]
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    apply Finset.card_le_one.mpr
    intro j hj j' hj'
    simp only [Finset.mem_filter, Finset.mem_range, k_eq] at hj hj'
    have := hS.pick_inj (by omega) (by omega) (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)) (hj.2.trans hj'.2.symm)
    omega


/-- The target of an attack keeps its `DEFEND` flag (only its pool and charge change). -/
theorem _root_.Homm3.resolveAttack_defending_target {us : ℕ → Stack} {i t : ℕ} {dest : Hex}
    (hit : i ≠ t) : (resolveAttack us i t dest t).defending = (us t).defending := by
  unfold resolveAttack
  split_ifs <;> simp [Ne.symm hit, Stack.hit]

theorem αP_count (j : ℕ) : (αP S j).count = 1 := rfl
theorem αP_type (j : ℕ) : (αP S j).type = ThreeP.pick S (j / 3) (j % 3) := rfl

theorem init_player_αP (hS : ThreeP.Parts a T S) {j : ℕ} (hj : j < (G3P a T).k) :
    initUnits (G3P a T) (αP S) j = ⟨.player, j,
      famPlayer 2 (a.getD (ThreeP.pick S (j / 3) (j % 3)) 0), seat (j / 3) (j % 3), 5, 1, 1,
      false⟩ := by
  have hj' : j < 3 * (a.length / 3) := by rw [← k_eq]; exact hj
  have hty : (G3P a T).slotType (αP S) j = famPlayer 2 (a.getD (ThreeP.pick S (j / 3) (j % 3)) 0) :=
    Fam.slotType_eq (L := layout (a.length / 3)) (α := αP S) (by simp [αP])
      (hS.pick_lt (by omega) (Nat.mod_lt _ (by norm_num)))
  rw [initUnits_player hj, hty, slotHex_eq hj']
  simp [αP, famPlayer]

theorem init_enemy_G3P {g : ℕ} (hg : g < a.length / 3) :
    initUnits (G3P a T) α ((G3P a T).k + g) = ⟨.enemy, g, famEnemy T, ehex g, T, 1, 1, false⟩ := by
  have hg' : g < (G3P a T).n := by rw [n_eq]; exact hg
  rw [initUnits_enemy hg', show (G3P a T).enemy g = ⟨famEnemy T, 1, ehex g⟩ from by
    unfold G3P; rw [Fam.enemy_eq (by simpa using hg)]; simp [layout, hg]]
  simp [famEnemy]

/-- Invariant of the witness run in the `NORMAL` phase: players still queued are fresh, every
enemy is undefended and has lost exactly the blows of its group's slots that have acted. -/
structure WN (a : List ℕ) (T : ℕ) (S : ℕ → Finset ℕ) (s : State) : Prop where
  reach : Reach (G3P a T) (αP S) s
  phase : s.phase = .normal
  bucket : ∀ i ∈ s.bucket, (s.units i).side = .enemy
  fresh : ∀ j < (G3P a T).k, j ∈ s.queue → (s.units j).pool = 5
  edef : ∀ g < a.length / 3, (s.units ((G3P a T).k + g)).defending = false
  epool : ∀ g < a.length / 3, (s.units ((G3P a T).k + g)).pool =
    T - ∑ r ∈ (Finset.range 3).filter (fun r => 3 * g + r ∉ s.queue),
      a.getD (ThreeP.pick S g r) 0

theorem WN.init (hS : ThreeP.Parts a T S) : WN a T S (initState (G3P a T) (αP S)) where
  reach := .refl
  phase := rfl
  bucket := by simp [initState]
  fresh j hj _ := by simp only [initState]; rw [init_player_αP hS hj]
  edef g hg := by simp only [initState]; rw [init_enemy_G3P hg]
  epool g hg := by
    simp only [initState]
    rw [init_enemy_G3P hg]
    have : (Finset.range 3).filter (fun r => 3 * g + r ∉ (initState (G3P a T) (αP S)).queue) = ∅ := by
      apply Finset.filter_false_of_mem
      intro r hr
      simp only [Finset.mem_range] at hr
      have hj : 3 * g + r < (G3P a T).k := by rw [k_eq]; omega
      rw [not_not]
      apply Prop11.mem_initQueue (by unfold Instance.N; omega)
      rw [init_player_αP hS hj]; unfold Stack.alive; norm_num
    simp only [initState] at this
    rw [this]; simp

/-- One step of the witness run: a player stack strikes its group's enemy from its own hex, an
enemy `WAIT`s (`(‡)`), a dead stack is skipped. -/
theorem WN.step (hP : Promise3P a T) (hS : ThreeP.Parts a T S) {s : State} (hw : WN a T S s)
    {i : ℕ} {q : List ℕ} (hq : s.queue = i :: q) :
    ∃ s', Step (G3P a T) s s' ∧ WN a T S s' ∧ s'.queue = q := by
  obtain ⟨-, hn, -⟩ := lemmaE1 rfl hw.reach
  have hf := Reach.frame hw.reach
  have hnq := head_not_mem_after hq hn
  have hmem : ∀ j, j ∈ q ↔ j ∈ s.queue ∧ j ≠ i := by
    intro j; rw [hq, List.mem_cons]
    constructor
    · intro hj; exact ⟨Or.inr hj, fun e => hnq (e ▸ List.mem_append_left _ hj)⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
  have hK := k_eq (a := a) (T := T)
  have hfilt_ne : ∀ g', (∀ x < 3, 3 * g' + x ≠ i) →
      (Finset.range 3).filter (fun r' => 3 * g' + r' ∉ q) =
        (Finset.range 3).filter (fun r' => 3 * g' + r' ∉ s.queue) := by
    intro g' hne
    apply Finset.filter_congr
    intro x hx
    rw [Finset.mem_range] at hx
    rw [hmem]
    constructor
    · intro h h'; exact h ⟨h', hne x hx⟩
    · rintro h ⟨h', -⟩; exact h h'
  by_cases ha : (s.units i).alive
  · rcases hside : (s.units i).side with _ | _
    · -- a player stack: strike `E_{i/3}` from its own hex
      have hi : i < (G3P a T).k := initUnits_side_player (by rw [← hf.side]; exact hside)
      set g := i / 3 with hgdef
      set r := i % 3 with hrdef
      have hg : g < a.length / 3 := by omega
      have hr : r < 3 := Nat.mod_lt _ (by norm_num)
      have hiQ : i ∈ s.Q := by simp [State.Q, hq]
      have hpool : (s.units i).pool = 5 := hw.fresh i hi (by rw [hq]; exact List.mem_cons_self)
      have hty : (s.units i).type = famPlayer 2 (a.getD (ThreeP.pick S g r) 0) := by
        rw [hf.type, init_player_αP hS hi]
      set ar := a.getD (ThreeP.pick S g r) 0 with hardef
      have har : 1 ≤ ar := ThreeP.pos_of_promise hP (hS.pick_lt hg hr)
      set F := (Finset.range 3).filter (fun r' => 3 * g + r' ∉ s.queue) with hFdef
      have hrF : r ∉ F := by
        simp only [hFdef, Finset.mem_filter, not_and, not_not]
        intro _; rw [show 3 * g + r = i by omega, hq]; exact List.mem_cons_self
      have hsumle : ∑ r' ∈ F, a.getD (ThreeP.pick S g r') 0 + ar ≤ T := by
        have h1 : insert r F ⊆ Finset.range 3 := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Finset.mem_range.mpr hr
          · exact (Finset.mem_filter.mp hx).1
        have := Finset.sum_le_sum_of_subset (f := fun r' => a.getD (ThreeP.pick S g r') 0) h1
        rw [Finset.sum_insert hrF, hS.sum_pick_T hg] at this
        omega
      have hepool := hw.epool g hg
      rw [← hFdef] at hepool
      have hTa : ar ≤ (s.units ((G3P a T).k + g)).pool := by rw [hepool]; omega
      have hta : (s.units ((G3P a T).k + g)).alive := by unfold Stack.alive; omega
      have htN : (G3P a T).k + g < (G3P a T).N := by unfold Instance.N; rw [n_eq]; omega
      have hts : (s.units ((G3P a T).k + g)).side = .enemy := by
        rw [hf.side, init_enemy_G3P hg]
      have hadj : Hex.Adj (s.units i).hex (s.units ((G3P a T).k + g)).hex := by
        rw [hex_of_Q hw.reach (by omega) hiQ, hex_enemy hw.reach hg]; exact seat_adj g hr
      have hstep := Step.playerAttack (I := G3P a T) (dest := (s.units i).hex)
        (t := (G3P a T).k + g) hq ha hside (start_mem_reach _ _) htN hta hts hadj
      refine ⟨_, hstep, ?_, rfl⟩
      have hit : i ≠ (G3P a T).k + g := by omega
      have hb : blow { activate (s.units i) with hex := (s.units i).hex }
          (s.units ((G3P a T).k + g)) = ar := by
        have := Prop11.blow_eq (C := famPlayer 2 ar) (c := 1)
          (a := { activate (s.units i) with hex := (s.units i).hex })
          (tg := s.units ((G3P a T).k + g))
          (by simp only [activate]; exact hty) (by simp [famPlayer]; exact har)
          (by simp [famPlayer]) (by simp only [activate]; rw [hpool]; rfl) le_rfl
          (by
            unfold Stack.defEff
            rw [hw.edef g hg, hf.type, init_enemy_G3P hg]; simp [famEnemy, famPlayer])
        rw [this, one_mul]; rfl
      refine ⟨hw.reach.tail hstep, hw.phase, ?_, ?_, ?_, ?_⟩
      · intro x hx; rw [hstep.side]; exact hw.bucket x hx
      · intro j hj hjq
        obtain ⟨hjq', hji⟩ := (hmem j).mp hjq
        simp only
        rw [resolveAttack_of_ne hji (by omega)]
        exact hw.fresh j hj hjq'
      · intro g' hg'
        simp only
        by_cases hgg : g' = g
        · subst hgg; rw [resolveAttack_defending_target hit]; exact hw.edef _ hg'
        · rw [resolveAttack_of_ne (by omega) (by omega)]; exact hw.edef g' hg'
      · intro g' hg'
        simp only
        by_cases hgg : g' = g
        · subst hgg
          rw [resolveAttack_pool_target hit, hepool, hb]
          have hF' : (Finset.range 3).filter (fun r' => 3 * g + r' ∉ q) = insert r F := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range, hFdef]
            rw [hmem]
            constructor
            · rintro ⟨hx, h⟩
              by_cases hxr : x = r
              · exact Or.inl hxr
              · exact Or.inr ⟨hx, fun h' => h ⟨h', by omega⟩⟩
            · rintro (rfl | ⟨hx, h⟩)
              · exact ⟨hr, fun ⟨_, h2⟩ => h2 (by omega)⟩
              · exact ⟨hx, fun ⟨h1, _⟩ => h h1⟩
          rw [hF', Finset.sum_insert hrF, Nat.sub_sub, add_comm]
        · rw [resolveAttack_of_ne (by omega) (by omega), hw.epool g' hg',
            hfilt_ne g' (fun x hx => by omega)]
    · -- an enemy stack: `(‡)` makes it `WAIT`
      have hstep := Step.enemyWait (I := G3P a T) hw.phase hq ha hside
      refine ⟨_, hstep, ?_, rfl⟩
      have hik : ∀ j < (G3P a T).k, j ≠ i := by
        intro j hj e; subst e
        rw [hf.side, initUnits_side_of_lt hj] at hside; cases hside
      refine ⟨hw.reach.tail hstep, hw.phase, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [hstep.side]
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw.bucket x hx
        · exact hside
      · intro j hj hjq
        simp only
        rw [update_of_ne (hik j hj)]
        exact hw.fresh j hj ((hmem j).mp hjq).1
      · intro g' hg'
        simp only [update_apply]
        split_ifs with he
        · simp [activate]
        · exact hw.edef g' hg'
      · intro g' hg'
        have hfilt := hfilt_ne g' (fun x hx => hik _ (by omega))
        simp only
        rw [hfilt, ← hw.epool g' hg', update_apply]
        split_ifs with he
        · rw [he]; simp [activate]
        · rfl
  · -- a dead stack is skipped; it cannot be a player slot (those are fresh)
    have hstep := Step.skip (I := G3P a T) hq ha
    have hik : ∀ j < (G3P a T).k, j ≠ i := by
      intro j hj e; subst e
      exact ha (by unfold Stack.alive; rw [hw.fresh j hj (by rw [hq]; exact List.mem_cons_self)]; norm_num)
    refine ⟨_, hstep, ⟨hw.reach.tail hstep, hw.phase, hw.bucket, ?_, hw.edef, ?_⟩, rfl⟩
    · intro j hj hjq; exact hw.fresh j hj ((hmem j).mp hjq).1
    · intro g' hg'
      simp only
      rw [hfilt_ne g' (fun x hx => hik _ (by omega))]; exact hw.epool g' hg'

theorem WN.run (hP : Promise3P a T) (hS : ThreeP.Parts a T S) :
    ∀ (L : List ℕ) (s : State), WN a T S s → s.queue = L →
      ∃ s', Relation.ReflTransGen (Step (G3P a T)) s s' ∧ WN a T S s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    obtain ⟨s1, h1, hw1, hq1⟩ := hw.step hP hS hq
    obtain ⟨s2, h2, hw2, hq2⟩ := WN.run hP hS q s1 hw1 hq1
    exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩

/-- **Lemma E.13 (`3-PARTITION` yes ⟹ game yes).** -/
theorem yes (hP : Promise3P a T) (h3 : THREE_PARTITION a T) : ArmyAllocation (G3P a T) := by
  obtain ⟨S, hS⟩ := ThreeP.parts_of h3
  refine ⟨αP S, αP_feasible hS, ?_⟩
  by_cases hm0 : a.length / 3 = 0
  · obtain ⟨s, hs, hd⟩ := exists_done (G3P a T) (initState (G3P a T) (αP S))
    exact ⟨s, hs, hd, by rw [W_eq, hm0]; exact Nat.zero_le _⟩
  have hT : 1 ≤ T := by
    have := (hP.2.2 _ (ThreeP.getD_mem (a := a) (i := 0) (by omega))).2; omega
  obtain ⟨s1, h1, hw1, hq1⟩ := WN.run hP hS _ _ (WN.init hS) rfl
  have hdead : ∀ g < a.length / 3, (s1.units ((G3P a T).k + g)).pool = 0 := by
    intro g hg
    rw [hw1.epool g hg, hq1]
    simp only [List.not_mem_nil, not_false_eq_true, Finset.filter_true]
    rw [hS.sum_pick_T hg, Nat.sub_self]
  obtain ⟨s2, h2, hd2⟩ := exists_done (G3P a T) s1
  have hr2 : Reach (G3P a T) (αP S) s2 := hw1.reach.trans h2
  refine ⟨s2, hr2, hd2, ?_⟩
  unfold G3P at hr2 ⊢
  rw [Fam.destroyed_eq hT (Reach.frame hr2)]
  simp only [W_eq, ehex_len, slots_len] at *
  have : ∀ g ∈ Finset.range (a.length / 3),
      (if (s2.units (3 * (a.length / 3) + g)).pool = 0 then 1 else 0) = 1 := by
    intro g hg
    have h0 := hdead g (Finset.mem_range.mp hg)
    rw [k_eq] at h0
    have := pool_le_of_rtg h2 (3 * (a.length / 3) + g)
    rw [if_pos (by omega)]
  rw [Finset.sum_congr rfl this]
  simp

/-- **Theorem 2.** On the promise of `3-PARTITION`, `(a, T)` is a yes-instance iff `G_{3P}(a, T)`
is a yes-instance of `ARMY-ALLOCATION`. -/
theorem theorem2 (a : List ℕ) (T : ℕ) (hP : Promise3P a T) :
    THREE_PARTITION a T ↔ ArmyAllocation (G3P a T) :=
  ⟨yes hP, Fam.fam_no hP (by simp [layout])⟩

end Thm2

/-! ## Totality -/

/-- **The total reduction** of Appendix E (Theorem 2, *Totality*; Theorem 4 "verbatim"), for a
construction `G`: an encoding failing a syntactic check goes to `G_no`, the empty encoding to
the fixed yes-instance `G((1,1,1), 3)`, every other one to `G(a, T)`. -/
def reduction3P (G : List ℕ → ℕ → Instance) (a : List ℤ) (T : ℤ) : Instance :=
  if InDomain3P a T then (if a = [] then G [1, 1, 1] 3 else G (a.map Int.toNat) T.toNat)
  else Corridor.Gno

/-- The totality branch is correct for any construction that is correct on the promise. -/
theorem reduction3P_iff (G : List ℕ → ℕ → Instance)
    (hG : ∀ a T, Promise3P a T → (THREE_PARTITION a T ↔ ArmyAllocation (G a T)))
    (a : List ℤ) (T : ℤ) : THREE_PARTITIONℤ a T ↔ ArmyAllocation (reduction3P G a T) := by
  unfold reduction3P
  split_ifs with hd hnil
  · subst hnil
    exact ⟨fun _ => (hG _ _ ThreeP.promise_111).mp ThreeP.yes_111, fun _ => ThreeP.nil_iff T⟩
  · rw [ThreeP.toNat_iff hd]; exact hG _ _ (ThreeP.promise_toNat hd hnil)
  · exact ⟨fun h => absurd h.1 hd, fun h => absurd h Corridor.Gno_no⟩

/-- **Theorem 2, total form**: the reduction is correct on every integer encoding. -/
theorem theorem2_total (a : List ℤ) (T : ℤ) :
    THREE_PARTITIONℤ a T ↔ ArmyAllocation (reduction3P G3P a T) :=
  reduction3P_iff G3P Thm2.theorem2 a T

end Homm3
