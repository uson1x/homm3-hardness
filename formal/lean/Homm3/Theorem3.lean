import Homm3.X3CBoard
import Homm3.LemmaE20

/-!
# Session 4, targets 1–2. Theorem 3 and Corollary 3.1 (modulo the embedding)

Paper: §3.3, Appendix D.5 (Lemmas D.5–D.9, the proofs of Theorem 3 and Corollary 3.1).

* **The generalized ledger** (`LedgerB`, `ledgerB`): session 3's strike/blow ledger with two
  changes — each recorded strike carries a predicate `Bd j (β j)` on its *actual* blow (not
  only `β ≤ nominal`), and the per-attack hypothesis may consult the **current** ledger.  The
  second change is what lets Lemma D.7 run as an invariant: whether the doorway of a dead
  enemy is plugged is read off the ledger of the position in which a stack attacks.
* **Lemma D.5** (`lemmaD5`, `hp(P) ≥ 2`): no player creature dies, every occupied slot's stack
  keeps its count all round (so it is never skipped).
* **Lemma D.6** (`lemmaD6`, `def(Q) ≥ 2`, no geometry): `t ≤ q` dead enemies; at `t = q` every
  slot holds one creature, strikes a dead enemy, and each dead enemy has exactly three
  strikers.  Uses the ledger's disjoint striker sets and Lemma 3.2's abstract core.
* **Lemma D.7** (`confinedLedger`, `lemmaD7`): for **every** allocation with at most one
  creature per slot (not only in the tight situation of D.6), in every position of round 1,
  every strike so far was by a slot `e` on an `E_S` with `S ∋ e`; and while slot `e` has not
  taken its terminal action, every `E_S` with `S ∋ e` is alive.  The induction runs along the
  play: a dead `E_S` has `≥ 3` recorded strikers, all in `S` by the invariant, hence exactly
  the three slots of `S` — so slot `e ∈ S` has already acted.
* **Lemma D.8** (`lemmaD8`) through a general witness run (`witness`): slots strike their
  planned targets from their dockings in the `NORMAL` phase; the negative control reuses it.
* **Lemma D.9** (`lemmaD9`), **`theorem3`**, **`cor31`** (Corollary 3.1, `BATTLE-PLAY`, valid
  already for `def(Q) ≥ att(P)`), `winning_unique` (the all-ones allocation is the only
  winner), and the total form `theorem3_total` (in `BoardCheck.lean`).
* `theorem3_core`, `cor31_core`: the same statements from `InvCore`, the part of (I1)–(I4)
  the proof consumes; `theorem3`, `cor31` follow through `Inv.core`.
-/

namespace Homm3

open Function

variable {I : Instance} {α : ℕ → SlotAlloc}

/-! ## The generalized ledger -/

/-- A ledger whose recorded strikes satisfy `P j g`, and whose blows satisfy `Bd j (β j)`. -/
structure LedgerB (I : Instance) (P : ℕ → ℕ → Prop) (Bd : ℕ → ℕ → Prop) (s : State)
    (τ : ℕ → Option ℕ) (β : ℕ → ℕ) : Prop where
  acted : ∀ j g, τ j = some g → j < I.k ∧ j ∉ s.Q ∧ g < I.n ∧ P j g ∧ Bd j (β j)
  pool : ∀ g < I.n, (s.units (I.k + g)).pool = (I.enemy g).type.hp - ∑ j ∈ strikers I τ g, β j

/-- The hypothesis of `ledgerB`: whatever a strike from a reachable position (with its current
ledger) satisfies. -/
def LedgerHyp (I : Instance) (α : ℕ → SlotAlloc) (P Bd : ℕ → ℕ → Prop) : Prop :=
  ∀ s τ β, Reach I α s → LedgerB I P Bd s τ β → ∀ i q, s.queue = i :: q →
    (s.units i).alive → (s.units i).side = .player → ∀ g < I.n,
    ∀ dest ∈ reachOf I s.units i, (s.units (I.k + g)).alive →
    Hex.Adj dest (s.units (I.k + g)).hex →
    P i g ∧ Bd i (blow { activate (s.units i) with hex := dest } (s.units (I.k + g)))

/-- **The generalized ledger exists in every position of round 1.** -/
theorem ledgerB (hR : I.R = 1) (hone : ∀ g < I.n, (I.enemy g).count = 1)
    {P Bd : ℕ → ℕ → Prop} (hPB : LedgerHyp I α P Bd) {s : State} (h : Reach I α s) :
    ∃ τ β, LedgerB I P Bd s τ β := by
  induction h with
  | refl =>
    refine ⟨fun _ => none, fun _ => 0, ⟨fun j g h => (by simp at h), ?_⟩⟩
    intro g hg
    simp only [initState, initUnits_enemy hg, hone g hg, one_mul, Finset.sum_const_zero,
      Nat.sub_zero]
  | @tail s₁ s₂ h₁ hst ih =>
    obtain ⟨τ, β, hL⟩ := ih
    obtain ⟨hr, hn, -⟩ := lemmaE1 hR h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have hf := Reach.frame h₁
    rcases hst.attack_or with hall | ⟨i, q, dest, t, hq, ha, hs, hd, ht, hta, hts, hadj, hus,
      hq', hb'⟩
    · refine ⟨τ, β, ⟨fun j g hj => ?_, fun g hg => by rw [hall]; exact hL.pool g hg⟩⟩
      obtain ⟨a1, a2, a3, a4⟩ := hL.acted j g hj
      exact ⟨a1, fun hm => a2 (hsub j hm), a3, a4⟩
    · have hiQ : i ∈ s₁.Q := by simp [State.Q, hq]
      have hi : i < I.k := initUnits_side_player (by rw [← hf.side]; exact hs)
      obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
      have hτi : τ i = none := by
        rcases e : τ i with _ | g0
        · rfl
        · exact absurd hiQ (hL.acted i g0 e).2.1
      have hiQ' : i ∉ s₂.Q := by
        simp only [State.Q, hq', hb']; exact head_not_mem_after hq hn
      set a : Stack := { activate (s₁.units i) with hex := dest } with ha_def
      set b := blow a (s₁.units (I.k + g)) with hb_def
      obtain ⟨hPi, hBi⟩ := hPB s₁ τ β h₁ hL i q hq ha hs g hg dest hd hta hadj
      refine ⟨update τ i (some g), update β i b, ⟨?_, ?_⟩⟩
      · intro j g' hj
        by_cases hji : j = i
        · subst hji
          rw [update_self] at hj; cases hj
          exact ⟨hi, hiQ', hg, hPi, by rw [update_self]; exact hBi⟩
        · rw [update_of_ne hji] at hj
          obtain ⟨a1, a2, a3, a4, a5⟩ := hL.acted j g' hj
          exact ⟨a1, fun hm => a2 (hsub j hm), a3, a4, by rw [update_of_ne hji]; exact a5⟩
      · intro g' hg'
        rw [hus]
        by_cases hgg : g' = g
        · subst hgg
          rw [resolveAttack_pool_target (by omega), hL.pool g' hg',
            strikers_update_self hi hτi, Finset.sum_insert (by
              simp [strikers, hτi]), update_self, Nat.sub_sub]
          have : ∑ j ∈ strikers I τ g', update β i b j = ∑ j ∈ strikers I τ g', β j := by
            apply Finset.sum_congr rfl
            intro j hj
            have : j ≠ i := by rintro rfl; simp [strikers, hτi] at hj
            rw [update_of_ne this]
          rw [this, add_comm]
        · rw [resolveAttack_of_ne (by omega) (by omega), hL.pool g' hg',
            strikers_update_ne hτi hgg]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have : j ≠ i := by rintro rfl; simp [strikers, hτi] at hj
          rw [update_of_ne this]

theorem strikers_sub (τ : ℕ → Option ℕ) (g : ℕ) : strikers I τ g ⊆ Finset.range I.k :=
  fun _ hj => (Finset.mem_filter.mp hj).1

theorem mem_strikers {τ : ℕ → Option ℕ} {g j : ℕ} (hj : j < I.k) (h : τ j = some g) :
    j ∈ strikers I τ g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩

theorem strikers_spec {τ : ℕ → Option ℕ} {g j : ℕ} (h : j ∈ strikers I τ g) : τ j = some g :=
  (Finset.mem_filter.mp h).2

/-! ## `G_3`: the attacking stack -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

/-- The attacking stack at its activation: `c ≥ 1` creatures of `P`, full pool, hence count `c`. -/
theorem attacker (hhp : 1 ≤ hpP) (hα : Feasible (G3 hpP defQ P B) α) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) {i : ℕ} (hi : i < 3 * P.q) (hiQ : i ∈ s.Q)
    (ha : (s.units i).alive) :
    0 < (α i).count ∧ (s.units i).type = ptype hpP B.σ ∧ (s.units i).count = (α i).count ∧
      (s.units i).hex = B.p i := by
  obtain ⟨hc, hty⟩ := G3.player_of_alive hα hs hi ha
  have hpool := fresh_of_Q (I := G3 hpP defQ P B) rfl hs i (by simpa using hi) hiQ
  rw [G3.init_player hα hi hc] at hpool
  refine ⟨hc, hty, Prop11.count_eq (by rw [hty]; exact hhp) (by rw [hty]; exact hpool), ?_⟩
  obtain ⟨-, -, hx⟩ := lemmaE1 (I := G3 hpP defQ P B) rfl hs
  rw [hx i hiQ, G3.init_player hα hi hc]

/-- The blow of slot `i` on `E_g`: `damage c 1 (1 − defEff)`, `defEff ≥ def(Q)`. -/
theorem blow_eq (hhp : 1 ≤ hpP) (hα : Feasible (G3 hpP defQ P B) α) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) {i : ℕ} (hi : i < 3 * P.q) (hiQ : i ∈ s.Q)
    (ha : (s.units i).alive) {g : ℕ} (hg : g < P.n) (dest : Hex) :
    ∃ Δ : ℤ, Δ ≤ 1 - defQ ∧
      blow { activate (s.units i) with hex := dest } (s.units (3 * P.q + g)) =
        damage (α i).count 1 Δ := by
  obtain ⟨-, hty, hcnt, -⟩ := attacker hhp hα hs hi hiQ ha
  have htg : (s.units (3 * P.q + g)).type = qtype defQ := by
    rw [(Reach.frame hs).type, G3.init_enemy hg]
  refine ⟨1 - (s.units (3 * P.q + g)).defEff, ?_, ?_⟩
  · unfold Stack.defEff; rw [htg]; simp only [qtype]; push_cast; split_ifs <;> omega
  · unfold blow
    have hc : ({ activate (s.units i) with hex := dest } : Stack).count = (α i).count := by
      rw [← hcnt]; rfl
    rw [hc]
    simp only [activate, hty, ptype]
    push_cast; ring_nf

end T3

/-! ## Lemma D.5 (no interference) -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

/-- **Lemma D.5 (No interference).** With `hp(P) ≥ 2`: every occupied slot's stack is alive in
every position of round 1 and keeps its count `c`; it is untouched until its terminal action
and loses at most one hit point (one retaliation) afterwards. -/
theorem lemmaD5 (hhp : 2 ≤ hpP) (hα : Feasible (G3 hpP defQ P B) α) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) : ∀ j < 3 * P.q, 0 < (α j).count →
      (s.units j).alive ∧ (s.units j).count = (α j).count ∧
      (j ∈ s.Q → (s.units j).pool = (α j).count * hpP) ∧
      (α j).count * hpP ≤ (s.units j).pool + 1 := by
  have key : ∀ j < 3 * P.q, 0 < (α j).count → (α j).count * hpP ≤ (s.units j).pool + 1 := by
    induction hs with
    | refl =>
      intro j hj hc
      simp only [initState]; rw [G3.init_player hα hj hc]; simp
    | @tail s₁ s₂ h₁ hst ih =>
      intro j hj hc
      obtain ⟨hr, hn, -⟩ := lemmaE1 (I := G3 hpP defQ P B) rfl h₁
      have hf := Reach.frame h₁
      rcases hst.pool_cases j with heq | ⟨i, q, dest, t, hq, ha, hsd, hd, ht, hta, hts, hadj,
        hus, hq', hb'⟩
      · rw [heq]; exact ih j hj hc
      by_cases hji : j = i
      · subst hji
        have hjt : j ≠ t := by rintro rfl; rw [hsd] at hts; cases hts
        have hjQ : j ∈ s₁.Q := by simp [State.Q, hq]
        have hp0 := fresh_of_Q (I := G3 hpP defQ P B) rfl h₁ j (by simpa using hj) hjQ
        rw [G3.init_player hα hj hc] at hp0
        simp only at hp0
        obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
        simp only [G3.n_eq] at hg ⊢
        rw [hus]
        rcases resolveAttack_attacker_pool (us := s₁.units) (dest := dest) hjt with
          he | ⟨tg, hty, hle, h1, he⟩
        · rw [he, hp0]; omega
        · rw [he, hp0]
          have hty' : tg.type = qtype defQ := by
            rw [hty, hf.type, G3.k_eq, G3.init_enemy hg]
          have hpl : tg.pool ≤ 1 * 3 := by
            have := hf.pool ((G3 hpP defQ P B).k + g)
            rw [G3.k_eq, G3.init_enemy hg] at this
            rw [G3.k_eq] at hle
            simp only at this; omega
          obtain ⟨-, htyj⟩ := G3.player_of_alive hα h₁ hj ha
          have hb := Prop11.blow_le (C := qtype defQ) (c := 1) (a := tg)
            (tg := { activate (s₁.units j) with hex := dest }) hty' (by simp [qtype])
            (by simp [qtype]) h1 (by simpa [qtype] using hpl)
            (by simp only [activate]; rw [htyj]; simp [qtype, ptype])
          have hb' : blow tg { activate (s₁.units j) with hex := dest } ≤ 1 := by
            simpa [qtype] using hb
          omega
      · have hjt : j ≠ t := by
          rintro rfl
          rw [hf.side, initUnits_side_of_lt (by simpa using hj)] at hts; cases hts
        rw [hus, resolveAttack_of_ne hji hjt]; exact ih j hj hc
  intro j hj hc
  have hk := key j hj hc
  have hup := (Reach.frame hs).pool j
  rw [G3.init_player hα hj hc] at hup
  simp only at hup
  have hty := (Reach.frame hs).type j
  rw [G3.init_player hα hj hc] at hty
  refine ⟨?_, ?_, fun hjQ => ?_, hk⟩
  · unfold Stack.alive
    have : 2 * (α j).count ≤ (α j).count * hpP := by nlinarith
    omega
  · unfold Stack.count
    rw [hty]; simp only [ptype]
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]; omega
  · have := fresh_of_Q (I := G3 hpP defQ P B) rfl hs j (by simpa using hj) hjQ
    rw [this, G3.init_player hα hj hc]

end T3

/-! ## Value destroyed -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

/-- The dead enemies of a position. -/
def dead (P : X3C) (s : State) : Finset ℕ :=
  (Finset.range P.n).filter (fun g => (s.units (3 * P.q + g)).pool = 0)

theorem one_eq {g : ℕ} (hg : g < (G3 hpP defQ P B).n) : ((G3 hpP defQ P B).enemy g).count = 1 := by
  simp only [G3.n_eq] at hg; rw [G3.enemy_eq hg]

/-- Value destroyed = number of dead enemies. -/
theorem destroyed_eq {s : State} (hs : Reach (G3 hpP defQ P B) α s) :
    destroyed (G3 hpP defQ P B) s = (dead P s).card := by
  rw [destroyed_single (fun g hg => one_eq hg)
    (fun g hg => by simp only [G3.n_eq] at hg; rw [G3.enemy_eq hg]; simp [qtype])
    (Reach.frame hs)]
  simp only [G3.n_eq, G3.k_eq, dead, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro g hg
  rw [G3.enemy_eq (Finset.mem_range.mp hg)]
  rfl

theorem hp_eq {g : ℕ} (hg : g < P.n) : ((G3 hpP defQ P B).enemy g).type.hp = 3 := by
  rw [G3.enemy_eq hg]; rfl

end T3

/-! ## Lemma D.6 (budget) -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

/-- The blow predicate of Lemma D.6: `b ≤ c_j`, with equality only for `c_j = 1`. -/
def BdD6 (α : ℕ → SlotAlloc) (j b : ℕ) : Prop :=
  1 ≤ (α j).count ∧ b ≤ (α j).count ∧ (b = (α j).count → (α j).count = 1)

theorem hypD6 (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) (hα : Feasible (G3 hpP defQ P B) α) :
    LedgerHyp (G3 hpP defQ P B) α (fun _ _ => True) (BdD6 α) := by
  intro s τ β hs _ i q hq ha hsd g hg dest _ _ _
  have hi : i < 3 * P.q := by
    have := initUnits_side_player (I := G3 hpP defQ P B) (α := α) (i := i)
      (by rw [← (Reach.frame hs).side]; exact hsd)
    simpa using this
  have hiQ : i ∈ s.Q := by simp [State.Q, hq]
  simp only [G3.n_eq] at hg
  obtain ⟨hc, -, -, -⟩ := attacker hhp hα hs hi hiQ ha
  obtain ⟨Δ, hΔ, hb⟩ := blow_eq hhp hα hs hi hiQ ha hg dest
  simp only [G3.k_eq]
  rw [hb]
  have := blow_resource (c := (α i).count) (c' := (α i).count) (Δ := Δ) (by omega) le_rfl hc
  exact ⟨trivial, hc, this⟩

/-- **Lemma D.6 (Budget).** With `def(Q) ≥ 2`, in every position of round 1 at most `q`
enemies are dead.  If exactly `q` are dead, every slot holds exactly one creature, every slot's
stack struck a dead enemy, and every dead enemy has exactly three strikers (the strike record
`τ`).  No geometry is used. -/
theorem lemmaD6 (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) (hα : Feasible (G3 hpP defQ P B) α)
    {s : State} (hs : Reach (G3 hpP defQ P B) α s) :
    (dead P s).card ≤ P.q ∧ ((dead P s).card = P.q →
      (∀ j < 3 * P.q, (α j).count = 1) ∧ ∃ τ : ℕ → Option ℕ,
        (∀ j < 3 * P.q, ∃ g ∈ dead P s, τ j = some g) ∧
        ∀ g ∈ dead P s, (strikers (G3 hpP defQ P B) τ g).card = 3) := by
  obtain ⟨τ, β, hL⟩ := ledgerB (I := G3 hpP defQ P B) rfl (fun g hg => one_eq hg)
    (hypD6 hhp hdef hα) hs
  set I := G3 hpP defQ P B with hIdef
  set K := dead P s with hKdef
  set c : ℕ → ℕ := fun j => (α j).count with hcdef
  have hKn : ∀ g ∈ K, g < P.n := fun g hg => Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  -- each dead enemy: `Σ β ≥ 3` over its strikers, hence `Σ c ≥ 3`
  have hres : ∀ g ∈ K, 3 ≤ ∑ j ∈ strikers I τ g, c j ∧
      (∑ j ∈ strikers I τ g, c j = 3 →
        (strikers I τ g).card = 3 ∧ ∀ j ∈ strikers I τ g, c j = 1) := by
    intro g hg
    have hgn := hKn g hg
    have h0 : (s.units (3 * P.q + g)).pool = 0 := (Finset.mem_filter.mp hg).2
    have hpool := hL.pool g (by rw [hIdef, G3.n_eq]; exact hgn)
    rw [G3.k_eq, h0, hp_eq hgn] at hpool
    have hbd : ∀ j ∈ strikers I τ g, BdD6 α j (β j) := fun j hj =>
      (hL.acted j g (strikers_spec hj)).2.2.2.2
    exact resource _ c β (fun j hj => (hbd j hj).2.1) (fun j hj => (hbd j hj).2.2) (by omega)
  have hdisj : ((K : Set ℕ)).PairwiseDisjoint (strikers I τ) :=
    fun g _ g' _ hne => Ledger.disjoint (I := I) (τ := τ) g g' hne
  set U := K.biUnion (strikers I τ) with hUdef
  have hUsub : U ⊆ Finset.range (3 * P.q) := by
    intro j hj
    obtain ⟨g, -, hjg⟩ := Finset.mem_biUnion.mp hj
    have := strikers_sub (I := I) τ g hjg
    simpa [hIdef] using this
  have hsumU : ∑ j ∈ U, c j = ∑ g ∈ K, ∑ j ∈ strikers I τ g, c j := Finset.sum_biUnion hdisj
  have hU3q : ∑ j ∈ U, c j ≤ 3 * P.q :=
    (Finset.sum_le_sum_of_subset hUsub).trans (G3.sum_count_le hα)
  have h3K : ∑ g ∈ K, 3 ≤ ∑ g ∈ K, ∑ j ∈ strikers I τ g, c j :=
    Finset.sum_le_sum (fun g hg => (hres g hg).1)
  rw [Finset.sum_const, smul_eq_mul] at h3K
  refine ⟨by omega, fun hKq => ?_⟩
  -- tightness
  have htight : ∑ g ∈ K, ∑ j ∈ strikers I τ g, c j = ∑ g ∈ K, 3 := by
    rw [Finset.sum_const, smul_eq_mul]; omega
  have heach : ∀ g ∈ K, ∑ j ∈ strikers I τ g, c j = 3 := fun g hg =>
    (Finset.sum_eq_sum_iff_of_le (fun g hg => (hres g hg).1)).mp htight.symm g hg |>.symm
  have hcard3 : ∀ g ∈ K, (strikers I τ g).card = 3 := fun g hg => ((hres g hg).2 (heach g hg)).1
  have hone : ∀ g ∈ K, ∀ j ∈ strikers I τ g, c j = 1 := fun g hg => ((hres g hg).2 (heach g hg)).2
  have hUcard : U.card = 3 * P.q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard3, Finset.sum_const, smul_eq_mul,
      hKq, mul_comm]
  have hUeq : U = Finset.range (3 * P.q) :=
    Finset.eq_of_subset_of_card_le hUsub (by rw [hUcard, Finset.card_range])
  have hcov : ∀ j < 3 * P.q, ∃ g ∈ K, j ∈ strikers I τ g := by
    intro j hj
    have : j ∈ U := by rw [hUeq]; exact Finset.mem_range.mpr hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp this
    exact ⟨g, hg, hjg⟩
  refine ⟨fun j hj => ?_, τ, fun j hj => ?_, hcard3⟩
  · obtain ⟨g, hg, hjg⟩ := hcov j hj; exact hone g hg j hjg
  · obtain ⟨g, hg, hjg⟩ := hcov j hj; exact ⟨g, hg, strikers_spec hjg⟩

end T3

/-! ## Lemma D.7 (confinement) -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

/-- The confined ledger: every recorded strike is by a slot `e` on an `E_S` with `S ∋ e`, and
every blow is `1`. -/
abbrev LedgerC (hpP defQ : ℕ) (P : X3C) (B : X3CBoard) (s : State) (τ : ℕ → Option ℕ)
    (β : ℕ → ℕ) : Prop :=
  LedgerB (G3 hpP defQ P B) (fun j g => j ∈ P.set g) (fun _ b => b = 1) s τ β

/-- Under the confined ledger, a dead enemy's strikers are exactly the three slots of its set. -/
theorem strikers_eq_of_dead (hP : P.WF) {s : State} {τ : ℕ → Option ℕ} {β : ℕ → ℕ}
    (hL : LedgerC hpP defQ P B s τ β) {S : ℕ} (hS : S < P.n)
    (h0 : (s.units (3 * P.q + S)).pool = 0) :
    strikers (G3 hpP defQ P B) τ S = P.set S := by
  have hpool := hL.pool S (by simpa using hS)
  rw [G3.k_eq, h0, hp_eq hS] at hpool
  have hβ : ∀ j ∈ strikers (G3 hpP defQ P B) τ S, β j = 1 := fun j hj =>
    (hL.acted j S (strikers_spec hj)).2.2.2.2
  rw [Finset.sum_congr rfl hβ, Finset.sum_const, smul_eq_mul, mul_one] at hpool
  have hsubS : strikers (G3 hpP defQ P B) τ S ⊆ P.set S := fun j hj =>
    (hL.acted j S (strikers_spec hj)).2.2.2.1
  exact Finset.eq_of_subset_of_card_le hsubS (by rw [hP.card S hS]; omega)

/-- **The heart of Lemma D.7**: under the confined ledger, while slot `e` has not taken its
terminal action, every `E_S` with `S ∋ e` is alive (a dead one would have the three slots of
`S`, `e` among them, as recorded strikers). -/
theorem alive_of_ledgerC (hP : P.WF) {s : State} {τ : ℕ → Option ℕ} {β : ℕ → ℕ}
    (hL : LedgerC hpP defQ P B s τ β) {e : ℕ} (heQ : e ∈ s.Q) :
    ∀ S < P.n, e ∈ P.set S → (s.units (3 * P.q + S)).alive := by
  intro S hS heS
  by_contra hdead
  have h0 : (s.units (3 * P.q + S)).pool = 0 := by unfold Stack.alive at hdead; omega
  have heq := strikers_eq_of_dead hP hL hS h0
  have he' : e ∈ strikers (G3 hpP defQ P B) τ S := heq ▸ heS
  exact (hL.acted e S (strikers_spec he')).2.1 heQ

theorem hypD7 (hP : P.WF) (hI : B.InvCore P) (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ)
    (hα : Feasible (G3 hpP defQ P B) α) (hc1 : ∀ j < 3 * P.q, (α j).count ≤ 1) :
    LedgerHyp (G3 hpP defQ P B) α (fun j g => j ∈ P.set g) (fun _ b => b = 1) := by
  intro s τ β hs hL i q hq ha hsd g hg dest hd _ hadj
  have hi : i < 3 * P.q := by
    have := initUnits_side_player (I := G3 hpP defQ P B) (α := α) (i := i)
      (by rw [← (Reach.frame hs).side]; exact hsd)
    simpa using this
  have hiQ : i ∈ s.Q := by simp [State.Q, hq]
  simp only [G3.n_eq] at hg
  obtain ⟨-, -, -, hhex⟩ := attacker hhp hα hs hi hiQ ha
  have halive := alive_of_ledgerC hP hL hiQ
  have hhex' : (s.units i).hex ∈ B.R i := hhex ▸ hI.pMem i hi
  have henemy : ∀ g < P.n, (s.units (3 * P.q + g)).hex = B.z g := fun g hg => G3.hex_enemy hs hg
  rw [G3.k_eq, henemy g hg] at hadj
  obtain ⟨hig, -⟩ := X3CBoard.dock_of_confined hI hi hi hhex' henemy halive hd hg hadj
  refine ⟨hig, ?_⟩
  obtain ⟨Δ, hΔ, hb⟩ := blow_eq hhp hα hs hi hiQ ha hg dest
  rw [G3.k_eq, hb]
  exact damage_le_one_eq (by omega) (hc1 i hi)

/-- **The confined ledger exists in every position of round 1**, for every allocation with at
most one creature per slot and `def(Q) ≥ att(P)`. -/
theorem confinedLedger (hP : P.WF) (hI : B.InvCore P) (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ)
    (hα : Feasible (G3 hpP defQ P B) α) (hc1 : ∀ j < 3 * P.q, (α j).count ≤ 1) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) : ∃ τ β, LedgerC hpP defQ P B s τ β :=
  ledgerB rfl (fun _ hg => one_eq hg) (hypD7 hP hI hhp hdef hα hc1) hs

/-- **Lemma D.7 (Confinement).** With at most one creature per slot (the situation of Lemma D.6
at `t = q`, but not only there): while slot `e` has not taken its terminal action, every `E_S`
with `S ∋ e` is alive; consequently it can strike only enemies `E_S` with `S ∋ e`, from
`d_S^e`. -/
theorem lemmaD7 (hP : P.WF) (hI : B.InvCore P) (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ)
    (hα : Feasible (G3 hpP defQ P B) α) (hc1 : ∀ j < 3 * P.q, (α j).count ≤ 1) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) {e : ℕ} (he : e < 3 * P.q) (heQ : e ∈ s.Q) :
    (∀ S < P.n, e ∈ P.set S → (s.units (3 * P.q + S)).alive) ∧
    ∀ t, CanStrike (G3 hpP defQ P B) s.units e t → ∃ g < P.n, e ∈ P.set g ∧
      t = 3 * P.q + g ∧ ∀ dest ∈ reachOf (G3 hpP defQ P B) s.units e,
        Hex.Adj dest (B.z g) → dest = B.d g e := by
  obtain ⟨τ, β, hL⟩ := confinedLedger hP hI hhp hdef hα hc1 hs
  have halive := alive_of_ledgerC hP hL heQ
  refine ⟨halive, fun t ⟨ht, hts, hta, dest, hd, hadj⟩ => ?_⟩
  have hf := Reach.frame hs
  obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
  simp only [G3.k_eq, G3.n_eq] at hg hadj ⊢
  have henemy : ∀ g < P.n, (s.units (3 * P.q + g)).hex = B.z g := fun g hg => G3.hex_enemy hs hg
  have hal : (s.units e).alive := by
    have := (Reach.mem_Q (I := G3 hpP defQ P B) rfl hs heQ).2
    have hc : 0 < (α e).count := by
      by_contra h0
      rw [initUnits_player (by simpa using he)] at this
      unfold Stack.alive at this; simp [show (α e).count = 0 by omega] at this
    rw [Stack.alive, fresh_of_Q (I := G3 hpP defQ P B) rfl hs e (by simpa using he) heQ,
      G3.init_player hα he hc]
    exact Nat.mul_pos hc hhp
  obtain ⟨-, -, -, hhex⟩ := attacker hhp hα hs he heQ hal
  have hhex' : (s.units e).hex ∈ B.R e := hhex ▸ hI.pMem e he
  rw [henemy g hg] at hadj
  refine ⟨g, hg, (X3CBoard.dock_of_confined hI he he hhex' henemy halive hd hg hadj).1, rfl,
    fun dest' hd' hadj' => (X3CBoard.dock_of_confined hI he he hhex' henemy halive hd' hg
      hadj').2⟩

/-- **The no-direction core** (Lemmas D.7 and D.9): with at most one creature per slot, a
position with at least `q` dead enemies yields an exact cover — the dead enemies' sets. -/
theorem exactCover_of_confined (hP : P.WF) (hI : B.InvCore P) (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ)
    (hα : Feasible (G3 hpP defQ P B) α) (hc1 : ∀ j < 3 * P.q, (α j).count ≤ 1) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) (hW : P.q ≤ (dead P s).card) : P.ExactCover := by
  obtain ⟨τ, β, hL⟩ := confinedLedger hP hI hhp hdef hα hc1 hs
  have hKn : ∀ g ∈ dead P s, g < P.n := fun g hg =>
    Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hstr : ∀ g ∈ dead P s, strikers (G3 hpP defQ P B) τ g = P.set g := fun g hg =>
    strikers_eq_of_dead hP hL (hKn g hg) (Finset.mem_filter.mp hg).2
  have hdis : ∀ g ∈ dead P s, ∀ g' ∈ dead P s, g ≠ g' → Disjoint (P.set g) (P.set g') := by
    intro g hg g' hg' hne
    rw [← hstr g hg, ← hstr g' hg']
    exact Ledger.disjoint (I := G3 hpP defQ P B) (τ := τ) g g' hne
  exact ⟨dead P s, hKn, hdis, X3C.cover_of_card hP hKn hdis hW⟩

/-- **Lemma D.9 (yes ⟹ exact cover).** -/
theorem lemmaD9 (hP : P.WF) (hI : B.InvCore P) (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ)
    (h : ArmyAllocation (G3 hpP defQ P B)) : P.ExactCover := by
  obtain ⟨α, hα, s, hs, -, hW⟩ := h
  rw [destroyed_eq hs, G3.W_eq] at hW
  obtain ⟨hle, htight⟩ := lemmaD6 hhp hdef hα hs
  have hc1 := (htight (le_antisymm hle hW)).1
  exact exactCover_of_confined hP hI hhp (by omega) hα (fun j hj => (hc1 j hj).le) hs hW

/-- **The winning allocation is unique** (Lemma D.6): on every instance, an allocation with a
play destroying `q` holds exactly one creature in every slot. -/
theorem winning_unique (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) (hα : Feasible (G3 hpP defQ P B) α)
    {s : State} (hs : Reach (G3 hpP defQ P B) α s) (hW : P.q ≤ destroyed (G3 hpP defQ P B) s) :
    ∀ j < 3 * P.q, (α j).count = 1 := by
  rw [destroyed_eq hs] at hW
  obtain ⟨hle, htight⟩ := lemmaD6 hhp hdef hα hs
  exact (htight (le_antisymm hle hW)).1

end T3

/-! ## The witness run (Lemma D.8, and the negative control) -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

/-- The allocation "`c j` creatures of `P` in slot `j`". -/
def αc (c : ℕ → ℕ) : ℕ → SlotAlloc := fun j => ⟨0, c j⟩

/-- The all-ones allocation of Lemma D.8 and Corollary 3.1. -/
def α1 : ℕ → SlotAlloc := αc (fun _ => 1)

/-- The slots planned to strike `E_g`. -/
def att (P : X3C) (c tgt : ℕ → ℕ) (g : ℕ) : Finset ℕ :=
  (Finset.range (3 * P.q)).filter (fun j => 0 < c j ∧ tgt j = g)

/-- The nominal undefended blow of `c` creatures. -/
def bl (defQ c : ℕ) : ℕ := damage c 1 (1 - (defQ : ℤ))

/-- A strike plan: slot `j` (if occupied) strikes `E_{tgt j}`, a set containing `j`, and the
planned blows on each enemy total at most its `3` hit points. -/
structure Plan (P : X3C) (defQ : ℕ) (c tgt : ℕ → ℕ) : Prop where
  tgt_lt : ∀ j < 3 * P.q, 0 < c j → tgt j < P.n
  mem : ∀ j < 3 * P.q, 0 < c j → j ∈ P.set (tgt j)
  budget : ∀ g < P.n, ∑ j ∈ att P c tgt g, bl defQ (c j) ≤ 3
  stock : ∑ j ∈ Finset.range (3 * P.q), c j ≤ 3 * P.q

theorem αc_feasible {c : ℕ → ℕ} (hst : ∑ j ∈ Finset.range (3 * P.q), c j ≤ 3 * P.q) :
    Feasible (G3 hpP defQ P B) (αc c) := by
  refine ⟨fun j _ _ => by simp [αc], fun t ht => ?_⟩
  have : t = 0 := by simpa using ht
  subst this
  simp only [αc, G3.k_eq]
  simpa [G3] using hst

/-- The planned slots that have already struck (are no longer in the queue `L`). -/
def done (P : X3C) (c tgt : ℕ → ℕ) (g : ℕ) (L : List ℕ) : Finset ℕ :=
  (att P c tgt g).filter (fun j => j ∉ L)

/-- Invariant of the witness run in the `NORMAL` phase. -/
structure WP (hpP defQ : ℕ) (P : X3C) (B : X3CBoard) (c tgt : ℕ → ℕ) (s : State) : Prop where
  reach : Reach (G3 hpP defQ P B) (αc c) s
  phase : s.phase = .normal
  bucket : ∀ i ∈ s.bucket, (s.units i).side = .enemy
  seated : ∀ j < 3 * P.q, 0 < c j → j ∉ s.queue → (s.units j).hex = B.d (tgt j) j
  epool : ∀ g < P.n, (s.units (3 * P.q + g)).pool =
    3 - ∑ j ∈ done P c tgt g s.queue, bl defQ (c j)

theorem mem_initQueue_player (hhp : 1 ≤ hpP) {c : ℕ → ℕ}
    (hst : ∑ j ∈ Finset.range (3 * P.q), c j ≤ 3 * P.q) {j : ℕ} (hj : j < 3 * P.q)
    (hc : 0 < c j) : j ∈ (initState (G3 hpP defQ P B) (αc c)).queue := by
  apply Prop11.mem_initQueue (by simp; omega)
  rw [G3.init_player (αc_feasible hst) hj hc]
  unfold Stack.alive; simp only [αc]; exact Nat.mul_pos hc hhp

theorem WP.init (hhp : 1 ≤ hpP) {c tgt : ℕ → ℕ} (hpl : Plan P defQ c tgt) :
    WP hpP defQ P B c tgt (initState (G3 hpP defQ P B) (αc c)) where
  reach := .refl
  phase := rfl
  bucket := by simp [initState]
  seated j hj hc hq := absurd (mem_initQueue_player hhp hpl.stock hj hc) hq
  epool g hg := by
    have : done P c tgt g (initState (G3 hpP defQ P B) (αc c)).queue = ∅ := by
      apply Finset.filter_false_of_mem
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      rw [not_not]
      exact mem_initQueue_player hhp hpl.stock (Finset.mem_range.mp hj'.1) hj'.2.1
    rw [this, Finset.sum_empty]
    simp only [initState]; rw [G3.init_enemy hg]; rfl

/-- The blow of an occupied slot in the `NORMAL` phase: the nominal undefended `bl`. -/
theorem blow_normal (hhp : 1 ≤ hpP) (hα : Feasible (G3 hpP defQ P B) α) {s : State}
    (hs : Reach (G3 hpP defQ P B) α s) (hph : s.phase = .normal) {i : ℕ} (hi : i < 3 * P.q)
    (hiQ : i ∈ s.Q) (ha : (s.units i).alive) {g : ℕ} (hg : g < P.n) (dest : Hex) :
    blow { activate (s.units i) with hex := dest } (s.units (3 * P.q + g)) =
      bl defQ (α i).count := by
  obtain ⟨-, hty, hcnt, -⟩ := attacker hhp hα hs hi hiQ ha
  have htg : (s.units (3 * P.q + g)).type = qtype defQ := by
    rw [(Reach.frame hs).type, G3.init_enemy hg]
  have hdef := normal_undefended (I := G3 hpP defQ P B) rfl hs hph (g := g) (by simpa using hg)
  rw [G3.k_eq] at hdef
  unfold blow bl
  have hc : ({ activate (s.units i) with hex := dest } : Stack).count = (α i).count := by
    rw [← hcnt]; rfl
  rw [hc]
  simp only [activate, hty, ptype, Stack.defEff, hdef, htg, qtype]
  simp

theorem WP.step (hhp : 1 ≤ hpP) (hI : B.InvCore P) {c tgt : ℕ → ℕ} (hpl : Plan P defQ c tgt)
    {s : State} (hw : WP hpP defQ P B c tgt s) {i : ℕ} {q : List ℕ} (hq : s.queue = i :: q) :
    ∃ s', Step (G3 hpP defQ P B) s s' ∧ WP hpP defQ P B c tgt s' ∧ s'.queue = q := by
  have hs := hw.reach
  have hα : Feasible (G3 hpP defQ P B) (αc c) := αc_feasible hpl.stock
  obtain ⟨-, hn, hxE⟩ := lemmaE1 (I := G3 hpP defQ P B) rfl hs
  have hf := Reach.frame hs
  have hnq := head_not_mem_after hq hn
  have hmem : ∀ j, j ∈ q ↔ j ∈ s.queue ∧ j ≠ i := by
    intro j; rw [hq, List.mem_cons]
    constructor
    · intro hj; exact ⟨Or.inr hj, fun e => hnq (e ▸ List.mem_append_left _ hj)⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
  -- the `done` set of an enemy is unchanged unless `i` is one of its planned strikers
  have hdone_ne : ∀ g, i ∉ att P c tgt g → done P c tgt g q = done P c tgt g s.queue := by
    intro g hig
    apply Finset.filter_congr
    intro j hj
    rw [hmem]
    constructor
    · intro h h'; exact h ⟨h', fun e => hig (e ▸ hj)⟩
    · rintro h ⟨h', -⟩; exact h h'
  by_cases ha : (s.units i).alive
  · rcases hside : (s.units i).side with _ | _
    · -- a player slot strikes its planned target from its docking
      have hi : i < 3 * P.q := by
        have := initUnits_side_player (I := G3 hpP defQ P B) (α := αc c) (i := i)
          (by rw [← hf.side]; exact hside)
        simpa using this
      have hiQ : i ∈ s.Q := by simp [State.Q, hq]
      obtain ⟨hc, hty, -, hhex⟩ := attacker hhp hα hs hi hiQ ha
      simp only [αc] at hc
      have hg : tgt i < P.n := hpl.tgt_lt i hi hc
      have hig : i ∈ P.set (tgt i) := hpl.mem i hi hc
      have hiatt : i ∈ att P c tgt (tgt i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hc, rfl⟩
      have hidone : i ∉ done P c tgt (tgt i) s.queue := by
        intro h; exact (Finset.mem_filter.mp h).2 (by rw [hq]; exact List.mem_cons_self)
      -- the target is alive: the other planned blows total at most `3 − bl(c_i) ≤ 2`
      have hsum : ∑ j ∈ done P c tgt (tgt i) s.queue, bl defQ (c j) + bl defQ (c i) ≤ 3 := by
        have hsub : insert i (done P c tgt (tgt i) s.queue) ⊆ att P c tgt (tgt i) :=
          Finset.insert_subset hiatt (Finset.filter_subset _ _)
        have := (Finset.sum_le_sum_of_subset hsub).trans (hpl.budget _ hg)
        rwa [Finset.sum_insert hidone, add_comm] at this
      have hb1 : 1 ≤ bl defQ (c i) := one_le_damage _ _ _
      have hepool := hw.epool _ hg
      have hta : (s.units (3 * P.q + tgt i)).alive := by unfold Stack.alive; rw [hepool]; omega
      -- every hex of `R_i` is free for slot `i`
      have hfreeR : ∀ x ∈ B.R i, free (G3 hpP defQ P B) s.units i x := by
        intro x hx
        rw [G3.free_iff]
        refine ⟨(hI.rOpen i hi x hx).1, fun i' hi' hne hal hxe => ?_⟩
        by_cases hik : i' < 3 * P.q
        · obtain ⟨hc', -⟩ := G3.player_of_alive hα hs hik hal
          simp only [αc] at hc'
          have hin : (s.units i').hex ∈ B.R i' := by
            by_cases hq' : i' ∈ s.queue
            · rw [hxE i' (List.mem_append_left _ hq'),
                G3.init_player hα hik (by simpa [αc] using hc')]
              exact hI.pMem i' hik
            · rw [hw.seated i' hik hc' hq']
              exact hI.dMem _ (hpl.tgt_lt i' hik hc') i' (hpl.mem i' hik hc')
          exact Finset.disjoint_left.mp (hI.rDisj i' hik i hi hne) hin (hxe ▸ hx)
        · obtain ⟨g', hg', rfl⟩ : ∃ g' < P.n, i' = 3 * P.q + g' :=
            ⟨i' - 3 * P.q, by omega, by omega⟩
          rw [G3.hex_enemy hs hg'] at hxe
          exact (hI.rOpen i hi x hx).2 g' hg' hxe.symm
      have hd : B.d (tgt i) i ∈ reachOf (G3 hpP defQ P B) s.units i := by
        unfold reachOf
        rw [hty, hhex]
        exact mem_reach_of_rtg (hI.pMem i hi) (hI.rConn i hi _ (hI.dMem _ hg i hig)) hfreeR
          (hI.i4 i hi)
      have hadj : Hex.Adj (B.d (tgt i) i) (s.units (3 * P.q + tgt i)).hex := by
        rw [G3.hex_enemy hs hg]; exact hI.dAdj _ hg i hig
      have hit : i ≠ 3 * P.q + tgt i := by omega
      have hstep : Step (G3 hpP defQ P B) s
          { s with units := resolveAttack s.units i (3 * P.q + tgt i) (B.d (tgt i) i),
                   queue := q } :=
        Step.playerAttack hq ha hside hd (by simp; omega) hta (G3.side_enemy hs hg) hadj
      refine ⟨_, hstep, ⟨hs.tail hstep, hw.phase, ?_, ?_, ?_⟩, rfl⟩
      · intro x hx; rw [hstep.side]; exact hw.bucket x hx
      · intro j hj hcj hjq
        simp only at hjq ⊢
        by_cases hji : j = i
        · subst hji; rw [resolveAttack_self_hex hit]
        · rw [resolveAttack_hex_of_ne hji]
          exact hw.seated j hj hcj (fun h => hjq ((hmem j).mpr ⟨h, hji⟩))
      · intro g' hg'
        simp only
        by_cases hgg : g' = tgt i
        · subst hgg
          rw [resolveAttack_pool_target hit, hepool,
            blow_normal hhp hα hs hw.phase hi hiQ ha hg (B.d (tgt i) i)]
          have hins : done P c tgt (tgt i) q = insert i (done P c tgt (tgt i) s.queue) := by
            ext j
            simp only [done, Finset.mem_filter, Finset.mem_insert, hmem, not_and, not_not]
            constructor
            · rintro ⟨hj, h⟩
              by_cases hji : j = i
              · exact Or.inl hji
              · exact Or.inr ⟨hj, fun h' => hji (h h')⟩
            · rintro (rfl | ⟨hj, h⟩)
              · exact ⟨hiatt, fun _ => rfl⟩
              · exact ⟨hj, fun h' => absurd h' h⟩
          rw [hins, Finset.sum_insert hidone, Nat.sub_sub, add_comm (bl defQ (c i))]
          rfl
        · have hig' : i ∉ att P c tgt g' := by
            intro h; exact hgg (Finset.mem_filter.mp h).2.2.symm
          rw [resolveAttack_of_ne (by omega) (by omega), hw.epool g' hg', hdone_ne g' hig']
    · -- an enemy stack: `(‡)` makes it `WAIT`
      have hstep : Step (G3 hpP defQ P B) s { s with
          units := update s.units i (activate (s.units i)), queue := q,
          bucket := s.bucket ++ [i] } := Step.enemyWait hw.phase hq ha hside
      have hik : ∀ j < 3 * P.q, j ≠ i := by
        intro j hj e; subst e
        rw [hf.side, initUnits_side_of_lt (by simpa using hj)] at hside; cases hside
      have hnatt : ∀ g, i ∉ att P c tgt g := fun g h =>
        hik i (Finset.mem_range.mp (Finset.mem_filter.mp h).1) rfl
      refine ⟨_, hstep, ⟨hs.tail hstep, hw.phase, ?_, ?_, ?_⟩, rfl⟩
      · intro x hx
        rw [hstep.side]
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw.bucket x hx
        · exact hside
      · intro j hj hcj hjq
        simp only at hjq ⊢
        rw [update_of_ne (hik j hj)]
        exact hw.seated j hj hcj (fun h => hjq ((hmem j).mpr ⟨h, hik j hj⟩))
      · intro g' hg'
        simp only
        rw [hdone_ne g' (hnatt g'), ← hw.epool g' hg']
        simp only [update_apply]
        split_ifs with he
        · rw [he]; simp [activate]
        · rfl
  · -- a dead stack is skipped; it is not an occupied slot
    have hstep : Step (G3 hpP defQ P B) s { s with queue := q } := Step.skip hq ha
    have hnatt : ∀ g, i ∉ att P c tgt g := by
      intro g h
      have hh := Finset.mem_filter.mp h
      have hi := Finset.mem_range.mp hh.1
      have hiQ : i ∈ s.Q := by simp [State.Q, hq]
      have := fresh_of_Q (I := G3 hpP defQ P B) rfl hs i (by simpa using hi) hiQ
      rw [G3.init_player hα hi (by simpa [αc] using hh.2.1)] at this
      exact ha (by unfold Stack.alive; rw [this]; simp only [αc]; exact Nat.mul_pos hh.2.1 hhp)
    refine ⟨_, hstep, ⟨hs.tail hstep, hw.phase, hw.bucket, ?_, ?_⟩, rfl⟩
    · intro j hj hcj hjq
      have hji : j ≠ i := fun e => hnatt (tgt j) (e ▸ Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hj, hcj, rfl⟩)
      exact hw.seated j hj hcj (fun h => hjq ((hmem j).mpr ⟨h, hji⟩))
    · intro g' hg'
      simp only
      rw [hdone_ne g' (hnatt g')]; exact hw.epool g' hg'

theorem WP.run (hhp : 1 ≤ hpP) (hI : B.InvCore P) {c tgt : ℕ → ℕ} (hpl : Plan P defQ c tgt) :
    ∀ (L : List ℕ) (s : State), WP hpP defQ P B c tgt s → s.queue = L →
      ∃ s', Relation.ReflTransGen (Step (G3 hpP defQ P B)) s s' ∧
        WP hpP defQ P B c tgt s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    obtain ⟨s1, h1, hw1, hq1⟩ := hw.step hhp hI hpl hq
    obtain ⟨s2, h2, hw2, hq2⟩ := WP.run hhp hI hpl q s1 hw1 hq1
    exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩

/-- **The witness run.** For every strike plan there is a complete play in which each enemy has
lost exactly the planned blows. -/
theorem witness (hhp : 1 ≤ hpP) (hI : B.InvCore P) {c tgt : ℕ → ℕ} (hpl : Plan P defQ c tgt) :
    ∃ s, Reach (G3 hpP defQ P B) (αc c) s ∧ Done s ∧
      ∀ g < P.n, (s.units (3 * P.q + g)).pool = 3 - ∑ j ∈ att P c tgt g, bl defQ (c j) := by
  obtain ⟨s1, h1, hw1, hq1⟩ := WP.run hhp hI hpl _ _ (WP.init hhp hpl) rfl
  obtain ⟨s2, h2, hd2⟩ := exists_done (G3 hpP defQ P B) s1
  have hz : Frozen s1 :=
    ⟨(lemmaE1 (I := G3 hpP defQ P B) rfl hw1.reach).1, Or.inl ⟨hw1.phase, hq1, hw1.bucket⟩⟩
  have hfr := hz.run h2
  refine ⟨s2, hw1.reach.trans h2, hd2, fun g hg => ?_⟩
  rw [(hfr _).1, hw1.epool g hg]
  have : done P c tgt g s1.queue = att P c tgt g := by
    apply Finset.filter_true_of_mem
    intro j _; rw [hq1]; exact List.not_mem_nil
  rw [this]

end T3

/-! ## Lemma D.8, Theorem 3, Corollary 3.1 -/

namespace T3

variable {hpP defQ : ℕ} {P : X3C} {B : X3CBoard}

open Classical in
/-- The member of the cover `K` containing `e`. -/
noncomputable def coverTgt (P : X3C) (K : Finset ℕ) (e : ℕ) : ℕ :=
  if h : ∃ g ∈ K, e ∈ P.set g then h.choose else 0

theorem coverTgt_spec {K : Finset ℕ} (hcov : ∀ e < 3 * P.q, ∃ g ∈ K, e ∈ P.set g) {e : ℕ}
    (he : e < 3 * P.q) : coverTgt P K e ∈ K ∧ e ∈ P.set (coverTgt P K e) := by
  have h := hcov e he
  unfold coverTgt; rw [dif_pos h]; exact h.choose_spec

theorem coverTgt_eq {K : Finset ℕ}
    (hdis : ∀ g ∈ K, ∀ g' ∈ K, g ≠ g' → Disjoint (P.set g) (P.set g'))
    (hcov : ∀ e < 3 * P.q, ∃ g ∈ K, e ∈ P.set g) {e g : ℕ} (he : e < 3 * P.q) (hg : g ∈ K)
    (heg : e ∈ P.set g) : coverTgt P K e = g := by
  obtain ⟨h1, h2⟩ := coverTgt_spec hcov he
  by_contra hne
  exact Finset.disjoint_left.mp (hdis _ h1 g hg hne) h2 heg

theorem α1_feasible : Feasible (G3 hpP defQ P B) α1 :=
  αc_feasible (by simp)

theorem bl_one (hdef : 1 ≤ defQ) : bl defQ 1 = 1 :=
  damage_le_one_eq (by omega) le_rfl

/-- **Lemma D.8 (yes ⟹ yes)**, with the all-ones allocation: a complete play destroying `q`. -/
theorem lemmaD8 (hP : P.WF) (hI : B.InvCore P) (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ)
    (hX : P.ExactCover) :
    ∃ s, Reach (G3 hpP defQ P B) α1 s ∧ Done s ∧ P.q ≤ destroyed (G3 hpP defQ P B) s := by
  obtain ⟨K, hK, hdis, hcov⟩ := hX
  have hatt : ∀ g < P.n, att P (fun _ => 1) (coverTgt P K) g =
      if g ∈ K then P.set g else ∅ := by
    intro g hg
    ext j
    simp only [att, Finset.mem_filter, Finset.mem_range, zero_lt_one, true_and]
    split_ifs with hgK
    · constructor
      · rintro ⟨hj, rfl⟩; exact (coverTgt_spec hcov hj).2
      · intro hj
        have hj' := hP.sub g hg j hj
        exact ⟨hj', coverTgt_eq hdis hcov hj' hgK hj⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro hj he
      exact hgK (he ▸ (coverTgt_spec hcov hj).1)
  have hpl : Plan P defQ (fun _ => 1) (coverTgt P K) := by
    refine ⟨fun j hj _ => hK _ (coverTgt_spec hcov hj).1, fun j hj _ => (coverTgt_spec hcov hj).2,
      fun g hg => ?_, by simp⟩
    rw [hatt g hg, Finset.sum_congr rfl (fun _ _ => bl_one hdef)]
    split_ifs
    · simp [hP.card g hg]
    · simp
  obtain ⟨s, hs, hd, hpool⟩ := witness (B := B) hhp hI hpl
  refine ⟨s, hs, hd, ?_⟩
  rw [destroyed_eq hs, ← X3C.card_cover hP hK hdis hcov]
  apply Finset.card_le_card
  intro g hgK
  have hg := hK g hgK
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, ?_⟩
  rw [hpool g hg, hatt g hg, if_pos hgK, Finset.sum_congr rfl (fun _ _ => bl_one hdef)]
  simp [hP.card g hg]

end T3

open T3 in
/-- **Theorem 3 under the core invariants** (`X3CBoard.InvCore`, weaker than (I1)–(I4)). -/
theorem theorem3_core (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.InvCore P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) :
    P.ExactCover ↔ ArmyAllocation (G3 hpP defQ P B) := by
  constructor
  · intro hX
    obtain ⟨s, hs, hd, hW⟩ := lemmaD8 (defQ := defQ) (B := B) hP hI hhp (by omega) hX
    exact ⟨α1, α1_feasible, s, hs, hd, by simpa using hW⟩
  · exact lemmaD9 hP hI hhp hdef

/-- **Theorem 3 (modulo the embedding).** For every well-formed `X3C` instance `P` and every
board `B` satisfying (I1)–(I4), with player `hp ≥ 1` and enemy `def ≥ 2` (so that
`att(P) < def(Q)`): `P` has an exact cover iff `G_3(P, B)` is a yes-instance of
`ARMY-ALLOCATION`. -/
theorem theorem3 (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.Inv P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 2 ≤ defQ) :
    P.ExactCover ↔ ArmyAllocation (G3 hpP defQ P B) :=
  theorem3_core P B hP hI.core hhp hdef

/-- **Theorem 3 at the paper's constants** (`hp(P) = 4`, `def(Q) = 27`). -/
theorem theorem3_pub (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.Inv P) :
    P.ExactCover ↔ ArmyAllocation (G3pub P B) :=
  theorem3 P B hP hI (by norm_num) (by norm_num)

open T3 in
/-- **Corollary 3.1 under the core invariants.** -/
theorem cor31_core (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.InvCore P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ) :
    P.ExactCover ↔ ThmF.BattlePlay (G3 hpP defQ P B) α1 := by
  constructor
  · intro hX
    obtain ⟨s, hs, hd, hW⟩ := lemmaD8 hP hI hhp hdef hX
    exact ⟨s, hs, hd, by simpa using hW⟩
  · rintro ⟨s, hs, -, hW⟩
    rw [destroyed_eq hs, G3.W_eq] at hW
    exact exactCover_of_confined hP hI hhp hdef α1_feasible (fun j _ => le_rfl) hs hW

open T3 in
/-- **Corollary 3.1 (fixed allocation).** With one creature in every slot given, `P` has an
exact cover iff some play destroys `q` (`BATTLE-PLAY`).  Valid already for `def(Q) ≥ att(P)`:
with singleton stacks every blow is `1` and the resource lemma is not needed. -/
theorem cor31 (P : X3C) (B : X3CBoard) (hP : P.WF) (hI : B.Inv P) {hpP defQ : ℕ}
    (hhp : 1 ≤ hpP) (hdef : 1 ≤ defQ) :
    P.ExactCover ↔ ThmF.BattlePlay (G3 hpP defQ P B) α1 :=
  cor31_core P B hP hI.core hhp hdef

end Homm3
