import Homm3.BattleFacts
import Homm3.HexGraph
import Homm3.CorridorGame

/-!
# Session 2, target 1. Persistent matching reach (Definition E.8), the metric test
# (Lemma E.9) and the corridor family (Lemma E.10), for an arbitrary instance

Paper: Appendix E, "Proposition 1.1, and what matching reach has to mean".

* `CanStrike I us i t` — "the set of enemies that stack can strike": `t` is a living enemy
  stack with some hex of `i`'s BFS reach (over the free hexes of the position `us`, the
  empty walk included) adjacent to it.  These are exactly the targets for which the
  `playerAttack` step is enabled (`Step.canStrike`).
* `Matching I σ` — `σ` is a bijection from the slots `0 … k−1` onto the enemy stacks
  `0 … n−1`; enemy `j'` has stack id `k + j'`.
* `PMR I σ` — **Definition E.8**: `R = 1`, and for every feasible allocation, in every
  position reachable from its starting position (by legal player actions and `(‡)`), for
  every slot `j` whose stack has not yet taken its terminal action (`j ∈ s.Q`), the enemies
  it can strike are exactly `{E_{σ j}}`.
* `MetricTest I σ` — the hypotheses of **Lemma E.9**: `p_j` adjacent to `e_{σ j}`, and
  `dist(p_j, e_{j'}) > s + 1` for every `j' ≠ σ j` and every speed `s` of an army type (a
  slot's speed depends on the allocation; with one type this is the paper's `s_j`), plus
  "every enemy stack is alive at the start" (Definition 3.1: `count, hp ∈ ℤ_{>0}`).
* `lemmaE9 : MetricTest I σ → PMR I σ`; `lemmaE10`: the corridor family qualifies.
-/

namespace Homm3

open Function

/-! ## Instance bookkeeping -/

namespace Instance
variable (I : Instance)

/-- Deployment hex of slot `j`. -/
def slotHex (j : ℕ) : Hex := I.slots.getD j ⟨0, 0⟩

/-- Enemy stack `j` (stack id `k + j`). -/
def enemy (j : ℕ) : EnemySpec := I.enemies.getD j ⟨default, 0, ⟨0, 0⟩⟩

/-- The creature type slot `j` receives (`default` for an empty slot). -/
def slotType (α : ℕ → SlotAlloc) (j : ℕ) : CType :=
  if 0 < (α j).count then (I.army.getD (α j).type default).1 else default

end Instance

variable {I : Instance} {α : ℕ → SlotAlloc}

theorem initUnits_player {j : ℕ} (hj : j < I.k) :
    initUnits I α j = ⟨.player, j, I.slotType α j, I.slotHex j,
      (α j).count * (I.slotType α j).hp, (α j).count, 1, false⟩ := by
  unfold initUnits; rw [if_pos hj]; rfl

theorem initUnits_enemy {j : ℕ} (hj : j < I.n) :
    initUnits I α (I.k + j) = ⟨.enemy, j, (I.enemy j).type, (I.enemy j).hex,
      (I.enemy j).count * (I.enemy j).type.hp, (I.enemy j).count, 1, false⟩ := by
  unfold initUnits
  rw [if_neg (by omega), if_pos (by unfold Instance.N; omega)]
  simp [Instance.enemy]

theorem initUnits_out {i : ℕ} (hi : I.N ≤ i) : initUnits I α i = default := by
  unfold initUnits
  rw [if_neg (by unfold Instance.N at hi; omega), if_neg (by omega)]

theorem initUnits_side_player {i : ℕ} (h : (initUnits I α i).side = .player) : i < I.k := by
  by_contra hi
  unfold initUnits at h
  rw [if_neg hi] at h
  split_ifs at h <;> cases h

theorem initUnits_side_of_lt {i : ℕ} (hi : i < I.k) : (initUnits I α i).side = .player := by
  rw [initUnits_player hi]

/-- An enemy stack id below `N` is `k + j'` with `j' < n`. -/
theorem enemy_index {i : ℕ} (hN : i < I.N) (h : (initUnits I α i).side = .enemy) :
    ∃ j' < I.n, i = I.k + j' := by
  by_cases hi : i < I.k
  · rw [initUnits_side_of_lt hi] at h; cases h
  · exact ⟨i - I.k, by unfold Instance.N at hN; omega, by omega⟩

/-- A slot that is alive at the start holds a feasible army type. -/
theorem slotType_mem (hα : Feasible I α) {j : ℕ} (hj : j < I.k)
    (ha : (initUnits I α j).alive) : ∃ x ∈ I.army, I.slotType α j = x.1 := by
  rw [initUnits_player hj] at ha
  unfold Stack.alive at ha
  have hc : 0 < (α j).count := by
    by_contra h0; simp only [not_lt, nonpos_iff_eq_zero] at h0; rw [h0] at ha; simp at ha
  have ht := hα.1 j hj hc
  refine ⟨I.army[(α j).type], List.getElem_mem ht, ?_⟩
  simp [Instance.slotType, hc, List.getElem?_eq_getElem ht]

/-! ## Reachable positions -/

/-- Positions reachable from the start of allocation `α`. -/
abbrev Reach (I : Instance) (α : ℕ → SlotAlloc) (s : State) : Prop :=
  Relation.ReflTransGen (Step I) (initState I α) s

/-- Static fields, pools never above the start, enemies never move. -/
structure RFrame (I : Instance) (α : ℕ → SlotAlloc) (s : State) : Prop where
  St : ∀ i, (s.units i).St = (initUnits I α i).St
  pool : ∀ i, (s.units i).pool ≤ (initUnits I α i).pool
  ehex : ∀ i, (initUnits I α i).side = .enemy → (s.units i).hex = (initUnits I α i).hex

theorem RFrame.side {s : State} (hf : RFrame I α s) (i : ℕ) :
    (s.units i).side = (initUnits I α i).side := congrArg Prod.fst (hf.St i)
theorem RFrame.type {s : State} (hf : RFrame I α s) (i : ℕ) :
    (s.units i).type = (initUnits I α i).type := congrArg (fun x => x.2.2.1) (hf.St i)
theorem RFrame.initc {s : State} (hf : RFrame I α s) (i : ℕ) :
    (s.units i).init = (initUnits I α i).init := congrArg (fun x => x.2.2.2) (hf.St i)

theorem Reach.frame {s : State} (h : Reach I α s) : RFrame I α s := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun _ => le_rfl, fun _ _ => rfl⟩
  | tail _ hst ih =>
    refine ⟨fun i => (hst.St i).trans (ih.St i), fun i => (hst.pool_le i).trans (ih.pool i),
      fun i hi => ?_⟩
    rw [hst.hex_of_enemy (by rw [ih.side]; exact hi), ih.ehex i hi]

/-- In round 1, a stack not yet terminal was alive at the start and has id `< N`. -/
theorem Reach.mem_Q (hR : I.R = 1) {s : State} (h : Reach I α s) {i : ℕ} (hi : i ∈ s.Q) :
    i < I.N ∧ (initUnits I α i).alive := by
  have := (Q_antitone (s := initState I α) (by simp [initState, hR]) h).2 i hi
  simp only [State.Q, initState, List.append_nil, normalQueue] at this
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at this
  exact this

/-! ## Definition E.8 -/

/-- The enemies stack `i` can strike in position `us` (R11): living enemy stacks with a hex
of `i`'s BFS reach adjacent to them. -/
def CanStrike (I : Instance) (us : ℕ → Stack) (i t : ℕ) : Prop :=
  t < I.N ∧ (us t).side = .enemy ∧ (us t).alive ∧ ∃ dest ∈ reachOf I us i, Hex.Adj dest (us t).hex

/-- `σ` is a bijection from the slots `0 … k−1` onto the enemies `0 … n−1`. -/
structure Matching (I : Instance) (σ : ℕ → ℕ) : Prop where
  maps : ∀ j < I.k, σ j < I.n
  inj : ∀ j < I.k, ∀ j' < I.k, σ j = σ j' → j = j'
  surj : ∀ j' < I.n, ∃ j < I.k, σ j = j'

/-- **Definition E.8 (persistent matching reach).** -/
def PMR (I : Instance) (σ : ℕ → ℕ) : Prop :=
  I.R = 1 ∧ Matching I σ ∧
    ∀ α, Feasible I α → ∀ s, Reach I α s →
      ∀ j < I.k, j ∈ s.Q → ∀ t, CanStrike I s.units j t ↔ t = I.k + σ j

/-- The attack step is enabled only against a strikable enemy. -/
theorem canStrike_of_attack {us : ℕ → Stack} {i t : ℕ} {dest : Hex}
    (hd : dest ∈ reachOf I us i) (ht : t < I.N) (hta : (us t).alive)
    (hts : (us t).side = .enemy) (hadj : Hex.Adj dest (us t).hex) : CanStrike I us i t :=
  ⟨ht, hts, hta, dest, hd, hadj⟩

/-! ## Lemma E.9 -/

/-- **The hypotheses of Lemma E.9** (the metric test). -/
structure MetricTest (I : Instance) (σ : ℕ → ℕ) : Prop where
  R1 : I.R = 1
  matching : Matching I σ
  /-- (1) `p_j` is adjacent to `e_{σ j}` -/
  adj : ∀ j < I.k, Hex.Adj (I.slotHex j) (I.enemy (σ j)).hex
  /-- (2) `dist(p_j, e_{j'}) > s + 1` for `j' ≠ σ j`, for every speed `s` of the army -/
  sep : ∀ j < I.k, ∀ x ∈ I.army, ∀ j' < I.n, j' ≠ σ j →
    (x.1.spd : ℤ) + 1 < Hex.dist (I.slotHex j) (I.enemy j').hex
  /-- every enemy stack is alive at the start (Definition 3.1) -/
  alive : ∀ j' < I.n, 0 < (I.enemy j').count * (I.enemy j').type.hp

variable {σ : ℕ → ℕ}

/-- **Lemma E.9, containment** — needs only Lemma E.1 and the metric half of Lemma E.3, so
it holds in every reachable position however many hexes earlier kills have freed. -/
theorem MetricTest.contain (hm : MetricTest I σ) (hα : Feasible I α) {s : State}
    (h : Reach I α s) {i t : ℕ} (hi : i < I.k) (hiQ : i ∈ s.Q)
    (hc : CanStrike I s.units i t) : t = I.k + σ i := by
  obtain ⟨ht, hts, -, dest, hd, hadj⟩ := hc
  have hf := h.frame
  obtain ⟨-, -, hhex⟩ := lemmaE1 hm.R1 h
  obtain ⟨-, hal⟩ := h.mem_Q hm.R1 hiQ
  obtain ⟨x, hx, hty⟩ := slotType_mem hα hi hal
  obtain ⟨j', hj', rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
  have hpi : (s.units i).hex = I.slotHex i := by rw [hhex i hiQ, initUnits_player hi]
  have hpe : (s.units (I.k + j')).hex = (I.enemy j').hex := by
    rw [hf.ehex _ (by rw [initUnits_enemy hj']), initUnits_enemy hj']
  have hspd : (s.units i).type.spd = x.1.spd := by
    rw [hf.type, initUnits_player hi]; simp only; rw [hty]
  unfold reachOf at hd
  rw [hpi, hspd] at hd
  rw [hpe] at hadj
  have hr := strike_radius (I.slotHex i) x.1.spd hd hadj
  by_contra hne
  have := hm.sep i hi x hx j' hj' (fun e => hne (by rw [e]))
  linarith

/-- In round 1 of a metric-test instance, the enemy of a slot that has not acted is untouched. -/
theorem MetricTest.untouched (hm : MetricTest I σ) (hα : Feasible I α) {s : State}
    (h : Reach I α s) : ∀ j < I.k, j ∈ s.Q →
      (s.units (I.k + σ j)).pool = (initUnits I α (I.k + σ j)).pool := by
  induction h with
  | refl => intro j _ _; rfl
  | @tail s₁ s₂ h₁ hst ih =>
    intro j hj hjQ
    obtain ⟨hr, hn, -⟩ := lemmaE1 hm.R1 h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have ihj := ih j hj (hsub j hjQ)
    rcases hst.pool_cases (I.k + σ j) with heq | ⟨i, q, dest, t0, hq, ha, hs, hdst, ht0, hta,
      hts, hadj, hus, hq', hb'⟩
    · rw [heq, ihj]
    have hiQ : i ∈ s₁.Q := by simp [State.Q, hq]
    have hi : i < I.k := initUnits_side_player (by rw [← (Reach.frame h₁).side]; exact hs)
    have hct := hm.contain hα h₁ hi hiQ (canStrike_of_attack hdst ht0 hta hts hadj)
    have hji : i ≠ j := by
      rintro rfl
      have : i ∉ s₂.Q := by
        simp only [State.Q, hq', hb']; exact head_not_mem_after hq hn
      exact this hjQ
    have hne : I.k + σ j ≠ t0 := by
      rw [hct]; intro e
      exact hji (hm.matching.inj i hi j hj (by omega))
    rw [hus, resolveAttack_of_ne (by omega) hne, ihj]

/-- **Lemma E.9.** The metric test implies persistent matching reach. -/
theorem lemmaE9 (hm : MetricTest I σ) : PMR I σ := by
  refine ⟨hm.R1, hm.matching, fun α hα s h j hj hjQ t => ⟨hm.contain hα h hj hjQ, ?_⟩⟩
  rintro rfl
  have hf := h.frame
  have hσ := hm.matching.maps j hj
  obtain ⟨-, -, hhex⟩ := lemmaE1 hm.R1 h
  refine ⟨by unfold Instance.N; omega, by rw [hf.side, initUnits_enemy hσ], ?_, I.slotHex j,
    ?_, ?_⟩
  · -- alive: nobody has struck it yet
    unfold Stack.alive
    rw [hm.untouched hα h j hj hjQ, initUnits_enemy hσ]
    exact hm.alive _ hσ
  · -- the empty walk
    have : (s.units j).hex = I.slotHex j := by rw [hhex j hjQ, initUnits_player hj]
    unfold reachOf; rw [this]; exact start_mem_reach _ _
  · rw [hf.ehex _ (by rw [initUnits_enemy hσ]), initUnits_enemy hσ]
    exact hm.adj j hj

/-! ## Lemma E.10 -/

namespace Corridor

variable {n : ℕ} {t v : ℕ → ℕ} {d B W : ℕ}

theorem slotHex_inst {j : ℕ} (hj : j < n) : (inst n t v d B W).slotHex j = p j := by
  simp [Instance.slotHex, inst, hj]

theorem enemy_inst {j : ℕ} (hj : j < n) :
    (inst n t v d B W).enemy j = ⟨enemyType (t j) (v j), 1, e j⟩ := by
  simp [Instance.enemy, inst, hj]

theorem matching_id : Matching (inst n t v d B W) id :=
  ⟨fun j hj => by simpa using hj, fun j _ j' _ h => h, fun j' hj' => ⟨j', by simpa using hj', rfl⟩⟩

/-- **Lemma E.10.** Every corridor instance (hence every `G(a)`) passes the metric test. -/
theorem metricTest (ht : ∀ j < n, 1 ≤ t j) : MetricTest (inst n t v d B W) id where
  R1 := rfl
  matching := matching_id
  adj j hj := by
    simp only [inst_k] at hj
    rw [slotHex_inst hj, id, enemy_inst hj]; exact adj_p_e j
  sep j hj x hx j' hj' hne := by
    simp only [inst_k] at hj; simp only [inst_n] at hj'
    simp only [inst, List.mem_singleton] at hx
    subst hx
    rw [slotHex_inst hj, enemy_inst hj']
    have := dist_p_e_ne (j := j) (j' := j') (fun e => hne (by rw [e]; rfl))
    simp only [playerType]
    push_cast; linarith
  alive j' hj' := by
    simp only [inst_n] at hj'
    rw [enemy_inst hj']; have := ht j' hj'; simp [enemyType]; omega

/-- **Lemma E.10** in the form of Definition E.8. -/
theorem pmr (ht : ∀ j < n, 1 ≤ t j) : PMR (inst n t v d B W) id := lemmaE9 (metricTest ht)

end Corridor

end Homm3
