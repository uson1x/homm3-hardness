import Homm3.MatchingReach
import Homm3.Prop11
import Homm3.KnapsackArray

/-!
# Session 2, target 2. Proposition 1.1 in the paper's generality

Paper: Appendix E, "Proposition 1.1, and what matching reach has to mean", the proof.

Hypotheses (`Prop11Hyp I C B σ`), for an arbitrary `ARMY-ALLOCATION` instance `I`:
* **persistent matching reach** with bijection `σ` (Definition E.8, `PMR`; it contains
  `R = 1`, and the defence is `(‡)` by construction of the semantics);
* a **single creature type** `C` of flat damage `d := C.dmg ≥ 1` and `hp ≥ 1`, stock `B`
  (`I.army = [(C, B)]`);
* **one creature per enemy stack**, of `t ≥ 1` hit points;
* damage under `(★)`: of `(★)` the proof consumes exactly `def(E) = att(C)` for every
  enemy (`Star` below gives it from the paper's full `(★)`).

Conclusion (`opt`, `decide`): the optimum destroyed value over all feasible allocations and
all plays is `dp = OPT` of the 0-1 knapsack `(K)` with items `j < k`, values
`v_j := value(E_{σ j})`, weights `b_j := ⌈t_{σ j} / d⌉`, capacity `B`; so
`ARMY-ALLOCATION I ↔ W ≤ dp`.

The proof is the paper's, with Definition E.8 used exactly where the paper uses it: the
upper bound applies it to every attack step (the attacker has not yet taken its terminal
action, so it can strike only its own enemy), the witness applies it to obtain a legal
approach hex *in the position where the attack is taken*.  The corridor proof of session 1
is re-derived as the special case (`Corridor.prop11_decide_via_general`).
-/

namespace Homm3

open Function

/-- The paper's `(★)` for an instance: every army type and every enemy type has
`att = def = 1`, every enemy type flat damage `1`. -/
structure Star (I : Instance) : Prop where
  army : ∀ x ∈ I.army, x.1.att = 1 ∧ x.1.dfn = 1
  enemy : ∀ j < I.n, (I.enemy j).type.att = 1 ∧ (I.enemy j).type.dfn = 1 ∧
    (I.enemy j).type.dmg = 1

/-- **The hypotheses of Proposition 1.1.** -/
structure Prop11Hyp (I : Instance) (C : CType) (B : ℕ) (σ : ℕ → ℕ) : Prop where
  pmr : PMR I σ
  army : I.army = [(C, B)]
  dmg : 1 ≤ C.dmg
  hp : 1 ≤ C.hp
  one : ∀ j < I.n, (I.enemy j).count = 1
  ehp : ∀ j < I.n, 1 ≤ (I.enemy j).type.hp
  dfn : ∀ j < I.n, (I.enemy j).type.dfn = C.att

/-- `(★)` supplies the damage hypothesis. -/
theorem Prop11Hyp.ofStar {I : Instance} {C : CType} {B : ℕ} {σ : ℕ → ℕ} (hpmr : PMR I σ)
    (harmy : I.army = [(C, B)]) (hstar : Star I) (hd : 1 ≤ C.dmg) (hhp : 1 ≤ C.hp)
    (hone : ∀ j < I.n, (I.enemy j).count = 1) (hehp : ∀ j < I.n, 1 ≤ (I.enemy j).type.hp) :
    Prop11Hyp I C B σ :=
  ⟨hpmr, harmy, hd, hhp, hone, hehp, fun j hj => by
    rw [(hstar.enemy j hj).2.1, (hstar.army (C, B) (by simp [harmy])).1]⟩

namespace Prop11

/-- Knapsack item `j` (slot `j`): value of `E_{σ j}`. -/
def val (I : Instance) (σ : ℕ → ℕ) (j : ℕ) : ℕ := (I.enemy (σ j)).type.value
/-- Hit points of `E_{σ j}`. -/
def hpOf (I : Instance) (σ : ℕ → ℕ) (j : ℕ) : ℕ := (I.enemy (σ j)).type.hp
/-- Weight of item `j`: `b_j = ⌈t_{σ j} / d⌉`. -/
def need (I : Instance) (C : CType) (σ : ℕ → ℕ) (j : ℕ) : ℕ :=
  (hpOf I σ j + C.dmg - 1) / C.dmg

/-! ## Counting creatures -/

theorem count_le {u : Stack} {c : ℕ} (hhp : 1 ≤ u.type.hp) (h : u.pool ≤ c * u.type.hp) :
    u.count ≤ c := by
  unfold Stack.count
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega), Nat.succ_mul]
  generalize c * u.type.hp = m at h ⊢
  omega

theorem one_le_count {u : Stack} (hhp : 1 ≤ u.type.hp) (h : 1 ≤ u.pool) : 1 ≤ u.count := by
  unfold Stack.count
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

theorem count_eq {u : Stack} {c : ℕ} (hhp : 1 ≤ u.type.hp) (h : u.pool = c * u.type.hp) :
    u.count = c := by
  unfold Stack.count
  apply Nat.div_eq_of_lt_le
  · rw [h]; omega
  · rw [h, Nat.succ_mul]; omega

variable {C : CType}

/-- Every blow of a stack of type `C` with at most `c` creatures' worth of pool, on a target
of defence `≥ att(C)`, is at most nominal `c · d` (§2.4, with or without `DEFEND`). -/
theorem blow_le {a tg : Stack} {c : ℕ} (hty : a.type = C) (hd : 1 ≤ C.dmg) (hhp : 1 ≤ C.hp)
    (h1 : 1 ≤ a.pool) (h2 : a.pool ≤ c * C.hp) (hdef : C.att ≤ tg.type.dfn) :
    blow a tg ≤ c * C.dmg := by
  have hc1 := one_le_count (u := a) (by rw [hty]; exact hhp) h1
  have hc2 := count_le (u := a) (c := c) (by rw [hty]; exact hhp) (by rw [hty]; exact h2)
  unfold blow
  rw [hty]
  have hΔ : ((C.att : ℤ) - tg.defEff) ≤ 0 := by
    have : C.att ≤ tg.defEff := le_trans hdef (by unfold Stack.defEff; omega)
    omega
  exact (damage_le_nominal hΔ (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega)))).trans (Nat.mul_le_mul_right _ hc2)

/-- A fresh stack of `c ≥ 1` creatures of type `C` striking an undefended target of defence
`att(C)` deals exactly `c · d` (`Δ = 0`, `(★)`). -/
theorem blow_eq {a tg : Stack} {c : ℕ} (hty : a.type = C) (hd : 1 ≤ C.dmg) (hhp : 1 ≤ C.hp)
    (hpool : a.pool = c * C.hp) (hc : 1 ≤ c) (hdef : tg.defEff = C.att) :
    blow a tg = c * C.dmg := by
  have hcnt := count_eq (u := a) (c := c) (by rw [hty]; exact hhp) (by rw [hty]; exact hpool)
  unfold blow
  rw [hty, hcnt, hdef, sub_self]
  exact damage_zero (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

variable {I : Instance} {B : ℕ} {σ : ℕ → ℕ} {α : ℕ → SlotAlloc}

theorem slotType_eq (H : Prop11Hyp I C B σ)
    (hα : ∀ j < I.k, 0 < (α j).count → (α j).type < I.army.length) {j : ℕ} (hj : j < I.k)
    (hc : 0 < (α j).count) : I.slotType α j = C := by
  have ht := hα j hj hc
  rw [H.army] at ht
  have h0 : (α j).type = 0 := by simpa using ht
  simp [Instance.slotType, hc, h0, H.army]

/-- A player stack alive at the start has type `C` and `c_j ≥ 1` creatures. -/
theorem player_start (H : Prop11Hyp I C B σ) (hα : Feasible I α) {j : ℕ} (hj : j < I.k)
    (ha : (initUnits I α j).alive) :
    0 < (α j).count ∧ (initUnits I α j).type = C ∧ (initUnits I α j).pool = (α j).count * C.hp := by
  rw [initUnits_player hj] at ha ⊢
  unfold Stack.alive at ha
  have hc : 0 < (α j).count := by
    by_contra h0; simp only [not_lt, nonpos_iff_eq_zero] at h0; rw [h0] at ha; simp at ha
  exact ⟨hc, slotType_eq H hα.1 hj hc, by simp only; rw [slotType_eq H hα.1 hj hc]⟩

/-- Under a feasible allocation the slots hold at most `B` creatures. -/
theorem sum_count_le (H : Prop11Hyp I C B σ) (hα : Feasible I α) :
    ∑ j ∈ Finset.range I.k, (α j).count ≤ B := by
  have h := hα.2 0 (by simp [H.army])
  rw [Finset.sum_filter_of_ne] at h
  · simpa [H.army] using h
  · intro j hj hne
    have := hα.1 j (Finset.mem_range.mp hj) (Nat.pos_of_ne_zero hne)
    simp [H.army] at this; exact this

theorem enemy_start (H : Prop11Hyp I C B σ) {j : ℕ} (hj : j < I.k) :
    (initUnits I α (I.k + σ j)).pool = hpOf I σ j ∧
      (initUnits I α (I.k + σ j)).type = (I.enemy (σ j)).type ∧
      (initUnits I α (I.k + σ j)).side = .enemy := by
  have hσ := H.pmr.2.1.maps j hj
  rw [initUnits_enemy hσ]
  simp [H.one _ hσ, hpOf]

/-! ## Value destroyed -/

theorem destroyed_eq (H : Prop11Hyp I C B σ) {s : State} (hf : RFrame I α s) :
    destroyed I s =
      ∑ j ∈ Finset.range I.k, if (s.units (I.k + σ j)).pool = 0 then val I σ j else 0 := by
  unfold destroyed Instance.N
  rw [Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range I.k, (if (s.units x).side = .enemy then
      ((s.units x).init - (s.units x).count) * (s.units x).type.value else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hf.side, initUnits_side_of_lt (Finset.mem_range.mp hj)]
    simp
  rw [h1, zero_add]
  have hM := H.pmr.2.1
  refine (Finset.sum_nbij σ (fun j hj => Finset.mem_range.mpr
      (hM.maps j (Finset.mem_range.mp hj)))
    (fun j hj j' hj' e => hM.inj j (Finset.mem_range.mp hj) j' (Finset.mem_range.mp hj') e)
    (fun j' hj' => by
      obtain ⟨j, hj, e⟩ := hM.surj j' (Finset.mem_range.mp hj')
      exact ⟨j, Finset.mem_range.mpr hj, e⟩) ?_).symm
  intro j hj
  have hj := Finset.mem_range.mp hj
  have hσ := hM.maps j hj
  have hty := hf.type (I.k + σ j)
  have hin := hf.initc (I.k + σ j)
  have hpl := hf.pool (I.k + σ j)
  rw [initUnits_enemy hσ] at hty hin hpl
  simp only at hty hin hpl
  rw [H.one _ hσ, one_mul] at hpl
  rw [H.one _ hσ] at hin
  rw [hf.side, initUnits_enemy hσ, hin, hty,
    Corridor.count_single (H.ehp _ hσ) (by rw [hty]) hpl]
  simp only [↓reduceIte, val]
  split_ifs <;> simp

/-! ## The optimum is at most `(K)` -/

/-- The upper-bound invariant: the enemy of slot `j` has lost at most the one blow of slot
`j`, and only after slot `j` took its terminal action. -/
theorem key (H : Prop11Hyp I C B σ) (hα : Feasible I α) {s : State} (h : Reach I α s) :
    ∀ j < I.k, hpOf I σ j ≤ (s.units (I.k + σ j)).pool +
      (if j ∈ s.Q then 0 else (α j).count * C.dmg) := by
  have hR := H.pmr.1
  induction h with
  | refl =>
    intro j hj
    simp only [initState]
    rw [(enemy_start (α := α) H hj).1]; omega
  | @tail s₁ s₂ h₁ hst ih =>
    intro j hj
    obtain ⟨hr, hn, -⟩ := lemmaE1 hR h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have hf := Reach.frame h₁
    rcases hst.pool_cases (I.k + σ j) with heq | ⟨i, q, dest, t0, hq, ha, hs, hdst, ht0, hta,
      hts, hadj, hus, hq', hb'⟩
    · rw [heq]; exact Corridor.key_transfer (ih j hj) (hsub j)
    have hiQ : i ∈ s₁.Q := by simp [State.Q, hq]
    have hi : i < I.k := initUnits_side_player (by rw [← hf.side]; exact hs)
    have hct : t0 = I.k + σ i :=
      (H.pmr.2.2 α hα s₁ h₁ i hi hiQ t0).mp (canStrike_of_attack hdst ht0 hta hts hadj)
    subst hct
    have hiQ' : i ∉ s₂.Q := by
      simp only [State.Q, hq', hb']; exact head_not_mem_after hq hn
    by_cases hji : j = i
    · subst hji
      rw [hus, resolveAttack_pool_target (by omega), if_neg hiQ']
      have hk := ih j hj
      rw [if_pos hiQ] at hk
      obtain ⟨-, hal⟩ := Reach.mem_Q hR h₁ hiQ
      obtain ⟨-, hty, hpool⟩ := player_start H hα hj hal
      have hb := blow_le (C := C) (c := (α j).count)
        (a := { activate (s₁.units j) with hex := dest }) (tg := s₁.units (I.k + σ j))
        (by simp only [activate]; rw [hf.type, hty]) H.dmg H.hp
        (by simp only [activate]; exact Nat.succ_le_of_lt ha)
        (by simp only [activate]; rw [← hpool]; exact hf.pool j)
        (by
          rw [hf.type, (enemy_start (α := α) H hj).2.1,
            H.dfn _ (H.pmr.2.1.maps j hj)])
      generalize blow _ _ = x at hb ⊢
      generalize (α j).count * C.dmg = y at hb ⊢
      omega
    · have hne : I.k + σ j ≠ I.k + σ i := by
        intro e; exact hji (H.pmr.2.1.inj j hj i hi (by omega))
      rw [hus, resolveAttack_of_ne (by omega) hne]
      exact Corridor.key_transfer (ih j hj) (hsub j)

/-- **Proposition 1.1, upper bound.** Every play under every feasible allocation destroys
at most `OPT` of `(K)`. -/
theorem upper (H : Prop11Hyp I C B σ) (hα : Feasible I α) {s : State} (h : Reach I α s) :
    destroyed I s ≤ Knapsack.OPT (val I σ) (need I C σ) I.k B := by
  rw [destroyed_eq H (Reach.frame h)]
  set S := (Finset.range I.k).filter (fun j => (s.units (I.k + σ j)).pool = 0) with hS
  have hsum : (∑ j ∈ Finset.range I.k,
      if (s.units (I.k + σ j)).pool = 0 then val I σ j else 0) = ∑ j ∈ S, val I σ j := by
    rw [hS, Finset.sum_filter]
  rw [hsum]
  apply Knapsack.le_OPT
  rw [Knapsack.mem_feasible]
  refine ⟨Finset.filter_subset _ _, ?_⟩
  calc ∑ j ∈ S, need I C σ j ≤ ∑ j ∈ S, (α j).count := by
        apply Finset.sum_le_sum
        intro j hjS
        rw [hS, Finset.mem_filter, Finset.mem_range] at hjS
        have hk := key H hα h j hjS.1
        rw [hjS.2, zero_add] at hk
        have h1 := H.ehp _ (H.pmr.2.1.maps j hjS.1)
        unfold hpOf at hk
        split_ifs at hk
        · omega
        · exact (Corridor.ceil_div_le_iff H.dmg).mpr hk
    _ ≤ ∑ j ∈ Finset.range I.k, (α j).count :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ B := sum_count_le H hα

/-! ## The optimum is at least `(K)` -/

/-- The witness allocation: `c_j := b_j` on `S`, empty elsewhere. -/
def αW (I : Instance) (C : CType) (σ : ℕ → ℕ) (S : Finset ℕ) (j : ℕ) : SlotAlloc :=
  ⟨0, if j ∈ S then need I C σ j else 0⟩

theorem αW_feasible (H : Prop11Hyp I C B σ) {S : Finset ℕ}
    (hS : S ∈ Knapsack.feasible (need I C σ) I.k B) : Feasible I (αW I C σ S) := by
  rw [Knapsack.mem_feasible] at hS
  refine ⟨fun j _ _ => by simp [αW, H.army], fun t' ht' => ?_⟩
  have : t' = 0 := by simpa [H.army] using ht'
  subst this
  have harmy : (I.army.getD 0 default).2 = B := by simp [H.army]
  rw [harmy]
  simpa [αW, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS.1] using hS.2

theorem one_le_need (H : Prop11Hyp I C B σ) {j : ℕ} (hj : j < I.k) : 1 ≤ need I C σ j := by
  unfold need hpOf
  have := H.ehp _ (H.pmr.2.1.maps j hj)
  have := H.dmg
  rw [Nat.one_le_div_iff (by omega)]; omega

theorem hp_le_need_mul (H : Prop11Hyp I C B σ) (j : ℕ) :
    hpOf I σ j ≤ need I C σ j * C.dmg :=
  (Corridor.ceil_div_le_iff H.dmg).mp le_rfl

/-- Invariant of the witness run in the `NORMAL` phase. -/
structure GWN (I : Instance) (C : CType) (σ : ℕ → ℕ) (S : Finset ℕ) (s : State) : Prop where
  reach : Reach I (αW I C σ S) s
  phase : s.phase = .normal
  bucket : ∀ i ∈ s.bucket, (s.units i).side = .enemy
  fresh : ∀ j < I.k, j ∈ s.queue →
    (s.units j).pool = (αW I C σ S j).count * C.hp ∧
    (s.units (I.k + σ j)).pool = hpOf I σ j ∧ (s.units (I.k + σ j)).defending = false
  killed : ∀ j ∈ S, j ∉ s.queue → (s.units (I.k + σ j)).pool = 0

variable {S : Finset ℕ}

theorem mem_initQueue {i : ℕ} (hi : i < I.N) (ha : (initUnits I α i).alive) :
    i ∈ (initState I α).queue := by
  simp only [initState, normalQueue]
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨hi, ha⟩


theorem αW_type (H : Prop11Hyp I C B σ) :
    ∀ j < I.k, 0 < (αW I C σ S j).count → (αW I C σ S j).type < I.army.length :=
  fun _ _ _ => by simp [αW, H.army]

theorem GWN.init (H : Prop11Hyp I C B σ) (hS : S ⊆ Finset.range I.k) :
    GWN I C σ S (initState I (αW I C σ S)) where
  reach := .refl
  phase := rfl
  bucket := by simp [initState]
  fresh j hj _ := by
    refine ⟨?_, (enemy_start H hj).1, by simp [initState, initUnits_enemy (H.pmr.2.1.maps j hj)]⟩
    simp only [initState, initUnits_player hj]
    by_cases hc : 0 < (αW I C σ S j).count
    · rw [slotType_eq H (αW_type H) hj hc]
    · have : (αW I C σ S j).count = 0 := by omega
      rw [this]; simp
  killed j hjS hjq := by
    exfalso; apply hjq
    have hj : j < I.k := Finset.mem_range.mp (hS hjS)
    apply mem_initQueue (by unfold Instance.N; omega)
    rw [initUnits_player hj]
    unfold Stack.alive
    have h1 := one_le_need H hj
    have hc : 0 < (αW I C σ S j).count := by simp [αW, hjS]; omega
    simp only
    rw [slotType_eq H (αW_type H) hj hc]
    exact Nat.mul_pos hc H.hp

/-- One step of the witness run in the `NORMAL` phase: a dead stack is skipped, an enemy
`WAIT`s (`(‡)`), a player stack strikes its own enemy from the approach hex Definition E.8
provides in the current position. -/
theorem GWN.step (H : Prop11Hyp I C B σ) (hS : S ∈ Knapsack.feasible (need I C σ) I.k B)
    {s : State} (hw : GWN I C σ S s) {i : ℕ} {q : List ℕ} (hq : s.queue = i :: q) :
    ∃ s', Step I s s' ∧ GWN I C σ S s' ∧ s'.queue = q := by
  have hR := H.pmr.1
  have hM := H.pmr.2.1
  have hSr := (Knapsack.mem_feasible.mp hS).1
  obtain ⟨-, hn, -⟩ := lemmaE1 hR hw.reach
  have hf := Reach.frame hw.reach
  have hnq := head_not_mem_after hq hn
  have hjq : ∀ j ∈ q, j ≠ i := fun j hj e => hnq (e ▸ List.mem_append_left _ hj)
  by_cases ha : (s.units i).alive
  · rcases hside : (s.units i).side with _ | _
    · -- a player stack: strike `E_{σ i}`
      have hi : i < I.k := initUnits_side_player (by rw [← hf.side]; exact hside)
      have hiq : i ∈ s.queue := by simp [hq]
      have hiQ : i ∈ s.Q := by simp [State.Q, hq]
      obtain ⟨hpool, hepool, hedef⟩ := hw.fresh i hi hiq
      have hiS : i ∈ S := by
        by_contra hiS
        simp [αW, hiS] at hpool; unfold Stack.alive at ha; omega
      have hσ := hM.maps i hi
      obtain ⟨ht, hts, hta, dest, hd, hadj⟩ :=
        (H.pmr.2.2 _ (αW_feasible H hS) s hw.reach i hi hiQ (I.k + σ i)).mpr rfl
      have hstep := Step.playerAttack (I := I) hq ha hside hd ht hta hts hadj
      refine ⟨_, hstep, ?_, rfl⟩
      have hdead : (resolveAttack s.units i (I.k + σ i) dest (I.k + σ i)).pool = 0 := by
        rw [resolveAttack_pool_target (by omega), hepool]
        have hc1 := one_le_need H hi
        have hb := blow_eq (C := C) (c := need I C σ i)
          (a := { activate (s.units i) with hex := dest }) (tg := s.units (I.k + σ i))
          (by
            simp only [activate]; rw [hf.type, initUnits_player hi]; simp only
            exact slotType_eq H (αW_type H) hi (by simp [αW, hiS]; omega))
          H.dmg H.hp (by simp only [activate]; rw [hpool]; simp [αW, hiS]) hc1
          (by
            unfold Stack.defEff
            rw [hedef, hf.type, (enemy_start H hi).2.1, H.dfn _ hσ]; simp)
        rw [hb]
        have := hp_le_need_mul H i
        omega
      refine ⟨hw.reach.tail hstep, hw.phase, ?_, ?_, ?_⟩
      · intro x hx; rw [hstep.side]; exact hw.bucket x hx
      · intro j hj hjq'
        have hji := hjq j hjq'
        obtain ⟨a1, a2, a3⟩ := hw.fresh j hj (by simp [hq, hjq'])
        have hne : I.k + σ j ≠ I.k + σ i := by
          intro e; exact hji (hM.inj j hj i hi (by omega))
        simp only
        rw [resolveAttack_of_ne hji (by omega), resolveAttack_of_ne (by omega) hne]
        exact ⟨a1, a2, a3⟩
      · intro j hjS hjq'
        simp only at hjq' ⊢
        by_cases hji : j = i
        · subst hji; exact hdead
        · have hj : j < I.k := Finset.mem_range.mp (hSr hjS)
          have hne : I.k + σ j ≠ I.k + σ i := by
            intro e; exact hji (hM.inj j hj i hi (by omega))
          rw [resolveAttack_of_ne (by omega) hne]
          exact hw.killed j hjS (by simp [hq, hji, hjq'])
    · -- an enemy stack: `(‡)` makes it `WAIT`
      have hstep := Step.enemyWait (I := I) hw.phase hq ha hside
      refine ⟨_, hstep, ?_, rfl⟩
      have hik : ∀ j < I.k, j ≠ i := by
        intro j hj e; subst e
        rw [hf.side, initUnits_side_of_lt hj] at hside; cases hside
      refine ⟨hw.reach.tail hstep, hw.phase, ?_, ?_, ?_⟩
      · intro x hx
        rw [hstep.side]
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw.bucket x hx
        · exact hside
      · intro j hj hjq'
        obtain ⟨a1, a2, a3⟩ := hw.fresh j hj (by simp [hq, hjq'])
        dsimp only
        rw [update_of_ne (hik j hj)]
        by_cases hnj : I.k + σ j = i
        · rw [← hnj, update_self]; exact ⟨a1, by simpa [activate] using a2, rfl⟩
        · rw [update_of_ne hnj]; exact ⟨a1, a2, a3⟩
      · intro j hjS hjq'
        have hj : j < I.k := Finset.mem_range.mp (hSr hjS)
        have := hw.killed j hjS (by simp [hq, hik j hj, hjq'])
        dsimp only
        by_cases hnj : I.k + σ j = i
        · rw [← hnj, update_self]; simpa [activate] using this
        · rw [update_of_ne hnj]; exact this
  · -- a dead stack is skipped
    have hstep := Step.skip (I := I) hq ha
    refine ⟨_, hstep, ⟨hw.reach.tail hstep, hw.phase, hw.bucket, ?_, ?_⟩, rfl⟩
    · intro j hj hjq'; exact hw.fresh j hj (by simp [hq, hjq'])
    · intro j hjS hjq'
      by_cases hji : j = i
      · subst hji
        have hj : j < I.k := Finset.mem_range.mp (hSr hjS)
        obtain ⟨hpool, -⟩ := hw.fresh j hj (by simp [hq])
        exfalso; apply ha
        unfold Stack.alive
        rw [hpool]
        have := one_le_need H hj
        simp only [αW, hjS, ↓reduceIte]
        exact Nat.mul_pos (by omega) H.hp
      · exact hw.killed j hjS (by simp [hq, hji]; exact hjq')

theorem GWN.run (H : Prop11Hyp I C B σ) (hS : S ∈ Knapsack.feasible (need I C σ) I.k B) :
    ∀ (L : List ℕ) (s : State), GWN I C σ S s → s.queue = L →
      ∃ s', Relation.ReflTransGen (Step I) s s' ∧ GWN I C σ S s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    obtain ⟨s1, h1, hw1, hq1⟩ := hw.step H hS hq
    obtain ⟨s2, h2, hw2, hq2⟩ := GWN.run H hS q s1 hw1 hq1
    exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩

/-- Invariant of the witness run in the `WAIT` phase. -/
structure GWW (I : Instance) (C : CType) (σ : ℕ → ℕ) (S : Finset ℕ) (s : State) : Prop where
  reach : Reach I (αW I C σ S) s
  phase : s.phase = .wait
  queue : ∀ i ∈ s.queue, (s.units i).side = .enemy
  killed : ∀ j ∈ S, (s.units (I.k + σ j)).pool = 0

theorem GWW.run : ∀ (L : List ℕ) (s : State), GWW I C σ S s → s.queue = L →
      ∃ s', Relation.ReflTransGen (Step I) s s' ∧ GWW I C σ S s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    have next : ∀ s1, Step I s s1 → s1.queue = q → s1.phase = .wait →
        (∀ j ∈ S, (s1.units (I.k + σ j)).pool = (s.units (I.k + σ j)).pool) →
        ∃ s', Relation.ReflTransGen (Step I) s s' ∧ GWW I C σ S s' ∧ s'.queue = [] := by
      intro s1 h1 hq1 hph hpool
      have hw1 : GWW I C σ S s1 := by
        refine ⟨hw.reach.tail h1, hph, ?_, ?_⟩
        · intro x hx
          rw [h1.side]; exact hw.queue x (by simp [hq, hq1 ▸ hx])
        · intro j hj; rw [hpool j hj]; exact hw.killed j hj
      obtain ⟨s2, h2, hw2, hq2⟩ := GWW.run q s1 hw1 hq1
      exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩
    by_cases ha : (s.units i).alive
    · have hside := hw.queue i (by simp [hq])
      refine next _ (Step.enemyDefend hw.phase hq ha hside) rfl hw.phase ?_
      intro j _; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
    · exact next _ (Step.skip hq ha) rfl hw.phase (fun _ _ => rfl)

/-- **Proposition 1.1, lower bound.** For every `S` feasible for `(K)` there is a feasible
allocation and a complete play destroying at least `Σ_{j∈S} v_j`. -/
theorem lower (H : Prop11Hyp I C B σ) (hS : S ∈ Knapsack.feasible (need I C σ) I.k B) :
    ∃ α, Feasible I α ∧ ∃ s, Reach I α s ∧ Done s ∧ ∑ j ∈ S, val I σ j ≤ destroyed I s := by
  have hSr := (Knapsack.mem_feasible.mp hS).1
  refine ⟨αW I C σ S, αW_feasible H hS, ?_⟩
  obtain ⟨s1, h1, hw1, hq1⟩ := GWN.run H hS _ _ (GWN.init H hSr) rfl
  have hstep := Step.toWait (I := I) hw1.phase hq1
  have hw2 : GWW I C σ S
      { s1 with phase := .wait, queue := s1.bucket.mergeSort (waitLe s1.units), bucket := [] } :=
    ⟨hw1.reach.tail hstep, rfl,
      fun x hx => hw1.bucket x ((List.mergeSort_perm _ _).mem_iff.mp hx),
      fun j hj => hw1.killed j hj (by simp [hq1])⟩
  obtain ⟨s3, h3, hw3, hq3⟩ := GWW.run _ _ hw2 rfl
  obtain ⟨hr3, -, -⟩ := lemmaE1 H.pmr.1 hw3.reach
  refine ⟨s3, hw3.reach, ⟨hw3.phase, hq3, by rw [hr3]⟩, ?_⟩
  rw [destroyed_eq H (Reach.frame hw3.reach), ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset
  intro j hj
  rw [Finset.mem_filter]
  exact ⟨hSr hj, hw3.killed j hj⟩

end Prop11

open Prop11 in
/-- **Proposition 1.1** (general form): under `Prop11Hyp` the optimum destroyed value over
all feasible allocations and all plays is exactly the knapsack DP value, attained by a
complete play. -/
theorem prop11_general {I : Instance} {C : CType} {B : ℕ} {σ : ℕ → ℕ}
    (H : Prop11Hyp I C B σ) :
    (∀ α, Feasible I α → ∀ s, Reach I α s →
        destroyed I s ≤ Knapsack.dp (val I σ) (need I C σ) I.k B) ∧
    ∃ α, Feasible I α ∧ ∃ s, Reach I α s ∧ Done s ∧
      destroyed I s = Knapsack.dp (val I σ) (need I C σ) I.k B := by
  refine ⟨fun α hα s hs => (Knapsack.dp_eq_OPT _ B).symm ▸ upper H hα hs, ?_⟩
  obtain ⟨S, hS, hSv⟩ := Knapsack.OPT_attained (v := val I σ) (b := need I C σ) I.k B
  obtain ⟨α, hα, s, hs, hdone, hle⟩ := lower H hS
  refine ⟨α, hα, s, hs, hdone, le_antisymm ?_ ?_⟩
  · rw [Knapsack.dp_eq_OPT]; exact upper H hα hs
  · rw [Knapsack.dp_eq_OPT, ← hSv]; exact hle

open Prop11 in
/-- **Proposition 1.1, decision form**: `ARMY-ALLOCATION I ↔ W ≤ dp`. -/
theorem prop11_general_decide {I : Instance} {C : CType} {B : ℕ} {σ : ℕ → ℕ}
    (H : Prop11Hyp I C B σ) :
    ArmyAllocation I ↔ I.W ≤ Knapsack.dp (val I σ) (need I C σ) I.k B := by
  constructor
  · rintro ⟨α, hα, s, hs, -, hW⟩
    exact hW.trans ((prop11_general H).1 α hα s hs)
  · intro hW
    obtain ⟨α, hα, s, hs, hdone, heq⟩ := (prop11_general H).2
    exact ⟨α, hα, s, hs, hdone, heq ▸ hW⟩

/-! ## The corridor as the special case -/

namespace Knapsack

/-- The DP reads its items only below the prefix length. -/
theorem dp_congr {v v' b b' : ℕ → ℕ} : ∀ {k : ℕ}, (∀ j < k, v j = v' j) →
    (∀ j < k, b j = b' j) → ∀ cap, dp v b k cap = dp v' b' k cap
  | 0, _, _, _ => rfl
  | k + 1, hv, hb, cap => by
    have ihv : ∀ j < k, v j = v' j := fun j hj => hv j (by omega)
    have ihb : ∀ j < k, b j = b' j := fun j hj => hb j (by omega)
    simp only [dp, hv k (by omega), hb k (by omega), dp_congr ihv ihb]

end Knapsack

namespace Corridor

variable {n : ℕ} {t v : ℕ → ℕ} {d B W : ℕ}

/-- The corridor family satisfies the hypotheses of Proposition 1.1 (with `σ = id`), via
Lemma E.10. -/
theorem prop11Hyp (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) :
    Prop11Hyp (inst n t v d B W) (playerType d) B id where
  pmr := pmr ht
  army := rfl
  dmg := hd
  hp := by simp [playerType]
  one j hj := by simp only [inst_n] at hj; rw [enemy_inst hj]
  ehp j hj := by simp only [inst_n] at hj; rw [enemy_inst hj]; exact ht j hj
  dfn j hj := by simp only [inst_n] at hj; rw [enemy_inst hj]; rfl

/-- Session 1's corridor Proposition 1.1, re-derived from the general theorem. -/
theorem prop11_decide_via_general (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) :
    ArmyAllocation (inst n t v d B W) ↔ W ≤ Knapsack.dp v (thr t d) n B := by
  rw [prop11_general_decide (prop11Hyp hd ht)]
  simp only [inst_k]
  rw [Knapsack.dp_congr (v' := v) (b' := thr t d) ?_ ?_]
  · rfl
  · intro j hj; simp [Prop11.val, enemy_inst hj, enemyType]
  · intro j hj; simp [Prop11.need, Prop11.hpOf, enemy_inst hj, enemyType, thr, playerType]

end Corridor

/-! ## The algorithm of the statement: preprocessing and the one-row DP -/

open Prop11 in
/-- **The preprocessing pass of Proposition 1.1**: with `B ≥ 1`, the allocation that deploys
a single creature in slot `j` and nothing else is feasible, and in its starting position the
enemies slot `j` can strike are exactly `{E_{σ j}}` — so one BFS per slot (`CanStrike` is a
BFS over the free hexes, `reachListOf`/`targets` in `Exec.lean`) recovers the bijection. -/
theorem prop11_preprocess {I : Instance} {C : CType} {B : ℕ} {σ : ℕ → ℕ}
    (H : Prop11Hyp I C B σ) (hB : 1 ≤ B) {j : ℕ} (hj : j < I.k) :
    Feasible I (fun i => if i = j then ⟨0, 1⟩ else ⟨0, 0⟩) ∧
      ∀ t, CanStrike I (initState I (fun i => if i = j then ⟨0, 1⟩ else ⟨0, 0⟩)).units j t ↔
        t = I.k + σ j := by
  set α : ℕ → SlotAlloc := fun i => if i = j then ⟨0, 1⟩ else ⟨0, 0⟩ with hαdef
  have hα : Feasible I α := by
    refine ⟨fun i _ _ => by simp only [hαdef]; split_ifs <;> simp [H.army], fun t ht => ?_⟩
    have : t = 0 := by simpa [H.army] using ht
    subst this
    have hfilt : (Finset.range I.k).filter (fun i => (α i).type = 0) = Finset.range I.k := by
      ext i; simp only [Finset.mem_filter, hαdef]; split_ifs <;> simp
    rw [hfilt]
    simp only [hαdef, H.army, List.getD_cons_zero]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (fun h => absurd
      (Finset.mem_range.mpr hj) h)]
    simpa using hB
  refine ⟨hα, (H.pmr.2.2 α hα _ .refl j hj ?_)⟩
  simp only [State.Q, initState, List.append_nil]
  apply mem_initQueue (by unfold Instance.N; omega)
  rw [initUnits_player hj]
  unfold Stack.alive
  have hc : 0 < (α j).count := by simp [hαdef]
  simp only
  rw [slotType_eq H hα.1 hj hc]
  exact Nat.mul_pos hc H.hp

open Prop11 in
/-- **Proposition 1.1 with the algorithm of the statement**: `ARMY-ALLOCATION` is decided
by the one-row, `O(B)`-space array program of `dp_single_type.py`. -/
theorem prop11_general_decide_array {I : Instance} {C : CType} {B : ℕ} {σ : ℕ → ℕ}
    (H : Prop11Hyp I C B σ) :
    ArmyAllocation I ↔ I.W ≤ Knapsack.dpArray (val I σ) (need I C σ) I.k B := by
  rw [Knapsack.dpArray_eq_dp]; exact prop11_general_decide H

end Homm3
