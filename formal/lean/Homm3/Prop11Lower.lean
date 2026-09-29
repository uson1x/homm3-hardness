import Homm3.Prop11

/-!
# Stage 4e. Proposition 1.1, lower bound: the witness play

Paper: Appendix E, proof of Proposition 1.1, "The optimum is at least `(K)`" (and, with
`t = v = a`, `d = 1`, Lemma E.6).  Allocate `c_j := ⌈t_j/d⌉` for `j ∈ S`, `0` otherwise;
every nonempty stack issues `WALK_AND_ATTACK` against its own enemy from its own hex
(empty walk) at its `NORMAL` activation, without waiting.  The run is built by induction
on the `NORMAL` queue, then on the `WAIT` queue (where only `(‡)`'s `DEFEND`s remain).
-/

namespace Homm3.Corridor

open Function

variable {n : ℕ} {t v : ℕ → ℕ} {d B W : ℕ}

/-- The witness allocation. -/
def αW (t : ℕ → ℕ) (d : ℕ) (S : Finset ℕ) (j : ℕ) : SlotAlloc :=
  ⟨0, if j ∈ S then thr t d j else 0⟩

theorem αW_feasible {S : Finset ℕ} (hS : S ∈ Knapsack.feasible (thr t d) n B) :
    Feasible (inst n t v d B W) (αW t d S) := by
  rw [Knapsack.mem_feasible] at hS
  refine ⟨fun j _ _ => by simp [αW, inst], fun t' ht' => ?_⟩
  have : t' = 0 := by simpa [inst] using ht'
  subst this
  have harmy : ((inst n t v d B W).army.getD 0 default).2 = B := rfl
  rw [harmy]
  simpa [inst_k, αW, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS.1] using hS.2

theorem one_le_thr {j : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t j) : 1 ≤ thr t d j := by
  unfold thr; rw [Nat.one_le_div_iff (by omega)]; omega

theorem t_le_thr_mul (hd : 1 ≤ d) (j : ℕ) : t j ≤ thr t d j * d :=
  (ceil_div_le_iff hd).mp le_rfl

/-- Invariant of the witness run during the `NORMAL` phase. -/
structure WN (S : Finset ℕ) (s : State) : Prop where
  frame : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) (αW t d S) s
  rounds : s.roundsLeft = 1
  phase : s.phase = .normal
  nodup : s.Q.Nodup
  ehex : ∀ j < n, (s.units (n + j)).hex = e j
  bucket : ∀ i ∈ s.bucket, (s.units i).side = .enemy
  fresh : ∀ j < n, j ∈ s.queue →
    (s.units j).pool = (αW t d S j).count * 5 ∧ (s.units j).hex = p j ∧
    (s.units (n + j)).pool = t j ∧ (s.units (n + j)).defending = false
  killed : ∀ j ∈ S, j ∉ s.queue → (s.units (n + j)).pool = 0

variable {S : Finset ℕ}

theorem lt_of_alive {α : ℕ → SlotAlloc} {s : State}
    (hf : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s) {i : ℕ}
    (ha : (s.units i).alive) : i < n + n := by
  by_contra hi
  have hp := hf.pool i
  unfold initUnits at hp
  rw [if_neg (by simp; omega), if_neg (by simp; omega)] at hp
  unfold Stack.alive at ha
  have : (default : Stack).pool = 0 := rfl
  omega

theorem WN.init (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) (hS : S ⊆ Finset.range n) :
    WN (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S
      (initState (inst n t v d B W) (αW t d S)) where
  frame := Frame.init _
  rounds := rfl
  phase := rfl
  nodup := by simpa [State.Q, initState] using normalQueue_nodup _ _
  ehex j hj := by simp [initState, init_enemy _ hj]
  bucket := by simp [initState]
  fresh j hj _ := by
    simp only [initState, init_enemy _ hj, init_player _ hj]
    exact ⟨pool_slotType (by simp [αW]), trivial, trivial, trivial⟩
  killed j hjS hjq := by
    exfalso; apply hjq
    have hj : j < n := Finset.mem_range.mp (hS hjS)
    simp only [initState, normalQueue]
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter, List.mem_range]
    refine ⟨by simp; omega, ?_⟩
    simp only [decide_eq_true_eq, Stack.alive, init_player _ hj]
    rw [pool_slotType (by simp [αW])]
    have := one_le_thr (t := t) hd (ht j hj)
    simp only [αW, hjS, ↓reduceIte]
    omega

/-- One step of the witness run in the `NORMAL` phase. -/
theorem WN.step (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) (hS : S ⊆ Finset.range n) {s : State}
    (hw : WN (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s) {i : ℕ} {q : List ℕ}
    (hq : s.queue = i :: q) :
    ∃ s', Step (inst n t v d B W) s s' ∧
      WN (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s' ∧ s'.queue = q := by
  have hnq := head_not_mem_after hq hw.nodup
  have hjq : ∀ j ∈ q, j ≠ i := fun j hj e => hnq (e ▸ List.mem_append_left _ hj)
  by_cases ha : (s.units i).alive
  · rcases hside : (s.units i).side with _ | _
    · -- a player stack: attack its own enemy from its own hex
      have hin : i < n := init_side_player (by rw [← hw.frame.side]; exact hside)
      have hiq : i ∈ s.queue := by simp [hq]
      obtain ⟨hpool, hhex, hepool, hedef⟩ := hw.fresh i hin hiq
      have hiS : i ∈ S := by
        by_contra hiS
        simp [αW, hiS] at hpool; unfold Stack.alive at ha; omega
      obtain ⟨hty, -⟩ := player_facts hw.frame hin ha
      have hti := ht i hin
      have hstep := Step.playerAttack (I := inst n t v d B W) (dest := (s.units i).hex)
        (t := n + i) hq ha hside (start_mem_reach _ _) (by simp; omega)
        (by unfold Stack.alive; omega)
        (by rw [hw.frame.side, init_enemy _ hin])
        (by rw [hw.ehex i hin, hhex]; exact adj_p_e i)
      refine ⟨_, hstep, ?_, rfl⟩
      have hs' := hw.frame.step hstep
      -- the enemy of block `i` dies
      have hdead : (resolveAttack s.units i (n + i) (s.units i).hex (n + i)).pool = 0 := by
        rw [resolveAttack_pool_target (by omega), hepool]
        have hb : blow { activate (s.units i) with hex := (s.units i).hex } (s.units (n + i))
            = thr t d i * d := by
          have hcnt : ({ activate (s.units i) with hex := (s.units i).hex } : Stack).count
              = thr t d i := by
            simp only [Stack.count, activate, hty, playerType, hpool, αW, if_pos hiS]
            omega
          unfold blow
          rw [hcnt]
          have hdefE : (s.units (n + i)).defEff = 1 := by
            have hty' := hw.frame.type (n + i)
            rw [init_enemy _ hin] at hty'
            simp [Stack.defEff, hedef, hty', enemyType]
          have hatt : ({ activate (s.units i) with hex := (s.units i).hex } : Stack).type
              = playerType d := by simp [activate, hty]
          rw [hdefE, hatt]
          simp only [playerType, Nat.cast_one, sub_self]
          exact damage_zero (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
            (by have := one_le_thr (t := t) hd hti; omega) (by omega)))
        rw [hb]
        have := t_le_thr_mul (t := t) hd i
        omega
      refine ⟨hs', hw.rounds, hw.phase, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hstep.Q_sub (by rw [hw.rounds])).2.2 hw.nodup
      · intro j hj
        rw [hstep.hex_of_enemy (by rw [hw.frame.side, init_enemy _ hj]), hw.ehex j hj]
      · intro x hx
        rw [hstep.side]; exact hw.bucket x hx
      · intro j hj hjq'
        have hji := hjq j hjq'
        obtain ⟨a1, a2, a3, a4⟩ := hw.fresh j hj (by simp [hq, hjq'])
        simp only
        rw [resolveAttack_of_ne hji (by omega), resolveAttack_of_ne (by omega) (by omega)]
        exact ⟨a1, a2, a3, a4⟩
      · intro j hjS hjq'
        simp only at hjq' ⊢
        by_cases hji : j = i
        · subst hji; exact hdead
        · rw [resolveAttack_of_ne (by omega) (by omega)]
          exact hw.killed j hjS (by simp [hq, hji, hjq'])
    · -- an enemy stack: `(‡)` makes it `WAIT`
      have hstep := Step.enemyWait (I := inst n t v d B W) hw.phase hq ha hside
      refine ⟨_, hstep, ?_, rfl⟩
      have hi2 := lt_of_alive hw.frame ha
      have hni : n ≤ i := by
        by_contra h
        rw [hw.frame.side, init_player _ (by omega)] at hside; cases hside
      refine ⟨hw.frame.step hstep, hw.rounds, hw.phase, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hstep.Q_sub (by rw [hw.rounds])).2.2 hw.nodup
      · intro j hj
        rw [hstep.hex_of_enemy (by rw [hw.frame.side, init_enemy _ hj]), hw.ehex j hj]
      · intro x hx
        rw [hstep.side]
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw.bucket x hx
        · exact hside
      · intro j hj hjq'
        obtain ⟨a1, a2, a3, a4⟩ := hw.fresh j hj (by simp [hq, hjq'])
        have hji : j ≠ i := by omega
        dsimp only
        rw [update_of_ne hji]
        by_cases hnj : n + j = i
        · rw [← hnj, update_self]; exact ⟨a1, a2, by simpa [activate] using a3, rfl⟩
        · rw [update_of_ne hnj]; exact ⟨a1, a2, a3, a4⟩
      · intro j hjS hjq'
        have hj : j < n := Finset.mem_range.mp (hS hjS)
        have hji : j ≠ i := by omega
        have := hw.killed j hjS (by simp [hq, hji, hjq'])
        dsimp only
        by_cases hnj : n + j = i
        · rw [← hnj, update_self]; simpa [activate] using this
        · rw [update_of_ne hnj]; exact this
  · -- a dead stack is skipped
    have hstep := Step.skip (I := inst n t v d B W) hq ha
    refine ⟨_, hstep, ?_, rfl⟩
    refine ⟨hw.frame.step hstep, hw.rounds, hw.phase, ?_, hw.ehex, hw.bucket, ?_, ?_⟩
    · exact (hstep.Q_sub (by rw [hw.rounds])).2.2 hw.nodup
    · intro j hj hjq'; exact hw.fresh j hj (by simp [hq, hjq'])
    · intro j hjS hjq'
      by_cases hji : j = i
      · subst hji
        have hj : j < n := Finset.mem_range.mp (hS hjS)
        obtain ⟨hpool, -⟩ := hw.fresh j hj (by simp [hq])
        exfalso; apply ha
        unfold Stack.alive
        rw [hpool]
        simp only [αW, if_pos hjS]
        have := one_le_thr (t := t) hd (ht j hj)
        omega
      · exact hw.killed j hjS (by simp [hq, hji]; exact hjq')

/-- The whole `NORMAL` phase of the witness run. -/
theorem WN.run (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) (hS : S ⊆ Finset.range n) :
    ∀ (L : List ℕ) (s : State),
      WN (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s → s.queue = L →
      ∃ s', Relation.ReflTransGen (Step (inst n t v d B W)) s s' ∧
        WN (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    obtain ⟨s1, h1, hw1, hq1⟩ := hw.step hd ht hS hq
    obtain ⟨s2, h2, hw2, hq2⟩ := WN.run hd ht hS q s1 hw1 hq1
    exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩

/-- Invariant of the witness run during the `WAIT` phase. -/
structure WW (S : Finset ℕ) (s : State) : Prop where
  frame : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) (αW t d S) s
  rounds : s.roundsLeft = 1
  phase : s.phase = .wait
  queue : ∀ i ∈ s.queue, (s.units i).side = .enemy
  killed : ∀ j ∈ S, (s.units (n + j)).pool = 0

theorem WW.run (hS : S ⊆ Finset.range n) :
    ∀ (L : List ℕ) (s : State),
      WW (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s → s.queue = L →
      ∃ s', Relation.ReflTransGen (Step (inst n t v d B W)) s s' ∧
        WW (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    have next : ∀ s1, Step (inst n t v d B W) s s1 → s1.queue = q → s1.phase = .wait →
        (∀ j ∈ S, (s1.units (n + j)).pool = (s.units (n + j)).pool) →
        ∃ s', Relation.ReflTransGen (Step (inst n t v d B W)) s s' ∧
          WW (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s' ∧ s'.queue = [] := by
      intro s1 h1 hq1 hph hpool
      have hr := h1.Q_sub (by rw [hw.rounds])
      have hw1 : WW (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S s1 := by
        refine ⟨hw.frame.step h1, hr.1.trans hw.rounds, hph, ?_, ?_⟩
        · intro x hx
          rw [h1.side]; exact hw.queue x (by simp [hq, hq1 ▸ hx])
        · intro j hj; rw [hpool j hj]; exact hw.killed j hj
      obtain ⟨s2, h2, hw2, hq2⟩ := WW.run hS q s1 hw1 hq1
      exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩
    by_cases ha : (s.units i).alive
    · have hside := hw.queue i (by simp [hq])
      refine next _ (Step.enemyDefend hw.phase hq ha hside) rfl hw.phase ?_
      intro j _; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
    · exact next _ (Step.skip hq ha) rfl hw.phase (fun _ _ => rfl)

/-- **Proposition 1.1, lower bound**: for every `S` feasible for `(K)` there is a feasible
allocation and a complete play destroying at least `Σ_{j∈S} v_j`. -/
theorem lower (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) {S : Finset ℕ}
    (hS : S ∈ Knapsack.feasible (thr t d) n B) :
    ∃ α, Feasible (inst n t v d B W) α ∧ ∃ s,
      Relation.ReflTransGen (Step (inst n t v d B W)) (initState (inst n t v d B W) α) s ∧
      Done s ∧ ∑ j ∈ S, v j ≤ destroyed (inst n t v d B W) s := by
  have hSr := (Knapsack.mem_feasible.mp hS).1
  refine ⟨αW t d S, αW_feasible hS, ?_⟩
  obtain ⟨s1, h1, hw1, hq1⟩ := WN.run (v := v) (B := B) (W := W) hd ht hSr _ _
    (WN.init hd ht hSr) rfl
  have hstep := Step.toWait (I := inst n t v d B W) hw1.phase hq1
  have hw2 : WW (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) S
      { s1 with phase := .wait, queue := s1.bucket.mergeSort (waitLe s1.units), bucket := [] } :=
    ⟨hw1.frame.step hstep, hw1.rounds, rfl,
      fun x hx => hw1.bucket x ((List.mergeSort_perm _ _).mem_iff.mp hx),
      fun j hj => hw1.killed j hj (by simp [hq1])⟩
  obtain ⟨s3, h3, hw3, hq3⟩ := WW.run hSr _ _ hw2 rfl
  refine ⟨s3, h1.trans (Relation.ReflTransGen.head hstep h3), ⟨hw3.phase, hq3, by
    rw [hw3.rounds]⟩, ?_⟩
  rw [destroyed_eq ht hw3.frame, ← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset
  intro j hj
  rw [Finset.mem_filter]
  exact ⟨hSr hj, hw3.killed j hj⟩

end Homm3.Corridor
