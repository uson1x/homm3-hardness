import Homm3.CorridorGame

/-!
# Stage 4d. Proposition 1.1 on the corridor family

Paper: Appendix E, "Proposition 1.1, and what matching reach has to mean" — the two halves
"The optimum is at most `(K)`" and "The optimum is at least `(K)`", specialized to the
family the reduction constructs (`inst n t v d B W`), where the matching reach is
discharged by Lemma E.9/E.10's metric argument (here: `Corridor.no_foreign_strike`).

Upper bound: an invariant of every reachable state (`UInv`), whose key clause is
`t_j ≤ pool(E_j) + [slot j has left the queue] · c_j · d`: the enemy of block `j` can only
lose hit points to the one blow of slot `j` (Lemma E.1 + E.3 + E.4), and that blow delivers
at most nominal (§2.4, `damage_le_nominal`).
-/

namespace Homm3.Corridor

open Function

variable {n : ℕ} {t v : ℕ → ℕ} {d B W : ℕ}

/-- Thresholds `b_j = ⌈t_j / d⌉`. -/
def thr (t : ℕ → ℕ) (d : ℕ) (j : ℕ) : ℕ := (t j + d - 1) / d

theorem ceil_div_le_iff {tj d c : ℕ} (hd : 1 ≤ d) : (tj + d - 1) / d ≤ c ↔ tj ≤ c * d := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega), Nat.succ_mul]
  generalize c * d = x
  omega

/-- A living player stack of the corridor is of the player type, with pool `≤ 5 c_j`. -/
theorem player_facts {α : ℕ → SlotAlloc} {s : State}
    (hf : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s) {i : ℕ}
    (hi : i < n) (ha : (s.units i).alive) :
    (s.units i).type = playerType d ∧ (s.units i).pool ≤ (α i).count * 5 := by
  have hty := hf.type i
  have hp := hf.pool i
  rw [init_player α hi] at hty hp
  simp only at hty hp
  unfold slotType at hty hp
  unfold Stack.alive at ha
  split_ifs at hty hp with h0
  · exact ⟨hty, by simpa [playerType] using hp⟩
  · exfalso; simp [show (default : CType).hp = 0 from rfl] at hp; omega

/-- **Every blow of a player stack on a corridor enemy is at most nominal** (§2.4:
`Δ = 1 − defEff ≤ 0` whether or not the `DEFEND` bonus is up). -/
theorem blow_le_nominal {a tg : Stack} {c : ℕ} (hd : 1 ≤ d) (hty : a.type = playerType d)
    (h1 : 1 ≤ a.pool) (h2 : a.pool ≤ c * 5) (htg : tg.type.dfn = 1) :
    blow a tg ≤ c * d := by
  unfold blow
  have hcnt : a.count = (a.pool + 4) / 5 := by
    simp [Stack.count, hty, playerType]
  have hc1 : 1 ≤ a.count := by rw [hcnt]; omega
  have hc2 : a.count ≤ c := by rw [hcnt]; omega
  have hΔ : ((a.type.att : ℤ) - tg.defEff) ≤ 0 := by
    have hatt : a.type.att = 1 := by rw [hty]; rfl
    have hdef : 1 ≤ tg.defEff := by unfold Stack.defEff; rw [htg]; omega
    rw [hatt]; omega
  rw [hty] at hΔ ⊢
  exact (damage_le_nominal hΔ (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (show (playerType d).dmg ≠ 0 by simp [playerType]; omega)))).trans
    (Nat.mul_le_mul_right d hc2)

/-- The upper-bound invariant. -/
structure UInv (α : ℕ → SlotAlloc) (s : State) : Prop where
  frame : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s
  rounds : s.roundsLeft = 1
  nodup : s.Q.Nodup
  ehex : ∀ j < n, (s.units (n + j)).hex = e j
  phex : ∀ j < n, j ∈ s.Q → (s.units j).hex = p j
  key : ∀ j < n, t j ≤ (s.units (n + j)).pool + (if j ∈ s.Q then 0 else (α j).count * d)

theorem UInv.init (α : ℕ → SlotAlloc) :
    UInv (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α
      (initState (inst n t v d B W) α) where
  frame := Frame.init α
  rounds := rfl
  nodup := by simpa [State.Q, initState] using normalQueue_nodup _ _
  ehex j hj := by simp [initState, init_enemy α hj]
  phex j hj _ := by simp [initState, init_player α hj]
  key j hj := by simp [initState, init_enemy α hj]

theorem key_transfer {tj P X : ℕ} {Q Q' : List ℕ} {j : ℕ}
    (hk : tj ≤ P + (if j ∈ Q then 0 else X)) (hsub : j ∈ Q' → j ∈ Q) :
    tj ≤ P + (if j ∈ Q' then 0 else X) := by
  by_cases h1 : j ∈ Q'
  · rw [if_pos h1]; rw [if_pos (hsub h1)] at hk; exact hk
  · rw [if_neg h1]; split_ifs at hk <;> omega

theorem UInv.step {α : ℕ → SlotAlloc} {s s' : State} (hd : 1 ≤ d)
    (hu : UInv (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s)
    (h : Step (inst n t v d B W) s s') :
    UInv (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s' := by
  have hr : s.roundsLeft ≤ 1 := by rw [hu.rounds]
  obtain ⟨hr', hsub, hnd⟩ := h.Q_sub hr
  refine ⟨hu.frame.step h, hr'.trans hu.rounds, hnd hu.nodup, ?_, ?_, ?_⟩
  · intro j hj
    rw [h.hex_of_enemy (by rw [hu.frame.side, init_enemy α hj]), hu.ehex j hj]
  · intro j hj hjQ
    rw [h.hex_of_mem hr hu.nodup hjQ, hu.phex j hj (hsub j hjQ)]
  · intro j hj
    rcases h.pool_cases (n + j) with heq | ⟨i, q, dest, t0, hq, ha, hs, hdst, ht0, hta, hts,
      hadj, hus, hq', hb'⟩
    · rw [heq]; exact key_transfer (hu.key j hj) (hsub j)
    -- the attack case: geometry first
    have hiQ : i ∈ s.Q := by simp [State.Q, hq]
    have hin : i < n := init_side_player (by rw [← hu.frame.side]; exact hs)
    obtain ⟨hty, hpl⟩ := player_facts hu.frame hin ha
    rw [inst_N] at ht0
    obtain ⟨j0, hj0, rfl⟩ := enemy_id ht0 (by rw [← hu.frame.side]; exact hts)
    rw [hu.ehex j0 hj0] at hadj
    have hreach : dest ∈ reach (free (inst n t v d B W) s.units i) (p i) 2 := by
      have := hdst; unfold reachOf at this; rwa [hu.phex i hin hiQ, hty] at this
    have hj0i : j0 = i := no_foreign_strike hreach hadj
    subst hj0i
    have hiQ' : j0 ∉ s'.Q := by
      simp only [State.Q, hq', hb']; exact head_not_mem_after hq hu.nodup
    by_cases hjj : j = j0
    · subst hjj
      rw [hus, resolveAttack_pool_target (by omega)]
      have hk := hu.key j hj
      rw [if_pos hiQ] at hk
      rw [if_neg hiQ']
      have hb := blow_le_nominal (tg := s.units (n + j)) (c := (α j).count) hd
        (a := { activate (s.units j) with hex := dest }) (by simpa [activate] using hty)
        (by simp only [activate]; exact Nat.succ_le_of_lt ha) (by simpa [activate] using hpl)
        (by rw [hu.frame.type, init_enemy α hj]; rfl)
      generalize blow _ _ = x at hb ⊢
      generalize (α j).count * d = y at hb ⊢
      omega
    · have heq : (s'.units (n + j)).pool = (s.units (n + j)).pool := by
        rw [hus, resolveAttack_of_ne (by omega) (by omega)]
      rw [heq]; exact key_transfer (hu.key j hj) (hsub j)

theorem UInv.reach {α : ℕ → SlotAlloc} {s : State} (hd : 1 ≤ d)
    (hs : Relation.ReflTransGen (Step (inst n t v d B W)) (initState (inst n t v d B W) α) s) :
    UInv (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s := by
  induction hs with
  | refl => exact UInv.init α
  | tail _ h ih => exact ih.step hd h

/-- Under a feasible allocation the slots hold at most `B` creatures in total. -/
theorem sum_count_le {α : ℕ → SlotAlloc} (hα : Feasible (inst n t v d B W) α) :
    ∑ j ∈ Finset.range n, (α j).count ≤ B := by
  have h := hα.2 0 (by simp [inst])
  simp only [inst_k] at h
  rw [Finset.sum_filter_of_ne] at h
  · simpa [inst] using h
  · intro j hj hne
    have := hα.1 j (by simpa using Finset.mem_range.mp hj) (Nat.pos_of_ne_zero hne)
    simp [inst] at this; exact this

/-- **Proposition 1.1, upper bound** (on the corridor family): every play under every
feasible allocation destroys at most `OPT = max{Σ_S v : Σ_S ⌈t_j/d⌉ ≤ B}`. -/
theorem upper (hd : 1 ≤ d) (ht : ∀ j < n, 1 ≤ t j) {α : ℕ → SlotAlloc}
    (hα : Feasible (inst n t v d B W) α) {s : State}
    (hs : Relation.ReflTransGen (Step (inst n t v d B W)) (initState (inst n t v d B W) α) s) :
    destroyed (inst n t v d B W) s ≤ Knapsack.OPT v (thr t d) n B := by
  have hu := UInv.reach hd hs
  rw [destroyed_eq ht hu.frame]
  set S := (Finset.range n).filter (fun j => (s.units (n + j)).pool = 0) with hS
  have hsum : (∑ j ∈ Finset.range n, if (s.units (n + j)).pool = 0 then v j else 0) =
      ∑ j ∈ S, v j := by rw [hS, Finset.sum_filter]
  rw [hsum]
  apply Knapsack.le_OPT
  rw [Knapsack.mem_feasible]
  refine ⟨Finset.filter_subset _ _, ?_⟩
  calc ∑ j ∈ S, thr t d j ≤ ∑ j ∈ S, (α j).count := by
        apply Finset.sum_le_sum
        intro j hjS
        rw [hS, Finset.mem_filter, Finset.mem_range] at hjS
        have hk := hu.key j hjS.1
        rw [hjS.2, zero_add] at hk
        have h1 := ht j hjS.1
        split_ifs at hk
        · omega
        · exact (ceil_div_le_iff hd).mpr hk
    _ ≤ ∑ j ∈ Finset.range n, (α j).count :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ B := sum_count_le hα

end Homm3.Corridor
