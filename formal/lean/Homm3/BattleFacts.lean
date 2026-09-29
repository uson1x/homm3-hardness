import Homm3.Battle

/-!
# Stage 4b. General facts about one step of the round semantics

These hold for every instance.  They are the model-level content of Lemma E.1
("one terminal action per round, issued from the deployment hex") and of the remark that
the defence never moves: static fields never change, pools never grow, only the acting
player's hex changes, and a stack leaves the queue for good once it has acted.
-/

namespace Homm3

open Function

/-- The fields no step ever changes. -/
def Stack.St (u : Stack) : Side × ℕ × CType × ℕ := (u.side, u.slot, u.type, u.init)

theorem resolveAttack_of_ne {us : ℕ → Stack} {i t j : ℕ} {dest : Hex} (hi : j ≠ i)
    (ht : j ≠ t) : resolveAttack us i t dest j = us j := by
  unfold resolveAttack
  split_ifs <;> simp [update_of_ne hi, update_of_ne ht]

theorem resolveAttack_St (us : ℕ → Stack) (i t : ℕ) (dest : Hex) (j : ℕ) :
    (resolveAttack us i t dest j).St = (us j).St := by
  unfold resolveAttack
  split_ifs <;> simp only [update_apply] <;> split_ifs <;> subst_vars <;>
    simp [Stack.St, Stack.hit, activate]

theorem resolveAttack_pool_le (us : ℕ → Stack) (i t : ℕ) (dest : Hex) (j : ℕ) :
    (resolveAttack us i t dest j).pool ≤ (us j).pool := by
  unfold resolveAttack
  split_ifs <;> simp only [update_apply] <;> split_ifs <;> subst_vars <;>
    simp [Stack.hit, activate]

/-- The target's hex is untouched: only the attacker moves. -/
theorem resolveAttack_hex_of_ne {us : ℕ → Stack} {i t j : ℕ} {dest : Hex} (hi : j ≠ i) :
    (resolveAttack us i t dest j).hex = (us j).hex := by
  unfold resolveAttack
  split_ifs <;> simp only [update_apply] <;> split_ifs <;> subst_vars <;>
    simp_all [Stack.hit, activate]

/-- The target's pool after the attack, when attacker and target differ. -/
theorem resolveAttack_pool_target {us : ℕ → Stack} {i t : ℕ} {dest : Hex} (hit : i ≠ t) :
    (resolveAttack us i t dest t).pool =
      (us t).pool - blow { activate (us i) with hex := dest } (us t) := by
  unfold resolveAttack
  split_ifs <;> simp [Ne.symm hit, Stack.hit]

section Step

variable {I : Instance} {s s' : State}

/-- Static fields are invariant. -/
theorem Step.St (h : Step I s s') (j : ℕ) : (s'.units j).St = (s.units j).St := by
  cases h with
  | skip => rfl
  | enemyWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
  | enemyDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
  | playerWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
  | playerDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
  | playerMove => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
  | playerAttack => exact resolveAttack_St _ _ _ _ _
  | toWait => rfl
  | nextRound => simp [newRound, Stack.St]

theorem Step.side (h : Step I s s') (j : ℕ) : (s'.units j).side = (s.units j).side :=
  congrArg Prod.fst (h.St j)
theorem Step.type (h : Step I s s') (j : ℕ) : (s'.units j).type = (s.units j).type :=
  congrArg (fun x => x.2.2.1) (h.St j)
theorem Step.init (h : Step I s s') (j : ℕ) : (s'.units j).init = (s.units j).init :=
  congrArg (fun x => x.2.2.2) (h.St j)

/-- Pools never grow. -/
theorem Step.pool_le (h : Step I s s') (j : ℕ) : (s'.units j).pool ≤ (s.units j).pool := by
  cases h with
  | skip => exact le_rfl
  | enemyWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | enemyDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerMove => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerAttack => exact resolveAttack_pool_le _ _ _ _ _
  | toWait => exact le_rfl
  | nextRound => simp [newRound]

/-- Only a player acting at its terminal action changes its hex; in particular enemy
stacks never move (the defence never initiates). -/
theorem Step.hex_of_enemy (h : Step I s s') {j : ℕ} (hj : (s.units j).side = .enemy) :
    (s'.units j).hex = (s.units j).hex := by
  cases h with
  | skip => rfl
  | enemyWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | enemyDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp_all
  | playerDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp_all
  | playerMove hq ha hs hd =>
    simp only [update_apply]; split_ifs with he
    · subst he; rw [hs] at hj; cases hj
    · rfl
  | playerAttack hq ha hs hd ht hta hts hadj =>
    refine resolveAttack_hex_of_ne ?_
    rintro rfl; rw [hs] at hj; cases hj
  | toWait => rfl
  | nextRound => simp [newRound]

/-- The queue-and-bucket multiset of a state. -/
def State.Q (s : State) : List ℕ := s.queue ++ s.bucket

/-- Inside one round (no `nextRound` step), a step only removes stacks from the
queue-and-bucket, keeps it duplicate-free, and does not change the round counter. -/
theorem Step.Q_sub (h : Step I s s') (hr : s.roundsLeft ≤ 1) :
    s'.roundsLeft = s.roundsLeft ∧ (∀ j ∈ s'.Q, j ∈ s.Q) ∧ (s.Q.Nodup → s'.Q.Nodup) := by
  cases h with
  | skip hq =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj; simp only [State.Q, hq, List.mem_append, List.mem_cons] at hj ⊢; tauto
    · simp only [State.Q, hq, List.cons_append, List.nodup_cons]; exact fun h => h.2
  | enemyWait _ hq | playerWait _ hq =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      simp only [State.Q, hq, List.mem_append, List.mem_cons] at hj ⊢
      tauto
    · simp only [State.Q, hq]
      intro hn
      rw [← List.append_assoc]
      exact (List.perm_append_singleton _ _).nodup_iff.mpr (by simpa using hn)
  | enemyDefend _ hq | playerDefend hq | playerMove hq | playerAttack hq =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj; simp only [State.Q, hq, List.mem_append, List.mem_cons] at hj ⊢; tauto
    · simp only [State.Q, hq, List.cons_append, List.nodup_cons]; exact fun h => h.2
  | toWait _ hq =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      simp only [State.Q, hq, List.nil_append, List.append_nil] at hj ⊢
      exact (List.mergeSort_perm _ _).mem_iff.mp hj
    · simp only [State.Q, hq, List.nil_append, List.append_nil]
      exact fun hn => (List.mergeSort_perm _ _).nodup_iff.mpr hn
  | nextRound _ _ h1 => omega

/-- The head of the queue that takes a terminal action leaves the queue-and-bucket. -/
theorem head_not_mem_after {s : State} {i : ℕ} {q : List ℕ} (hq : s.queue = i :: q)
    (hn : s.Q.Nodup) : i ∉ q ++ s.bucket := by
  simp only [State.Q, hq, List.cons_append, List.nodup_cons] at hn
  exact hn.1

/-- Inside one round, a stack still queued (or waiting) has not moved. -/
theorem Step.hex_of_mem (h : Step I s s') (hr : s.roundsLeft ≤ 1) (hn : s.Q.Nodup) {j : ℕ}
    (hj : j ∈ s'.Q) : (s'.units j).hex = (s.units j).hex := by
  cases h with
  | skip => rfl
  | enemyWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | enemyDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerWait => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerDefend => simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerMove hq ha hs hd =>
    rename_i i q dest
    have hji : j ≠ i := by rintro rfl; exact head_not_mem_after hq hn hj
    simp only [update_apply, hji, ↓reduceIte]
  | playerAttack hq ha hs hd ht hta hts hadj =>
    rename_i i q dest t
    have hji : j ≠ i := by rintro rfl; exact head_not_mem_after hq hn hj
    exact resolveAttack_hex_of_ne hji
  | toWait => rfl
  | nextRound _ _ h1 => omega

/-- Pools change only in a `WALK_AND_ATTACK`. -/
theorem Step.pool_cases (h : Step I s s') (j : ℕ) :
    (s'.units j).pool = (s.units j).pool ∨
    ∃ i q dest t, s.queue = i :: q ∧ (s.units i).alive ∧ (s.units i).side = .player ∧
      dest ∈ reachOf I s.units i ∧ t < I.N ∧ (s.units t).alive ∧
      (s.units t).side = .enemy ∧ Hex.Adj dest (s.units t).hex ∧
      s'.units = resolveAttack s.units i t dest ∧ s'.queue = q ∧ s'.bucket = s.bucket := by
  cases h with
  | skip => exact Or.inl rfl
  | enemyWait => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | enemyDefend => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerWait => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerDefend => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerMove => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerAttack hq ha hs hd ht hta hts hadj =>
    exact Or.inr ⟨_, _, _, _, hq, ha, hs, hd, ht, hta, hts, hadj, rfl, rfl, rfl⟩
  | toWait => exact Or.inl rfl
  | nextRound => left; simp [newRound]

end Step

theorem normalQueue_nodup (N : ℕ) (us : ℕ → Stack) : (normalQueue N us).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_range.filter _)

/-- **Lemma E.1, model form (hex half).** In any instance with `R = 1`, along every play
from the starting position of any allocation, the queue-and-bucket stays duplicate-free and
every stack in it — i.e. every stack that has not yet taken its terminal action — still
stands on its deployment hex. -/
theorem lemmaE1 {I : Instance} {α : ℕ → SlotAlloc} (hR : I.R = 1) {s : State}
    (hs : Relation.ReflTransGen (Step I) (initState I α) s) :
    s.roundsLeft = 1 ∧ s.Q.Nodup ∧ ∀ j ∈ s.Q, (s.units j).hex = (initUnits I α j).hex := by
  induction hs with
  | refl =>
    refine ⟨hR, ?_, fun _ _ => rfl⟩
    simpa [State.Q, initState] using normalQueue_nodup _ _
  | tail _ h ih =>
    obtain ⟨hr, hn, hx⟩ := ih
    obtain ⟨hr', hsub, hnd⟩ := h.Q_sub (by rw [hr])
    exact ⟨hr'.trans hr, hnd hn, fun j hj => (h.hex_of_mem (by rw [hr]) hn hj).trans
      (hx j (hsub j hj))⟩

/-- Inside round 1 the queue-and-bucket only shrinks along a play. -/
theorem Q_antitone {I : Instance} {s s' : State} (hr : s.roundsLeft = 1)
    (h : Relation.ReflTransGen (Step I) s s') : s'.roundsLeft = 1 ∧ ∀ j ∈ s'.Q, j ∈ s.Q := by
  induction h with
  | refl => exact ⟨hr, fun _ h => h⟩
  | tail _ h ih =>
    obtain ⟨hr', hsub⟩ := ih
    obtain ⟨hr'', hsub', -⟩ := h.Q_sub (by rw [hr'])
    exact ⟨hr''.trans hr', fun j hj => hsub j (hsub' j hj)⟩

/-- **Lemma E.1, model form (one blow).** Once a stack has taken its terminal action
(it was the head of the queue and the step neither re-queued nor bucketed it), it is never
activated again in round 1 — so it delivers at most one blow. -/
theorem lemmaE1_once {I : Instance} {α : ℕ → SlotAlloc} (hR : I.R = 1)
    {s₁ s₂ s₃ : State} {i : ℕ} {q : List ℕ}
    (h₁ : Relation.ReflTransGen (Step I) (initState I α) s₁) (hq : s₁.queue = i :: q)
    (hq₂ : s₂.queue = q) (hb₂ : s₂.bucket = s₁.bucket) (h₂ : Step I s₁ s₂)
    (h₃ : Relation.ReflTransGen (Step I) s₂ s₃) : i ∉ s₃.Q := by
  obtain ⟨hr, hn, -⟩ := lemmaE1 hR h₁
  have hr₂ : s₂.roundsLeft = 1 := ((h₂.Q_sub (by rw [hr])).1).trans hr
  intro hi
  have := (Q_antitone hr₂ h₃).2 i hi
  simp only [State.Q, hq₂, hb₂] at this
  exact head_not_mem_after hq hn this

end Homm3
