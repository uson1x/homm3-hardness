import Homm3.Theorem4

/-!
# Session 3, target 2 (cont.). Lemma E.20 in full, Lemma E.2, and local seat capacity

Paper: Appendix E, Lemma E.20 (damage accounting on `G_F`, "not necessarily attack-only"),
Lemma E.2 (retaliation is inert), and the Remark after Corollary 4.2 (an enemy has six
neighbours, so at most six stacks strike it in one round).

* **The R9 order in round 1** (`orderInv`, any instance with `R = 1`): in the `NORMAL` phase no
  enemy has its `DEFEND` bonus up, and a living enemy that has left the queue is in the `WAIT`
  bucket; in the `WAIT` phase the queue is sorted by `waitLe` (speed ascending), and a living
  enemy that has left the queue has its `DEFEND` bonus up.  Consequence
  (`wait_attack_defended`): when every army type is faster than every enemy, a player stack
  that strikes in the `WAIT` phase — a stack that waited — meets the postponed `DEFEND` of its
  target.
* **Lemma E.20** (`ThmF.lemmaE20`): on `G_F`, along every play (not only attack-only), a strike
  record `τ`, blow record `β` and phase record `ω` exist with: striker sets pairwise disjoint;
  absorbed `= min(T, Σ β)`; a blow issued without waiting (`ω = false`) is exactly nominal
  `a_i`; a waiting blow (`ω = true`) is `damage(1, a_i, Δ = −1)`, which is **at most nominal,
  with equality exactly when `a_i = 1`** (never "strictly less"); dead only if
  `Σ_{i ∈ S_g} a_i ≥ T`; and if no striker of `E_g` waited and `Σ_{i ∈ S_g} a_i ≥ T`, `E_g` is
  dead.
* **Lemma E.2** (`Fam.lemmaE2`, every layout of the stock-one family): a player stack is
  untouched until its terminal action, then loses at most one point; no player creature dies.
* **Seat capacity** (`ThmF.seat_capacity`): living stacks occupy distinct hexes
  (`ThmF.distinct_hexes`), strikers stay on a neighbour of their target and never die, so at
  most six stacks strike one enemy in round 1 — seven strikers do not fit six seats.
-/

namespace Homm3

open Function

variable {I : Instance} {α : ℕ → SlotAlloc}

/-! ## The `WAIT` order -/

theorem waitLe_trans (us : ℕ → Stack) (x y z : ℕ) (h1 : waitLe us x y = true)
    (h2 : waitLe us y z = true) : waitLe us x z = true := by
  simp only [waitLe, decide_eq_true_eq] at *
  omega

theorem waitLe_total (us : ℕ → Stack) (x y : ℕ) : (waitLe us x y || waitLe us y x) = true := by
  simp only [waitLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem waitLe_congr {us us' : ℕ → Stack} (h : ∀ i, (us' i).St = (us i).St) :
    waitLe us' = waitLe us := by
  funext x y
  have hx := h x; have hy := h y
  simp only [Stack.St, Prod.mk.injEq] at hx hy
  simp only [waitLe, hx.1, hx.2.1, hx.2.2.1, hy.1, hy.2.1, hy.2.2.1]

theorem resolveAttack_St' {us : ℕ → Stack} {i t : ℕ} {dest : Hex} :
    ∀ j, (resolveAttack us i t dest j).St = (us j).St := resolveAttack_St us i t dest

/-- The order facts of round 1. -/
structure OrderInv (I : Instance) (s : State) : Prop where
  n1 : s.phase = .normal → ∀ g < I.n, (s.units (I.k + g)).defending = false
  n2 : s.phase = .normal → ∀ g < I.n, I.k + g ∉ s.queue → (s.units (I.k + g)).alive →
    I.k + g ∈ s.bucket
  w1 : s.phase = .wait → s.queue.Pairwise (fun x y => waitLe s.units x y = true)
  w2 : s.phase = .wait → ∀ g < I.n, I.k + g ∉ s.queue → (s.units (I.k + g)).alive →
    (s.units (I.k + g)).defending = true

theorem pairwise_tail_static {us us' : ℕ → Stack} {i : ℕ} {q : List ℕ}
    (h : (i :: q).Pairwise (fun x y => waitLe us x y = true)) (hs : ∀ j, (us' j).St = (us j).St) :
    q.Pairwise (fun x y => waitLe us' x y = true) := by
  rw [waitLe_congr hs]; exact (List.pairwise_cons.mp h).2

/-- **The R9 order in round 1.** -/
theorem orderInv (hR : I.R = 1) {s : State} (h : Reach I α s) : OrderInv I s := by
  induction h with
  | refl =>
    refine ⟨fun _ g hg => ?_, fun _ g hg hq ha => ?_, fun hp => by simp [initState] at hp,
      fun hp => by simp [initState] at hp⟩
    · simp [initState, initUnits_enemy hg]
    · exfalso; apply hq
      exact Prop11.mem_initQueue (by unfold Instance.N; omega) ha
  | @tail s₁ s₂ h₁ hst ih =>
    have hr := (lemmaE1 hR h₁).1
    have hf := Reach.frame h₁
    have hside : ∀ g < I.n, (s₁.units (I.k + g)).side = .enemy := fun g hg => by
      rw [hf.side, initUnits_enemy hg]
    cases hst with
    | @skip i q hq ha =>
      have hno : ∀ g < I.n, I.k + g ∉ q → (s₁.units (I.k + g)).alive → I.k + g ∉ s₁.queue := by
        intro g hg hn hal hm
        rw [hq, List.mem_cons] at hm
        rcases hm with e | hm
        · rw [e] at hal; exact ha hal
        · exact hn hm
      exact ⟨fun hp g hg => ih.n1 hp g hg,
        fun hp g hg hn hal => ih.n2 hp g hg (hno g hg hn hal) hal,
        fun hp => by have := ih.w1 hp; rw [hq] at this; exact (List.pairwise_cons.mp this).2,
        fun hp g hg hn hal => ih.w2 hp g hg (hno g hg hn hal) hal⟩
    | @enemyWait i q hp hq ha hs =>
      refine ⟨fun _ g hg => ?_, fun _ g hg hn hal => ?_, fun hp' => by simp_all,
        fun hp' => by simp_all⟩
      · simp only [update_apply]; split_ifs with he
        · simp [activate]
        · exact ih.n1 hp g hg
      · simp only [List.mem_append, List.mem_singleton]
        by_cases he : I.k + g = i
        · exact Or.inr he
        · left
          simp only [update_apply, he, ↓reduceIte] at hal
          exact ih.n2 hp g hg (by rw [hq, List.mem_cons]; rintro (e | e); exact he e; exact hn e) hal
    | @enemyDefend i q hp hq ha hs =>
      refine ⟨fun hp' => by simp_all, fun hp' => by simp_all, fun _ => ?_,
        fun _ g hg hn hal => ?_⟩
      · refine pairwise_tail_static (by rw [← hq]; exact ih.w1 hp) (fun j => ?_)
        simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
      · simp only [update_apply] at hal ⊢
        split_ifs with he
        · rfl
        · rw [if_neg he] at hal
          exact ih.w2 hp g hg (by rw [hq, List.mem_cons]; rintro (e | e); exact he e; exact hn e) hal
    | @playerWait i q hp hq ha hs =>
      have hne : ∀ g < I.n, I.k + g ≠ i := fun g hg e => by
        have := hside g hg; rw [e, hs] at this; cases this
      refine ⟨fun _ g hg => ?_, fun _ g hg hn hal => ?_, fun hp' => by simp_all,
        fun hp' => by simp_all⟩
      · simp only [update_of_ne (hne g hg)]; exact ih.n1 hp g hg
      · simp only [update_of_ne (hne g hg)] at hal
        exact List.mem_append_left _ (ih.n2 hp g hg
          (by rw [hq, List.mem_cons]; rintro (e | e); exact hne g hg e; exact hn e) hal)
    | @playerDefend i q hq ha hs | @playerMove i q _ hq ha hs _ =>
      have hne : ∀ g < I.n, I.k + g ≠ i := fun g hg e => by
        have := hside g hg; rw [e, hs] at this; cases this
      have hnq : ∀ g < I.n, I.k + g ∉ q → I.k + g ∉ s₁.queue := fun g hg hn => by
        rw [hq, List.mem_cons]; rintro (e | e); exact hne g hg e; exact hn e
      refine ⟨fun hp g hg => ?_, fun hp g hg hn hal => ?_, fun hp => ?_, fun hp g hg hn hal => ?_⟩
      · simp only [update_of_ne (hne g hg)]; exact ih.n1 hp g hg
      · simp only [update_of_ne (hne g hg)] at hal
        exact ih.n2 hp g hg (hnq g hg hn) hal
      · refine pairwise_tail_static (by rw [← hq]; exact ih.w1 hp) (fun j => ?_)
        simp only [update_apply]; split_ifs <;> subst_vars <;> simp [Stack.St, activate]
      · simp only [update_of_ne (hne g hg)] at hal ⊢
        exact ih.w2 hp g hg (hnq g hg hn) hal
    | @playerAttack i q dest t hq ha hs hd ht hta hts hadj =>
      have hne : ∀ g < I.n, I.k + g ≠ i := fun g hg e => by
        have := hside g hg; rw [e, hs] at this; cases this
      have hit : i ≠ t := by rintro rfl; rw [hs] at hts; cases hts
      have hnq : ∀ g < I.n, I.k + g ∉ q → I.k + g ∉ s₁.queue := fun g hg hn => by
        rw [hq, List.mem_cons]; rintro (e | e); exact hne g hg e; exact hn e
      have hdef : ∀ g < I.n, (resolveAttack s₁.units i t dest (I.k + g)).defending =
          (s₁.units (I.k + g)).defending := by
        intro g hg
        by_cases het : I.k + g = t
        · rw [het]; exact resolveAttack_defending_target hit
        · rw [resolveAttack_of_ne (hne g hg) het]
      have hal' : ∀ g, (resolveAttack s₁.units i t dest (I.k + g)).alive →
          (s₁.units (I.k + g)).alive := fun g h =>
        lt_of_lt_of_le h (resolveAttack_pool_le _ _ _ _ _)
      refine ⟨fun hp g hg => ?_, fun hp g hg hn hal => ?_, fun hp => ?_, fun hp g hg hn hal => ?_⟩
      · simp only; rw [hdef g hg]; exact ih.n1 hp g hg
      · exact ih.n2 hp g hg (hnq g hg hn) (hal' g hal)
      · exact pairwise_tail_static (by rw [← hq]; exact ih.w1 hp) (resolveAttack_St' (dest := dest))
      · simp only; rw [hdef g hg]; exact ih.w2 hp g hg (hnq g hg hn) (hal' g hal)
    | toWait hp hq =>
      refine ⟨fun hp' => by simp at hp', fun hp' => by simp at hp', fun _ => ?_,
        fun _ g hg hn hal => ?_⟩
      · exact List.pairwise_mergeSort (waitLe_trans _) (waitLe_total _) _
      · exfalso; apply hn
        rw [(List.mergeSort_perm _ _).mem_iff]
        exact ih.n2 hp g hg (by rw [hq]; exact List.not_mem_nil) hal
    | nextRound _ _ h1 => omega

/-- In the `NORMAL` phase of round 1 no enemy has its `DEFEND` bonus up. -/
theorem normal_undefended (hR : I.R = 1) {s : State} (h : Reach I α s) (hp : s.phase = .normal)
    {g : ℕ} (hg : g < I.n) : (s.units (I.k + g)).defending = false :=
  (orderInv hR h).n1 hp g hg

/-- **A waiting blow meets the postponed `DEFEND`**: if every army type is faster than every
enemy, a player stack striking in the `WAIT` phase finds its (living) target defending. -/
theorem wait_attack_defended (hR : I.R = 1)
    (hspd : ∀ x ∈ I.army, ∀ g < I.n, (I.enemy g).type.spd < x.1.spd) (hα : Feasible I α)
    {s : State} (h : Reach I α s) (hp : s.phase = .wait) {i : ℕ} {q : List ℕ}
    (hq : s.queue = i :: q) (hs : (s.units i).side = .player) {g : ℕ} (hg : g < I.n)
    (hta : (s.units (I.k + g)).alive) : (s.units (I.k + g)).defending = true := by
  have hO := orderInv hR h
  have hf := Reach.frame h
  by_cases hin : I.k + g ∈ s.queue
  · exfalso
    have hne : I.k + g ≠ i := fun e => by
      have := hf.side (I.k + g); rw [initUnits_enemy hg, e, hs] at this; cases this
    have hpw := hO.w1 hp
    rw [hq] at hpw hin
    have hmq : I.k + g ∈ q := (List.mem_cons.mp hin).resolve_left hne
    have hle := (List.pairwise_cons.mp hpw).1 _ hmq
    have hi : i < I.k := initUnits_side_player (by rw [← hf.side]; exact hs)
    have hiQ : i ∈ s.Q := by simp [State.Q, hq]
    obtain ⟨-, hal⟩ := h.mem_Q hR hiQ
    obtain ⟨x, hx, hty⟩ := slotType_mem hα hi hal
    have h1 : (s.units i).type.spd = x.1.spd := by
      rw [hf.type, initUnits_player hi]; simp only; rw [hty]
    have h2 : (s.units (I.k + g)).type.spd = (I.enemy g).type.spd := by
      rw [hf.type, initUnits_enemy hg]
    have h3 := hspd x hx g hg
    simp only [waitLe, decide_eq_true_eq] at hle
    omega
  · exact hO.w2 hp g hg hin hta

/-! ## Player stacks are untouched until they act -/

/-- A player stack that has not taken its terminal action still has its initial pool. -/
theorem fresh_of_Q (hR : I.R = 1) {s : State} (h : Reach I α s) :
    ∀ j < I.k, j ∈ s.Q → (s.units j).pool = (initUnits I α j).pool := by
  induction h with
  | refl => intro j _ _; rfl
  | @tail s₁ s₂ h₁ hst ih =>
    intro j hj hjQ
    obtain ⟨hr, hn, -⟩ := lemmaE1 hR h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have hf := Reach.frame h₁
    rcases hst.pool_cases j with heq | ⟨i, q, dest, t, hq, ha, hs, hd, ht, hta, hts, hadj, hus,
      hq', hb'⟩
    · rw [heq]; exact ih j hj (hsub j hjQ)
    · have hji : j ≠ i := by
        rintro rfl
        have : j ∉ s₂.Q := by simp only [State.Q, hq', hb']; exact head_not_mem_after hq hn
        exact this hjQ
      have hjt : j ≠ t := by
        rintro rfl
        rw [hf.side, initUnits_side_of_lt hj] at hts; cases hts
      rw [hus, resolveAttack_of_ne hji hjt]; exact ih j hj (hsub j hjQ)

/-- Only the stack at the head of the queue can change its hex. -/
theorem Step.hex_cases {s s' : State} (h : Step I s s') (j : ℕ) :
    (s'.units j).hex = (s.units j).hex ∨ ∃ q, s.queue = j :: q := by
  cases h with
  | skip => exact Or.inl rfl
  | enemyWait => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | enemyDefend => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerWait => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerDefend => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | @playerMove i q dest hq =>
    by_cases hji : j = i
    · subst hji; exact Or.inr ⟨q, hq⟩
    · left; simp [update_of_ne hji]
  | @playerAttack i q dest t hq =>
    by_cases hji : j = i
    · subst hji; exact Or.inr ⟨q, hq⟩
    · exact Or.inl (resolveAttack_hex_of_ne hji)
  | toWait => exact Or.inl rfl
  | nextRound => left; simp [newRound]

/-- A hex of the BFS reach is the start hex or a free hex. -/
theorem mem_reach_cases {free : Hex → Prop} [DecidablePred free] {p : Hex} :
    ∀ {s : ℕ} {q : Hex}, q ∈ reach free p s → q = p ∨ free q
  | 0, q, hq => by simp only [reach, Finset.mem_singleton] at hq; exact Or.inl hq
  | s + 1, q, hq => by
    simp only [reach, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      List.mem_filter, decide_eq_true_eq] at hq
    rcases hq with hq | ⟨_, _, _, hf⟩
    · exact mem_reach_cases hq
    · exact Or.inr hf

/-- The attacker's pool after a `WALK_AND_ATTACK`: unchanged, or reduced by the blow of the
retaliating target (same type, pool at most the target's, alive). -/
theorem resolveAttack_attacker_pool {us : ℕ → Stack} {i t : ℕ} {dest : Hex} (hit : i ≠ t) :
    (resolveAttack us i t dest i).pool = (us i).pool ∨
    ∃ tg : Stack, tg.type = (us t).type ∧ tg.pool ≤ (us t).pool ∧ 1 ≤ tg.pool ∧
      (resolveAttack us i t dest i).pool =
        (us i).pool - blow tg { activate (us i) with hex := dest } := by
  unfold resolveAttack
  split_ifs with hret
  · right
    refine ⟨{ (us t).hit (blow { activate (us i) with hex := dest } (us t)) with
      retal := ((us t).hit (blow { activate (us i) with hex := dest } (us t))).retal - 1 },
      rfl, by simp [Stack.hit], hret.1, ?_⟩
    simp only [update_self]; rfl
  · left; simp [hit, activate]

/-! ## Lemma E.2 and Lemma E.20 on the stock-one family -/

namespace Fam

variable {L : Layout} {a : List ℕ} {T : ℕ}

/-- **Lemma E.2 (retaliation is inert)** on every layout of the family: a player stack is
untouched (pool `5`) until its terminal action and afterwards has lost at most one point, so
it keeps its one creature. -/
theorem lemmaE2 (hT : 1 ≤ T) (hα : Feasible (famInst L a T) α) {s : State}
    (h : Reach (famInst L a T) α s) : ∀ j < L.slots.length, 0 < (α j).count →
      ((j ∈ s.Q → (s.units j).pool = 5) ∧ 4 ≤ (s.units j).pool ∧ (s.units j).pool ≤ 5) := by
  have hinit : ∀ j < L.slots.length, 0 < (α j).count →
      (initUnits (famInst L a T) α j).pool = 5 := by
    intro j hj hc
    have ht := hα.1 j (by simpa using hj) hc
    rw [army_len] at ht
    rw [initUnits_player (by simpa using hj), slotType_eq hc ht,
      show (α j).count = 1 by have := count_le_one hα hj; omega]
    rfl
  induction h with
  | refl =>
    intro j hj hc
    have := hinit j hj hc
    exact ⟨fun _ => this, by simp only [initState]; omega, by simp only [initState]; omega⟩
  | @tail s₁ s₂ h₁ hst ih =>
    intro j hj hc
    obtain ⟨hr, hn, -⟩ := lemmaE1 rfl h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have hf := Reach.frame h₁
    have hfr := fresh_of_Q (I := famInst L a T) rfl (h₁.tail hst)
    obtain ⟨ih1, ih2, ih3⟩ := ih j hj hc
    refine ⟨fun hjQ => by rw [hfr j (by simpa using hj) hjQ]; exact hinit j hj hc, ?_⟩
    rcases hst.pool_cases j with heq | ⟨i, q, dest, t, hq, ha, hs, hd, ht, hta, hts, hadj, hus,
      hq', hb'⟩
    · rw [heq]; exact ⟨ih2, ih3⟩
    by_cases hji : j = i
    · subst hji
      have hjt : j ≠ t := by rintro rfl; rw [hs] at hts; cases hts
      have hp5 : (s₁.units j).pool = 5 := ih1 (by simp [State.Q, hq])
      obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
      simp only [n_eq] at hg
      rw [hus]
      -- the retaliation: one creature of flat damage 1 at `Δ ≤ 0` deals at most 1
      rcases resolveAttack_attacker_pool (us := s₁.units) (dest := dest) hjt with he | ⟨tg, hty, hle, h1, he⟩
      · rw [he, hp5]; omega
      · rw [he, hp5]
        have hty' : tg.type = famEnemy T := by
          rw [hty, hf.type, initUnits_enemy (by simpa using hg), enemy_eq hg]
        have hpl : tg.pool ≤ 1 * T := by
          have := hf.pool ((famInst L a T).k + g)
          rw [initUnits_enemy (by simpa using hg), enemy_eq hg] at this
          simp only [famEnemy, one_mul] at this ⊢; omega
        have hb := Prop11.blow_le (C := famEnemy T) (c := 1) (a := tg)
          (tg := { activate (s₁.units j) with hex := dest }) hty' (by simp [famEnemy])
          (by simpa [famEnemy] using hT) h1 (by simpa [famEnemy] using hpl)
          (by
            simp only [activate]; rw [hf.type, initUnits_player (by simpa using hj),
              slotType_eq hc (by have := hα.1 j (by simpa using hj) hc; rwa [army_len] at this)]
            simp [famEnemy, famPlayer])
        have hb' : blow tg { activate (s₁.units j) with hex := dest } ≤ 1 := hb
        omega
    · have hjt : j ≠ t := by
        rintro rfl
        rw [hf.side, initUnits_side_of_lt (by simpa using hj)] at hts; cases hts
      rw [hus, resolveAttack_of_ne hji hjt]; exact ⟨ih2, ih3⟩

end Fam

/-- A step moves at most the head of the queue, and only within its BFS reach. -/
theorem Step.hex_cases' {s s' : State} (h : Step I s s') (j : ℕ) :
    (s'.units j).hex = (s.units j).hex ∨
      ((s'.units j).hex ∈ reachOf I s.units j ∧ ∃ q, s.queue = j :: q) := by
  cases h with
  | skip => exact Or.inl rfl
  | enemyWait => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | enemyDefend => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerWait => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | playerDefend => left; simp only [update_apply]; split_ifs <;> subst_vars <;> simp [activate]
  | @playerMove i q dest hq ha hs hd =>
    by_cases hji : j = i
    · subst hji; right; simp only [update_self]; exact ⟨hd, q, hq⟩
    · left; simp [update_of_ne hji]
  | @playerAttack i q dest t hq ha hs hd ht hta hts hadj =>
    by_cases hji : j = i
    · subst hji
      have hit : j ≠ t := by rintro rfl; rw [hs] at hts; cases hts
      right; simp only; rw [resolveAttack_self_hex hit]; exact ⟨hd, q, hq⟩
    · exact Or.inl (resolveAttack_hex_of_ne hji)
  | toWait => exact Or.inl rfl
  | nextRound => left; simp [newRound]

namespace Fam

variable {L : Layout} {a : List ℕ} {T : ℕ}

/-- The phase-aware ledger of Lemma E.20: a strike record `τ`, blow record `β`, and `ω j` =
"slot `j` struck in the `WAIT` phase", i.e. after waiting. -/
structure LedgerW (L : Layout) (a : List ℕ) (T : ℕ) (α : ℕ → SlotAlloc) (s : State)
    (τ : ℕ → Option ℕ) (β : ℕ → ℕ) (ω : ℕ → Bool) : Prop where
  base : Ledger (famInst L a T) α (fun _ _ => True) s τ β
  occupied : ∀ j g, τ j = some g → 0 < (α j).count
  normal : ∀ j g, τ j = some g → ω j = false → β j = a.getD (α j).type 0
  wait : ∀ j g, τ j = some g → ω j = true → β j = damage 1 (a.getD (α j).type 0) (-1)
  hex : ∀ j g, τ j = some g → Hex.Adj (s.units j).hex (L.ehex.getD g ⟨0, 0⟩)

/-- **The phase-aware ledger exists along every play** (players faster than the enemies). -/
theorem ledgerW (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x) (hspd : 1 < L.spd)
    (hα : Feasible (famInst L a T) α) {s : State} (h : Reach (famInst L a T) α s) :
    ∃ τ β ω, LedgerW L a T α s τ β ω := by
  have H := acctHyp (L := L) hT ha
  induction h with
  | refl =>
    refine ⟨fun _ => none, fun _ => 0, fun _ => false,
      ⟨⟨fun j g h => (by simp at h), fun _ => Nat.zero_le _, ?_⟩, fun j g h => (by simp at h),
        fun j g h => (by simp at h), fun j g h => (by simp at h), fun j g h => (by simp at h)⟩⟩
    intro g hg
    simp only [initState, initUnits_enemy hg, H.one g hg, one_mul, Finset.sum_const_zero,
      Nat.sub_zero]
  | @tail s₁ s₂ h₁ hst ih =>
    obtain ⟨τ, β, ω, hL⟩ := ih
    obtain ⟨hr, hn, -⟩ := lemmaE1 H.R1 h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have hf := Reach.frame h₁
    rcases hst.attack_or with hall | ⟨i, q, dest, t, hq, hal, hs, hd, ht, hta, hts, hadj, hus,
      hq', hb'⟩
    · refine ⟨τ, β, ω, ⟨⟨fun j g hj => ?_, hL.base.blow, fun g hg => by
        rw [hall]; exact hL.base.pool g hg⟩, hL.occupied, hL.normal, hL.wait, fun j g hj => ?_⟩⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hL.base.acted j g hj
        exact ⟨a1, fun hm => a2 (hsub j hm), a3, a4⟩
      · rcases hst.hex_cases j with he | ⟨q0, hq0⟩
        · rw [he]; exact hL.hex j g hj
        · exact absurd (by simp [State.Q, hq0]) (hL.base.acted j g hj).2.1
    · have hiQ : i ∈ s₁.Q := by simp [State.Q, hq]
      have hi : i < (famInst L a T).k := initUnits_side_player (by rw [← hf.side]; exact hs)
      obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
      have hg' : g < L.ehex.length := by simpa using hg
      have hτi : τ i = none := by
        rcases e : τ i with _ | g0
        · rfl
        · exact absurd hiQ (hL.base.acted i g0 e).2.1
      have hiQ' : i ∉ s₂.Q := by
        simp only [State.Q, hq', hb']; exact head_not_mem_after hq hn
      have hit : i ≠ (famInst L a T).k + g := by omega
      obtain ⟨-, halI⟩ := Reach.mem_Q H.R1 h₁ hiQ
      have hc : 0 < (α i).count := by
        rw [initUnits_player hi] at halI; unfold Stack.alive at halI
        by_contra h0; simp only [not_lt, nonpos_iff_eq_zero] at h0; rw [h0] at halI; simp at halI
      have htyi : (α i).type < a.length := by
        have := hα.1 i hi hc; rwa [army_len] at this
      set ai := a.getD (α i).type 0 with hai
      have hai1 : 1 ≤ ai := ha _ (ThreeP.getD_mem htyi)
      -- the attacker is fresh: one creature of type `C_{type i}`
      have hpool : (s₁.units i).pool = 5 := by
        rw [fresh_of_Q H.R1 h₁ i hi hiQ, initUnits_player hi, slotType_eq hc htyi,
          show (α i).count = 1 by have := count_le_one hα (by simpa using hi); omega]
        rfl
      have htyA : (s₁.units i).type = famPlayer L.spd ai := by
        rw [hf.type, initUnits_player hi, slotType_eq hc htyi]
      have htyT : (s₁.units ((famInst L a T).k + g)).type = famEnemy T := by
        rw [hf.type, initUnits_enemy hg, enemy_eq hg']
      set A : Stack := { activate (s₁.units i) with hex := dest } with hA
      have hcntA : A.count = 1 :=
        Prop11.count_eq (c := 1) (by simp only [hA, activate]; rw [htyA]; simp [famPlayer])
          (by simp only [hA, activate]; rw [hpool, htyA]; rfl)
      have hblow : blow A (s₁.units ((famInst L a T).k + g)) =
          damage 1 ai (1 - (s₁.units ((famInst L a T).k + g)).defEff) := by
        unfold blow; rw [hcntA]; simp only [hA, activate]; rw [htyA]; rfl
      set b := blow A (s₁.units ((famInst L a T).k + g)) with hbdef
      set ph : Bool := decide (s₁.phase = .wait) with hph
      have hbN : ph = false → b = ai := by
        intro h0
        have hpn : s₁.phase = .normal := by
          cases hp : s₁.phase
          · rfl
          · rw [hph, hp] at h0; simp at h0
        have hdef := normal_undefended H.R1 h₁ hpn hg
        rw [hblow]
        unfold Stack.defEff; rw [hdef, htyT]
        simp only [famEnemy, Bool.false_eq_true, ↓reduceIte, add_zero, Nat.cast_one, sub_self]
        rw [damage_zero (by rw [one_mul]; exact hai1), one_mul]
      have hbW : ph = true → b = damage 1 ai (-1) := by
        intro h1
        have hpw : s₁.phase = .wait := by simpa [hph] using h1
        have hdef := wait_attack_defended H.R1 (fun x hx g' hg'' => by
            simp only [famInst, List.mem_map] at hx
            obtain ⟨ai', -, rfl⟩ := hx
            rw [enemy_eq (by simpa using hg'')]; simpa [famEnemy, famPlayer] using hspd)
          hα h₁ hpw hq hs hg hta
        rw [hblow]
        unfold Stack.defEff; rw [hdef, htyT]
        simp [famEnemy, defendBonus]
      refine ⟨update τ i (some g), update β i b, update ω i ph, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
      · intro j g' hj
        by_cases hji : j = i
        · subst hji; rw [update_self] at hj; cases hj; exact ⟨hi, hiQ', hg, trivial⟩
        · rw [update_of_ne hji] at hj
          obtain ⟨a1, a2, a3, a4⟩ := hL.base.acted j g' hj
          exact ⟨a1, fun hm => a2 (hsub j hm), a3, a4⟩
      · intro j
        by_cases hji : j = i
        · subst hji
          rw [update_self, nominal_eq hα (by simpa using hi), if_pos hc]
          by_cases hp0 : ph = true
          · rw [hbW hp0]
            have := damage_neg_one_le (c := 1) (d := ai) (by rw [one_mul]; exact hai1)
            rwa [one_mul] at this
          · rw [hbN (by simpa using hp0)]
        · rw [update_of_ne hji]; exact hL.base.blow j
      · intro g' hg''
        rw [hus]
        by_cases hgg : g' = g
        · subst hgg
          rw [resolveAttack_pool_target hit, hL.base.pool g' hg'',
            strikers_update_self hi hτi, Finset.sum_insert (by simp [strikers, hτi]), update_self,
            Nat.sub_sub]
          have : ∑ j ∈ strikers (famInst L a T) τ g', update β i b j =
              ∑ j ∈ strikers (famInst L a T) τ g', β j := by
            apply Finset.sum_congr rfl
            intro j hj
            have : j ≠ i := by rintro rfl; simp [strikers, hτi] at hj
            rw [update_of_ne this]
          rw [this, add_comm]
        · rw [resolveAttack_of_ne (by omega) (by omega), hL.base.pool g' hg'',
            strikers_update_ne hτi hgg]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have : j ≠ i := by rintro rfl; simp [strikers, hτi] at hj
          rw [update_of_ne this]
      · intro j g' hj
        by_cases hji : j = i
        · subst hji; exact hc
        · rw [update_of_ne hji] at hj; exact hL.occupied j g' hj
      · intro j g' hj hω
        by_cases hji : j = i
        · subst hji; rw [update_self] at hω ⊢; exact hbN hω
        · rw [update_of_ne hji] at hj hω ⊢; exact hL.normal j g' hj hω
      · intro j g' hj hω
        by_cases hji : j = i
        · subst hji; rw [update_self] at hω ⊢; exact hbW hω
        · rw [update_of_ne hji] at hj hω ⊢; exact hL.wait j g' hj hω
      · intro j g' hj
        by_cases hji : j = i
        · subst hji
          rw [update_self] at hj; cases hj
          rw [hus, resolveAttack_self_hex hit]
          have := hadj
          rwa [hf.ehex _ (by rw [initUnits_enemy hg]), initUnits_enemy hg, enemy_eq hg'] at this
        · rw [update_of_ne hji] at hj
          rw [hus, resolveAttack_hex_of_ne hji]; exact hL.hex j g' hj

end Fam

namespace ThmF

variable {a : List ℕ} {T : ℕ} {α : ℕ → SlotAlloc}

/-- **Lemma E.20 (damage accounting on `G_F`)**, for every allocation and every play of round 1,
not necessarily attack-only: striker sets pairwise disjoint (`Ledger.disjoint`); every blow at
most nominal; a blow issued without waiting exactly nominal `a_i`; a waiting blow meets the
postponed `DEFEND` and is at most nominal, **with equality exactly when `a_i = 1`**; absorbed
`= min(T, delivered)`; `E_g` dead only if `Σ_{i∈S_g} a_i ≥ T`; and if no striker of `E_g` waited
and `Σ_{i∈S_g} a_i ≥ T`, then `E_g` is dead. -/
theorem lemmaE20 (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x) (hα : Feasible (GF a T) α) {s : State}
    (h : Reach (GF a T) α s) :
    ∃ τ β ω, Fam.LedgerW (layout (a.length / 3)) a T α s τ β ω ∧
      (∀ j g, τ j = some g → ω j = true →
        β j ≤ a.getD (α j).type 0 ∧ (β j = a.getD (α j).type 0 ↔ a.getD (α j).type 0 = 1)) ∧
      (∀ g < a.length / 3, T - (s.units ((GF a T).k + g)).pool =
        min T (∑ j ∈ strikers (GF a T) τ g, β j)) ∧
      (∀ g < a.length / 3, (s.units ((GF a T).k + g)).pool = 0 →
        T ≤ ∑ i ∈ Fam.typesOf α (strikers (GF a T) τ g), a.getD i 0) ∧
      (∀ g < a.length / 3, (∀ j ∈ strikers (GF a T) τ g, ω j = false) →
        T ≤ ∑ i ∈ Fam.typesOf α (strikers (GF a T) τ g), a.getD i 0 →
        (s.units ((GF a T).k + g)).pool = 0) := by
  obtain ⟨τ, β, ω, hL⟩ := Fam.ledgerW (L := layout (a.length / 3)) hT ha
    (by simp [layout]) hα h
  have hsubF : ∀ g, strikers (GF a T) τ g ⊆ Finset.range (layout (a.length / 3)).slots.length :=
    fun g j hj => by simp only [strikers, Finset.mem_filter] at hj; simpa [GF] using hj.1
  have henemy : ∀ g < a.length / 3, ((GF a T).enemy g).type.hp = T := fun g hg => by
    rw [enemy_eq' hg]; rfl
  refine ⟨τ, β, ω, hL, fun j g hj hω => ?_, fun g hg => ?_, fun g hg h0 => ?_,
    fun g hg hnw hge => ?_⟩
  · rw [hL.wait j g hj hω]
    have h1 : 1 ≤ a.getD (α j).type 0 := by
      have hc := hL.occupied j g hj
      have hj' := (hL.base.acted j g hj).1
      have := hα.1 j hj' hc
      rw [show (GF a T).army.length = a.length from Fam.army_len] at this
      exact ha _ (ThreeP.getD_mem this)
    have h1' : 1 ≤ 1 * a.getD (α j).type 0 := by rw [one_mul]; exact h1
    have he := damage_neg_one_eq_iff (c := 1) (d := a.getD (α j).type 0) h1'
    rw [one_mul] at he
    have hl := damage_neg_one_le (c := 1) (d := a.getD (α j).type 0) h1'
    rw [one_mul] at hl
    exact ⟨hl, he⟩
  · have := hL.base.absorbed (g := g) (by simpa using hg)
    have he : ((famInst (layout (a.length / 3)) a T).enemy g).type.hp = T := henemy g hg
    rw [he] at this
    exact this
  · have := hL.base.dead (g := g) (by simpa using hg) h0
    have he : ((famInst (layout (a.length / 3)) a T).enemy g).type.hp = T := henemy g hg
    rw [he] at this
    have hs := Fam.sum_typesOf (L := layout (a.length / 3)) (a := a) (T := T) hα
      (F := strikers (famInst (layout (a.length / 3)) a T) τ g) (hsubF g)
    show T ≤ ∑ i ∈ Fam.typesOf α (strikers (famInst (layout (a.length / 3)) a T) τ g), a.getD i 0
    rw [hs]; exact this
  · have hsum : ∑ j ∈ strikers (famInst (layout (a.length / 3)) a T) τ g, β j =
        ∑ i ∈ Fam.typesOf α (strikers (famInst (layout (a.length / 3)) a T) τ g), a.getD i 0 := by
      rw [Fam.sum_typesOf (L := layout (a.length / 3)) (a := a) (T := T) hα
        (F := strikers (famInst (layout (a.length / 3)) a T) τ g) (hsubF g)]
      apply Finset.sum_congr rfl
      intro j hj
      have hjg : τ j = some g := (Finset.mem_filter.mp hj).2
      rw [hL.normal j g hjg (hnw j hj), Fam.nominal_eq hα (Finset.mem_range.mp (hsubF g hj)),
        if_pos (hL.occupied j g hjg)]
    have := hL.base.pool g (by simpa using hg)
    have he : ((famInst (layout (a.length / 3)) a T).enemy g).type.hp = T := henemy g hg
    rw [he] at this
    have hge' : T ≤ ∑ i ∈ Fam.typesOf α (strikers (famInst (layout (a.length / 3)) a T) τ g),
        a.getD i 0 := hge
    rw [hsum] at this
    show (s.units ((famInst (layout (a.length / 3)) a T).k + g)).pool = 0
    omega

/-! ## Local seat capacity -/

/-- Living stacks stand on pairwise distinct hexes throughout round 1. -/
theorem distinct_hexes {s : State} (h : Reach (GF a T) α s) :
    ∀ i < (GF a T).N, ∀ i' < (GF a T).N, i ≠ i' → (s.units i).alive → (s.units i').alive →
      (s.units i).hex ≠ (s.units i').hex := by
  have hstart : ∀ i < (GF a T).N, (initUnits (GF a T) α i).hex =
      if i < (GF a T).k then phex i else ehex (i - (GF a T).k) := by
    intro i hi
    split_ifs with hik
    · rw [initUnits_player hik, slotHex_eq (by have := k_eq (a := a) (T := T); omega)]
    · have hg : i - (GF a T).k < a.length / 3 := by
        have := k_eq (a := a) (T := T); have := N_eq (a := a) (T := T); omega
      have := initUnits_enemy (I := GF a T) (α := α) (j := i - (GF a T).k) (by rw [n_eq]; exact hg)
      rw [show (GF a T).k + (i - (GF a T).k) = i by omega] at this
      rw [this, enemy_eq' hg]
  induction h with
  | refl =>
    intro i hi i' hi' hne _ _
    simp only [initState]
    rw [hstart i hi, hstart i' hi']
    split_ifs with h1 h2 h2
    · simp [phex]; omega
    · simp [phex, ehex]
    · simp [phex, ehex]
    · intro e; exact hne (by have := ehex_inj e; omega)
  | @tail s₁ s₂ h₁ hst ih =>
    intro i hi i' hi' hne ha ha'
    have ha1 : (s₁.units i).alive := lt_of_lt_of_le ha (hst.pool_le i)
    have ha1' : (s₁.units i').alive := lt_of_lt_of_le ha' (hst.pool_le i')
    rcases hst.hex_cases' i with hi_eq | ⟨hmem, q, hq⟩ <;>
      rcases hst.hex_cases' i' with hi'_eq | ⟨hmem', q', hq'⟩
    · rw [hi_eq, hi'_eq]; exact ih i hi i' hi' hne ha1 ha1'
    · rw [hi_eq]
      rcases mem_reach_cases hmem' with e | hfr
      · rw [e]; exact ih i hi i' hi' hne ha1 ha1'
      · exact fun e => hfr.2.2 i hi (fun e' => hne e') ha1 e
    · rw [hi'_eq]
      rcases mem_reach_cases hmem with e | hfr
      · rw [e]; exact ih i hi i' hi' hne ha1 ha1'
      · exact fun e => hfr.2.2 i' hi' (fun e' => hne e'.symm) ha1' e.symm
    · exfalso; rw [hq] at hq'; exact hne (List.cons.inj hq').1

/-- **Seat capacity** (the Remark after Corollary 4.2): along every play of round 1, at most six
stacks strike any one enemy — every striker survives (Lemma E.2) on a neighbour of its target,
living stacks occupy distinct hexes, and an enemy has six neighbours. -/
theorem seat_capacity (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x) (hα : Feasible (GF a T) α) {s : State}
    (h : Reach (GF a T) α s) :
    ∃ τ β ω, Fam.LedgerW (layout (a.length / 3)) a T α s τ β ω ∧
      ∀ g < a.length / 3, (strikers (GF a T) τ g).card ≤ 6 := by
  obtain ⟨τ, β, ω, hL⟩ := Fam.ledgerW (L := layout (a.length / 3)) hT ha
    (by simp [layout]) hα h
  refine ⟨τ, β, ω, hL, fun g hg => ?_⟩
  have hE2 := Fam.lemmaE2 (L := layout (a.length / 3)) hT hα h
  have hjk : ∀ j ∈ strikers (GF a T) τ g, j < (GF a T).k ∧ τ j = some g := fun j hj => by
    simp only [strikers, Finset.mem_filter, Finset.mem_range] at hj; exact hj
  have hmaps : ∀ j ∈ strikers (GF a T) τ g, (s.units j).hex ∈ (ehex g).nbrs.toFinset := by
    intro j hj
    obtain ⟨-, hjg⟩ := hjk j hj
    have := hL.hex j g hjg
    simp only [layout, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg,
      Option.map_some, Option.getD_some] at this
    exact List.mem_toFinset.mpr (Hex.adj_symm this)
  have hinj : Set.InjOn (fun j => (s.units j).hex) (strikers (GF a T) τ g) := by
    intro j hj j' hj' he
    by_contra hne
    obtain ⟨hjK, hjg⟩ := hjk j hj
    obtain ⟨hjK', hjg'⟩ := hjk j' hj'
    have hal : ∀ x, x < (GF a T).k → τ x = some g → (s.units x).alive := fun x hx hxg => by
      have := (hE2 x (by simpa [GF] using hx) (hL.occupied x g hxg)).2.1
      unfold Stack.alive; omega
    have hk := k_eq (a := a) (T := T); have hN := N_eq (a := a) (T := T)
    exact distinct_hexes h j (by omega) j' (by omega) hne
      (hal j hjK hjg) (hal j' hjK' hjg') he
  calc (strikers (GF a T) τ g).card
      ≤ ((ehex g).nbrs.toFinset).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (ehex g).nbrs.length := List.toFinset_card_le _
    _ = 6 := by rw [nbrs_ehex]; rfl

end ThmF

end Homm3
