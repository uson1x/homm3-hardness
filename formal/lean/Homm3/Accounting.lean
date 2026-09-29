import Homm3.Prop11General
import Homm3.Exec
import Homm3.ThreePartition

/-!
# Session 3. Damage accounting for any instance (Lemmas E.12 and E.20), and the stock-one family

Paper: Appendix E, Lemma E.12 (Theorem 2) and Lemma E.20 (Theorem 4), proofs.

* `exists_done` — every position can be completed to a finished battle (`Done`): the
  successor function is never empty before the end and the measure `μ` drops at every step.
  The witnesses below reach a position where every enemy is dead and then finish the play
  with *any* legal steps; pools never grow (`pool_le_of_rtg`), so the dead stay dead.
* `destroyed_single` — with one-creature enemies, value destroyed = values of the enemies
  whose pool is empty.
* **The ledger** (`Ledger`, `ledger`): in every position reachable in round 1 under any
  feasible allocation there is a *strike record* `τ` (slot `j` struck enemy `g` iff
  `τ j = some g`) and a *blow record* `β` such that each recorded slot has taken its terminal
  action, `β j ≤ nominal(j) = c_j · d(type_j)`, and every enemy's pool is
  `hp − Σ_{j struck it} β j` (truncated: overkill discarded, R8).  The striker sets
  `{j | τ j = some g}` are pairwise disjoint because `τ` is a function: one terminal action
  per stack (Lemma E.1) and no retaliation blows by the player (`(‡)`).  This is the
  geometry-free core of Lemmas E.12 and E.20; a hypothesis `P` lets an instance add what its
  geometry says about the target (Theorem 2: only the slot's own enemy).
* The **stock-one family** `famInst L a T` (both `G_{3P}(a, T)` and `G_F(a, T)` are instances
  with different layouts `L`): player types `C_i = (att 1, def 1, dmg a_i, hp 5, spd, value 0)`
  of stock one, enemies one creature `(att 1, def 1, dmg 1, hp T, spd 1, value 1)`, `R = 1`,
  `W = m`.  **`fam_no`**: on *every* layout with `m` enemies, a play destroying `m` yields a
  3-partition — the no-directions of Theorems 2 and 4 (Lemmas E.14, E.22) use no geometry.
-/

namespace Homm3

open Function

variable {I : Instance} {α : ℕ → SlotAlloc}

/-! ## Completing a play -/

/-- Every position can be completed to a finished battle. -/
theorem exists_done (I : Instance) (s : State) :
    ∃ s', Relation.ReflTransGen (Step I) s s' ∧ Done s' := by
  induction hμ : μ I s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hd : Done s
    · exact ⟨s, .refl, hd⟩
    · obtain ⟨s1, hs1⟩ := List.exists_mem_of_ne_nil _ (succs_ne_nil (I := I) hd)
      have hst : Step I s s1 := step_iff_mem_succs.mpr hs1
      obtain ⟨s2, h2, hd2⟩ := ih _ (hμ ▸ hst.μ_lt) s1 rfl
      exact ⟨s2, .head hst h2, hd2⟩

/-- Pools never grow along a play. -/
theorem pool_le_of_rtg {s s' : State} (h : Relation.ReflTransGen (Step I) s s') (j : ℕ) :
    (s'.units j).pool ≤ (s.units j).pool := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih => exact (hst.pool_le j).trans ih

/-! ## Value destroyed with one-creature enemies -/

theorem destroyed_single (hone : ∀ g < I.n, (I.enemy g).count = 1)
    (hehp : ∀ g < I.n, 1 ≤ (I.enemy g).type.hp) {s : State} (hf : RFrame I α s) :
    destroyed I s =
      ∑ g ∈ Finset.range I.n, if (s.units (I.k + g)).pool = 0 then (I.enemy g).type.value else 0 := by
  unfold destroyed Instance.N
  rw [Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range I.k, (if (s.units x).side = .enemy then
      ((s.units x).init - (s.units x).count) * (s.units x).type.value else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hf.side, initUnits_side_of_lt (Finset.mem_range.mp hj)]
    simp
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro g hg
  have hg := Finset.mem_range.mp hg
  have hty := hf.type (I.k + g)
  have hin := hf.initc (I.k + g)
  have hpl := hf.pool (I.k + g)
  rw [initUnits_enemy hg] at hty hin hpl
  simp only at hty hin hpl
  rw [hone g hg, one_mul] at hpl
  rw [hone g hg] at hin
  rw [hf.side, initUnits_enemy hg, hin, hty,
    Corridor.count_single (hehp g hg) (by rw [hty]) hpl]
  simp only [↓reduceIte]
  split_ifs <;> simp

/-! ## The ledger -/

/-- Hypotheses of the accounting: `R = 1`; one-creature enemies of `hp ≥ 1`; army types of
`dmg ≥ 1`, `hp ≥ 1`; every enemy's defence at least every army type's attack (so every blow
is at most nominal, §2.4). -/
structure AcctHyp (I : Instance) : Prop where
  R1 : I.R = 1
  one : ∀ g < I.n, (I.enemy g).count = 1
  ehp : ∀ g < I.n, 1 ≤ (I.enemy g).type.hp
  dmg : ∀ x ∈ I.army, 1 ≤ x.1.dmg
  hp : ∀ x ∈ I.army, 1 ≤ x.1.hp
  dfn : ∀ x ∈ I.army, ∀ g < I.n, x.1.att ≤ (I.enemy g).type.dfn

/-- Nominal damage of slot `j`: `c_j · d(type_j)` (`(★)`). -/
def nominal (I : Instance) (α : ℕ → SlotAlloc) (j : ℕ) : ℕ := (α j).count * (I.slotType α j).dmg

/-- The slots recorded as strikers of enemy `g`. -/
def strikers (I : Instance) (τ : ℕ → Option ℕ) (g : ℕ) : Finset ℕ :=
  (Finset.range I.k).filter (fun j => τ j = some g)

/-- **The ledger of a position** (Lemmas E.12, E.20). -/
structure Ledger (I : Instance) (α : ℕ → SlotAlloc) (P : ℕ → ℕ → Prop) (s : State)
    (τ : ℕ → Option ℕ) (β : ℕ → ℕ) : Prop where
  acted : ∀ j g, τ j = some g → j < I.k ∧ j ∉ s.Q ∧ g < I.n ∧ P j g
  blow : ∀ j, β j ≤ nominal I α j
  pool : ∀ g < I.n, (s.units (I.k + g)).pool = (I.enemy g).type.hp - ∑ j ∈ strikers I τ g, β j

/-- A step either changes no pool or is a `WALK_AND_ATTACK`. -/
theorem Step.attack_or {s s' : State} (h : Step I s s') :
    (∀ j, (s'.units j).pool = (s.units j).pool) ∨
    ∃ i q dest t, s.queue = i :: q ∧ (s.units i).alive ∧ (s.units i).side = .player ∧
      dest ∈ reachOf I s.units i ∧ t < I.N ∧ (s.units t).alive ∧
      (s.units t).side = .enemy ∧ Hex.Adj dest (s.units t).hex ∧
      s'.units = resolveAttack s.units i t dest ∧ s'.queue = q ∧ s'.bucket = s.bucket := by
  by_cases hall : ∀ j, (s'.units j).pool = (s.units j).pool
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    exact Or.inr ((h.pool_cases j).resolve_left hj)

theorem strikers_update_self {τ : ℕ → Option ℕ} {i g : ℕ} (hi : i < I.k) (hτ : τ i = none) :
    strikers I (update τ i (some g)) g = insert i (strikers I τ g) := by
  ext j
  simp only [strikers, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, update_apply]
  by_cases hji : j = i
  · subst hji; simp [hi]
  · simp [hji]

theorem strikers_update_ne {τ : ℕ → Option ℕ} {i g g' : ℕ} (hτ : τ i = none) (hg : g' ≠ g) :
    strikers I (update τ i (some g)) g' = strikers I τ g' := by
  ext j
  simp only [strikers, Finset.mem_filter, Finset.mem_range, update_apply]
  by_cases hji : j = i
  · subst hji; simp [hτ, Ne.symm hg]
  · simp [hji]

/-- **The ledger exists in every position of round 1** (Lemmas E.12 / E.20, geometry-free
core).  `hP`: whatever the instance's geometry says about a strike by a not-yet-terminal
slot is recorded as `P`. -/
theorem ledger (H : AcctHyp I) (hα : Feasible I α) {P : ℕ → ℕ → Prop}
    (hP : ∀ s, Reach I α s → ∀ i < I.k, i ∈ s.Q → ∀ g < I.n,
      CanStrike I s.units i (I.k + g) → P i g) {s : State} (h : Reach I α s) :
    ∃ τ β, Ledger I α P s τ β := by
  induction h with
  | refl =>
    refine ⟨fun _ => none, fun _ => 0, ⟨fun j g h => (by simp at h), fun _ => Nat.zero_le _, ?_⟩⟩
    intro g hg
    simp only [initState, initUnits_enemy hg, H.one g hg, one_mul, Finset.sum_const_zero,
      Nat.sub_zero]
  | @tail s₁ s₂ h₁ hst ih =>
    obtain ⟨τ, β, hL⟩ := ih
    obtain ⟨hr, hn, -⟩ := lemmaE1 H.R1 h₁
    obtain ⟨-, hsub, -⟩ := hst.Q_sub (by rw [hr])
    have hf := Reach.frame h₁
    rcases hst.attack_or with hall | ⟨i, q, dest, t, hq, ha, hs, hd, ht, hta, hts, hadj, hus,
      hq', hb'⟩
    · refine ⟨τ, β, ⟨fun j g hj => ?_, hL.blow, fun g hg => by rw [hall]; exact hL.pool g hg⟩⟩
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
      refine ⟨update τ i (some g), update β i b, ⟨?_, ?_, ?_⟩⟩
      · intro j g' hj
        by_cases hji : j = i
        · subst hji
          rw [update_self] at hj; cases hj
          exact ⟨hi, hiQ', hg, hP s₁ h₁ j hi hiQ g hg (canStrike_of_attack hd ht hta hts hadj)⟩
        · rw [update_of_ne hji] at hj
          obtain ⟨a1, a2, a3, a4⟩ := hL.acted j g' hj
          exact ⟨a1, fun hm => a2 (hsub j hm), a3, a4⟩
      · intro j
        by_cases hji : j = i
        · subst hji
          rw [update_self]
          obtain ⟨-, hal⟩ := Reach.mem_Q H.R1 h₁ hiQ
          obtain ⟨x, hx, hty⟩ := slotType_mem hα hi hal
          have hty' : (s₁.units j).type = I.slotType α j := by
            rw [hf.type, initUnits_player hi]
          have hpool := hf.pool j
          rw [initUnits_player hi] at hpool
          simp only at hpool
          unfold nominal
          exact Prop11.blow_le (C := I.slotType α j) (c := (α j).count)
            (by simp only [ha_def, activate]; exact hty')
            (hty ▸ H.dmg x hx) (hty ▸ H.hp x hx)
            (by simp only [ha_def, activate]; exact Nat.succ_le_of_lt ha)
            (by simp only [ha_def, activate]; exact hpool)
            (by
              rw [hf.type, initUnits_enemy hg, hty]
              exact H.dfn x hx g hg)
        · rw [update_of_ne hji]; exact hL.blow j
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

namespace Ledger

variable {P : ℕ → ℕ → Prop} {s : State} {τ : ℕ → Option ℕ} {β : ℕ → ℕ}

/-- Striker sets are pairwise disjoint (one terminal action per stack). -/
theorem disjoint (g g' : ℕ) (hne : g ≠ g') : Disjoint (strikers I τ g) (strikers I τ g') := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  simp only [strikers, Finset.mem_filter] at h1 h2
  rw [h1.2] at h2
  exact hne (Option.some_injective _ h2.2)

/-- Absorbed damage: `hp − pool = min(hp, delivered)`. -/
theorem absorbed (hL : Ledger I α P s τ β) {g : ℕ} (hg : g < I.n) :
    (I.enemy g).type.hp - (s.units (I.k + g)).pool =
      min (I.enemy g).type.hp (∑ j ∈ strikers I τ g, β j) := by
  rw [hL.pool g hg]; omega

/-- **An enemy is dead only if its strikers' nominal damage reaches its hit points.** -/
theorem dead (hL : Ledger I α P s τ β) {g : ℕ} (hg : g < I.n)
    (h0 : (s.units (I.k + g)).pool = 0) :
    (I.enemy g).type.hp ≤ ∑ j ∈ strikers I τ g, nominal I α j := by
  have := hL.pool g hg
  rw [h0] at this
  exact (by omega : (I.enemy g).type.hp ≤ ∑ j ∈ strikers I τ g, β j).trans
    (Finset.sum_le_sum (fun j _ => hL.blow j))

end Ledger

/-! ## The stock-one family -/

/-- A layout: board, deployment hexes, enemy hexes, player speed. -/
structure Layout where
  width : ℕ
  height : ℕ
  slots : List Hex
  ehex : List Hex
  spd : ℕ

/-- Player type `C_i`: `(★)` `att = def = 1`, flat damage `a_i`, `hp 5`, value `0`. -/
def famPlayer (spd ai : ℕ) : CType := ⟨1, 1, ai, 5, spd, 0⟩
/-- Enemy type: `(★)` `att = def = 1`, flat damage `1`, `hp T`, speed `1`, value `1`. -/
def famEnemy (T : ℕ) : CType := ⟨1, 1, 1, T, 1, 1⟩

/-- The stock-one family of Theorems 2 and 4. -/
def famInst (L : Layout) (a : List ℕ) (T : ℕ) : Instance where
  width := L.width
  height := L.height
  obstacles := ∅
  slots := L.slots
  army := a.map (fun ai => (famPlayer L.spd ai, 1))
  enemies := L.ehex.map (fun h => ⟨famEnemy T, 1, h⟩)
  R := 1
  W := L.ehex.length

namespace Fam

variable {L : Layout} {a : List ℕ} {T : ℕ}

@[simp] theorem k_eq : (famInst L a T).k = L.slots.length := by simp [famInst, Instance.k]
@[simp] theorem n_eq : (famInst L a T).n = L.ehex.length := by simp [famInst, Instance.n]
@[simp] theorem R_eq : (famInst L a T).R = 1 := rfl
@[simp] theorem W_eq : (famInst L a T).W = L.ehex.length := rfl

theorem enemy_eq {g : ℕ} (hg : g < L.ehex.length) :
    (famInst L a T).enemy g = ⟨famEnemy T, 1, L.ehex.getD g ⟨0, 0⟩⟩ := by
  simp [Instance.enemy, famInst, hg]

theorem army_getD {t : ℕ} (ht : t < a.length) :
    (famInst L a T).army.getD t default = (famPlayer L.spd (a.getD t 0), 1) := by
  simp [famInst, ht]

theorem army_len : (famInst L a T).army.length = a.length := by simp [famInst]

theorem slotType_eq {α : ℕ → SlotAlloc} {j : ℕ} (hc : 0 < (α j).count)
    (ht : (α j).type < a.length) :
    (famInst L a T).slotType α j = famPlayer L.spd (a.getD (α j).type 0) := by
  unfold Instance.slotType; rw [if_pos hc, army_getD ht]

theorem slotHex_eq {j : ℕ} : (famInst L a T).slotHex j = L.slots.getD j ⟨0, 0⟩ := rfl

/-- The accounting hypotheses hold for every layout, given `T ≥ 1` and `a_i ≥ 1`. -/
theorem acctHyp (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x) : AcctHyp (famInst L a T) where
  R1 := rfl
  one g hg := by simp only [n_eq] at hg; rw [enemy_eq hg]
  ehp g hg := by simp only [n_eq] at hg; rw [enemy_eq hg]; exact hT
  dmg x hx := by
    simp only [famInst, List.mem_map] at hx
    obtain ⟨ai, hai, rfl⟩ := hx; exact ha ai hai
  hp x hx := by
    simp only [famInst, List.mem_map] at hx
    obtain ⟨ai, hai, rfl⟩ := hx; simp [famPlayer]
  dfn x hx g hg := by
    simp only [n_eq] at hg
    simp only [famInst, List.mem_map] at hx
    obtain ⟨ai, hai, rfl⟩ := hx
    rw [enemy_eq hg]; simp [famPlayer, famEnemy]

/-! ### Stock one -/

theorem stock (hα : Feasible (famInst L a T) α) {t : ℕ} (ht : t < a.length) :
    ∑ j ∈ (Finset.range L.slots.length).filter (fun j => (α j).type = t), (α j).count ≤ 1 := by
  have := hα.2 t (by rw [army_len]; exact ht)
  rw [army_getD ht] at this
  simpa using this

/-- A slot holds at most one creature. -/
theorem count_le_one (hα : Feasible (famInst L a T) α) {j : ℕ} (hj : j < L.slots.length) :
    (α j).count ≤ 1 := by
  by_cases hc : (α j).count = 0
  · omega
  · have ht := hα.1 j (by simpa using hj) (Nat.pos_of_ne_zero hc)
    rw [army_len] at ht
    have hs := stock hα ht
    have hmem : j ∈ (Finset.range L.slots.length).filter (fun x => (α x).type = (α j).type) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, rfl⟩
    exact le_trans (Finset.single_le_sum (f := fun x => (α x).count) (fun _ _ => Nat.zero_le _)
      hmem) hs

/-- A type occupies at most one slot. -/
theorem type_inj (hα : Feasible (famInst L a T) α) {j j' : ℕ} (hj : j < L.slots.length)
    (hj' : j' < L.slots.length) (hc : 0 < (α j).count) (hc' : 0 < (α j').count)
    (he : (α j).type = (α j').type) : j = j' := by
  by_contra hne
  have ht := hα.1 j (by simpa using hj) hc
  rw [army_len] at ht
  have hs := stock hα ht
  have hsub : ({j, j'} : Finset ℕ) ⊆
      (Finset.range L.slots.length).filter (fun x => (α x).type = (α j).type) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj', he.symm⟩
  have := Finset.sum_le_sum_of_subset (f := fun x => (α x).count) hsub
  rw [Finset.sum_pair hne] at this
  omega

/-- The nominal blow of a slot: `a_{type}` if occupied, `0` if empty. -/
theorem nominal_eq (hα : Feasible (famInst L a T) α) {j : ℕ} (hj : j < L.slots.length) :
    nominal (famInst L a T) α j = if 0 < (α j).count then a.getD (α j).type 0 else 0 := by
  unfold nominal
  split_ifs with hc
  · have ht := hα.1 j (by simpa using hj) hc
    rw [army_len] at ht
    rw [slotType_eq hc ht, show (α j).count = 1 by have := count_le_one hα hj; omega]
    simp [famPlayer]
  · simp [show (α j).count = 0 by omega]

/-- The types a striker set holds. -/
def typesOf (α : ℕ → SlotAlloc) (F : Finset ℕ) : Finset ℕ :=
  (F.filter (fun j => 0 < (α j).count)).image (fun j => (α j).type)

theorem sum_typesOf (hα : Feasible (famInst L a T) α) {F : Finset ℕ}
    (hF : F ⊆ Finset.range L.slots.length) :
    ∑ i ∈ typesOf α F, a.getD i 0 = ∑ j ∈ F, nominal (famInst L a T) α j := by
  unfold typesOf
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [nominal_eq hα (Finset.mem_range.mp (hF hj))]
  · intro j hj j' hj' he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hj hj'
    exact type_inj hα (Finset.mem_range.mp (hF hj.1)) (Finset.mem_range.mp (hF hj'.1)) hj.2
      hj'.2 he

/-- **The no-direction core** (Lemmas E.14, E.22 from E.12, E.20): if a ledger's striker sets
each deliver at least `T` in nominal damage to the `m` enemies, `(a, T)` is a 3-partition. -/
theorem three_partition_of_ledger (hP : Promise3P a T) (hα : Feasible (famInst L a T) α)
    (hm : L.ehex.length = a.length / 3) {Q : ℕ → ℕ → Prop} {s : State} {τ : ℕ → Option ℕ}
    {β : ℕ → ℕ} (_hL : Ledger (famInst L a T) α Q s τ β)
    (hge : ∀ g < L.ehex.length, T ≤ ∑ j ∈ strikers (famInst L a T) τ g,
      nominal (famInst L a T) α j) : THREE_PARTITION a T := by
  have hFsub : ∀ g, strikers (famInst L a T) τ g ⊆ Finset.range L.slots.length := by
    intro g j hj; simp only [strikers, Finset.mem_filter, k_eq] at hj; exact hj.1
  refine ThreeP.of_disjoint hP (fun g => typesOf α (strikers (famInst L a T) τ g)) ?_ ?_ ?_
  · intro g _ i hi
    simp only [typesOf, Finset.mem_image, Finset.mem_filter] at hi
    obtain ⟨j, ⟨hj, hc⟩, rfl⟩ := hi
    have := hα.1 j (by simpa using Finset.mem_range.mp (hFsub g hj)) hc
    rw [army_len] at this
    exact Finset.mem_range.mpr this
  · intro g _ g' _ hne
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [typesOf, Finset.mem_image, Finset.mem_filter] at h1 h2
    obtain ⟨j, ⟨hj, hc⟩, rfl⟩ := h1
    obtain ⟨j', ⟨hj', hc'⟩, he⟩ := h2
    have := type_inj hα (Finset.mem_range.mp (hFsub g hj)) (Finset.mem_range.mp (hFsub g' hj'))
      hc hc' he.symm
    subst this
    exact Finset.disjoint_left.mp (Ledger.disjoint g g' hne) hj hj'
  · intro g hg
    rw [sum_typesOf hα (hFsub g)]
    exact hge g (by omega)

/-- Value destroyed in the family = number of dead enemies. -/
theorem destroyed_eq (hT : 1 ≤ T) {s : State} (hf : RFrame (famInst L a T) α s) :
    destroyed (famInst L a T) s =
      ∑ g ∈ Finset.range L.ehex.length, if (s.units (L.slots.length + g)).pool = 0 then 1 else 0 := by
  have hn := destroyed_single (I := famInst L a T)
    (fun g hg => by simp only [n_eq] at hg; rw [enemy_eq hg])
    (fun g hg => by simp only [n_eq] at hg; rw [enemy_eq hg]; exact hT) hf
  rw [hn]
  simp only [n_eq, k_eq]
  apply Finset.sum_congr rfl
  intro g hg
  rw [enemy_eq (Finset.mem_range.mp hg)]
  rfl

/-- If the value destroyed reaches `m`, every enemy is dead. -/
theorem all_dead (hT : 1 ≤ T) {s : State} (hf : RFrame (famInst L a T) α s)
    (hW : L.ehex.length ≤ destroyed (famInst L a T) s) :
    ∀ g < L.ehex.length, (s.units (L.slots.length + g)).pool = 0 := by
  rw [destroyed_eq hT hf] at hW
  have hle : ∀ g ∈ Finset.range L.ehex.length,
      (if (s.units (L.slots.length + g)).pool = 0 then 1 else 0) ≤ 1 := by
    intro g _; split_ifs <;> omega
  have heq : ∑ g ∈ Finset.range L.ehex.length,
      (if (s.units (L.slots.length + g)).pool = 0 then 1 else 0) = ∑ g ∈ Finset.range L.ehex.length, 1 := by
    apply le_antisymm (Finset.sum_le_sum hle)
    simpa using hW
  intro g hg
  have := (Finset.sum_eq_sum_iff_of_le hle).mp heq g (Finset.mem_range.mpr hg)
  split_ifs at this with h
  exact h

/-- **The no-direction of Theorems 2 and 4 (Lemmas E.14, E.22), on every layout**: if some
play destroys `W = m`, then `(a, T)` is a 3-partition.  No geometry is used. -/
theorem fam_no (hP : Promise3P a T) (hm : L.ehex.length = a.length / 3)
    (h : ArmyAllocation (famInst L a T)) : THREE_PARTITION a T := by
  obtain ⟨α, hα, s, hs, -, hW⟩ := h
  by_cases hm0 : L.ehex.length = 0
  · -- `m = 0`: the empty partition
    have h3 := hP.1
    have hlen : a.length = 0 := by omega
    refine ⟨h3, fun _ => ∅, fun g hg => by omega, fun g hg => by omega, fun i hi => by omega⟩
  have hT : 1 ≤ T := by
    have := (hP.2.2 _ (ThreeP.getD_mem (a := a) (i := 0) (by omega))).2; omega
  have ha : ∀ x ∈ a, 1 ≤ x := fun x hx => by have := (hP.2.2 x hx).1; omega
  obtain ⟨τ, β, hL⟩ := ledger (acctHyp (L := L) hT ha) hα (P := fun _ _ => True)
    (fun _ _ _ _ _ _ _ _ => trivial) hs
  have hdead := all_dead hT (Reach.frame hs) hW
  refine three_partition_of_ledger hP hα hm hL (fun g hg => ?_)
  have := hL.dead (by simpa using hg) (by simpa using hdead g hg)
  rwa [enemy_eq hg] at this

/-- **A per-allocation bound** (from the ledger): `destroyed · T ≤ Σ_j nominal(j)` — each dead
enemy absorbed `T` from its own, pairwise disjoint, strikers. -/
theorem destroyed_mul_le (hT : 1 ≤ T) (ha : ∀ x ∈ a, 1 ≤ x) (hα : Feasible (famInst L a T) α)
    {s : State} (hs : Reach (famInst L a T) α s) :
    destroyed (famInst L a T) s * T ≤
      ∑ j ∈ Finset.range L.slots.length, nominal (famInst L a T) α j := by
  obtain ⟨τ, β, hL⟩ := ledger (acctHyp (L := L) hT ha) hα (P := fun _ _ => True)
    (fun _ _ _ _ _ _ _ _ => trivial) hs
  rw [destroyed_eq hT (Reach.frame hs), Finset.sum_mul]
  have hstep : ∀ g ∈ Finset.range L.ehex.length,
      (if (s.units (L.slots.length + g)).pool = 0 then 1 else 0) * T ≤
        ∑ j ∈ strikers (famInst L a T) τ g, nominal (famInst L a T) α j := by
    intro g hg
    split_ifs with h0
    · have := hL.dead (g := g) (by simpa using hg) (by simpa using h0)
      rw [enemy_eq (Finset.mem_range.mp hg)] at this
      simpa [famEnemy] using this
    · simp
  refine (Finset.sum_le_sum hstep).trans ?_
  have hpd : ((Finset.range L.ehex.length : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (strikers (famInst L a T) τ) := fun g _ g' _ hne => Ledger.disjoint g g' hne
  rw [← Finset.sum_biUnion hpd]
  apply Finset.sum_le_sum_of_subset
  intro j hj
  obtain ⟨g, -, hjg⟩ := Finset.mem_biUnion.mp hj
  simp only [strikers, Finset.mem_filter, k_eq] at hjg
  exact hjg.1

end Fam

end Homm3
