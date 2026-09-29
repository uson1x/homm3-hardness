import Homm3.Theorem2
import Homm3.Walk

/-!
# Session 3, targets 2–3. Theorem 4 (the featureless board `G_F(a, T)`), Corollaries 4.1, 4.2

Paper: §3.4 and Appendix E, "Theorem 4 and its corollaries" — the instance `G_F(a, T)`,
Lemmas E.15–E.22, the proofs of Theorem 4 and Corollaries 4.1 and 4.2.

* `GF a T` — six rows (`y = 0 … 5`), `w = 4m + 2` columns, no obstacles; enemy `E_g` (0-indexed
  `g`, the paper's `g + 1`) at `e_g = (X_g, 3)`, `X_g = 4g + 2`; slots `p_j = (j, 0)`,
  `j < 3m`; player types `C_i = (1, 1, a_i, hp 5, spd s = 4m + 8, value 0)`, stock one; enemies
  `(1, 1, 1, hp T, spd 1, value 1)`; `R = 1`, `W = m`.  `famInst (ThmF.layout m) a T`.
* The approach hexes `(Q)`: `q_g^1 = (X_g − 1, 2)`, `q_g^2 = (X_g, 2)`, `q_g^3 = (X_g + 1, 3)`
  (`ThmF.seat g 0/1/2`).
* **Lemma E.15**: `ThmF.nbrs_ehex` (the list `(N)`), `ThmF.seat_mem_nbrs`, `ThmF.seat_inj`,
  `ThmF.seat_y` (rows 2–3, off the deployment row).
* **Attack-only plays** (`AOReach`, via `succsAO` of `Exec.lean`, a sub-relation of `Step`).
* **Lemma E.16**: `ThmF.lemmaE16` — along every attack-only play every hex of a stack is in
  row 0, an enemy hex, or adjacent to one; `ThmF.clear_of_AO`: rows 1 and 5 and the hexes
  `(X_g + 1, 2)` are free throughout.
* **Lemma E.17**: `ThmF.route` — from `p_j`, one step into row 1, along row 1, down to a free
  seat, in at most `w + 2 ≤ s` steps (explicit walk, `Walk.lean`).
* **Lemma E.18**: `ThmF.lemmaE18` — complete reachability in the starting position, for every
  feasible allocation (the crowded board, all slots occupied, is the case `α` total).
-/

namespace Homm3

open Function

/-! ## Attack-only plays (any instance) -/

section AO

variable {I : Instance} {α : ℕ → SlotAlloc} {s s' : State}

/-- Positions reachable by an **attack-only** play (`brute_force.py`'s fragment): every player
stack passes or issues `WALK_AND_ATTACK`; the defence plays `(‡)`. -/
def AOReach (I : Instance) (α : ℕ → SlotAlloc) (s : State) : Prop :=
  Relation.ReflTransGen (fun s s' => s' ∈ succsAO I s) (initState I α) s

theorem AOReach.reach (h : AOReach I α s) : Reach I α s := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_of_mem_succsAO hst)

/-- An attack-only step leaves every hex in place, except a `WALK_AND_ATTACK`'s. -/
theorem succsAO_cases (h : s' ∈ succsAO I s) :
    (∀ j, (s'.units j).hex = (s.units j).hex) ∨
    ∃ i q dest t, s.queue = i :: q ∧ (s.units i).side = .player ∧ t < I.N ∧
      (s.units t).alive ∧ (s.units t).side = .enemy ∧ Hex.Adj dest (s.units t).hex ∧
      s'.units = resolveAttack s.units i t dest := by
  rcases hq : s.queue with _ | ⟨i, q⟩
  · left
    simp only [succsAO, hq, succsEnd, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h <;> simp at h <;> subst h <;> intro j <;>
      simp [sToWait, newRound]
  · simp only [succsAO, hq] at h
    split_ifs at h with ha hs hp
    · left; simp only [List.mem_singleton] at h; subst h; intro j
      simp only [sWait, update_apply]; split_ifs <;> subst_vars <;> simp [activate]
    · left; simp only [List.mem_singleton] at h; subst h; intro j
      simp only [sDefend, update_apply]; split_ifs <;> subst_vars <;> simp [activate]
    · rcases List.mem_cons.mp h with h | h
      · left; subst h; intro j
        simp only [sMove, update_apply]; split_ifs <;> subst_vars <;> simp [activate]
      · right
        obtain ⟨dest, -, t, ht, hta, hts, hadj, rfl⟩ := mem_attacks.mp h
        have hsp : (s.units i).side = .player := by
          cases h' : (s.units i).side <;> simp_all
        exact ⟨i, q, dest, t, rfl, hsp, ht, hta, hts, hadj, rfl⟩
    · left; simp only [List.mem_singleton] at h; subst h; intro j; rfl

theorem attack_mem_succsAO {i t : ℕ} {q : List ℕ} {dest : Hex} (hq : s.queue = i :: q)
    (ha : (s.units i).alive) (hs : (s.units i).side = .player) (hd : dest ∈ reachOf I s.units i)
    (ht : t < I.N) (hta : (s.units t).alive) (hts : (s.units t).side = .enemy)
    (hadj : Hex.Adj dest (s.units t).hex) : sAttack s i q dest t ∈ succsAO I s := by
  have hne : (s.units i).side ≠ .enemy := by rw [hs]; decide
  simp only [succsAO, hq, ha, hne, ↓reduceIte]
  exact List.mem_cons_of_mem _ (mem_attacks.mpr ⟨dest, hd, t, ht, hta, hts, hadj, rfl⟩)

theorem wait_mem_succsAO {i : ℕ} {q : List ℕ} (hp : s.phase = .normal) (hq : s.queue = i :: q)
    (ha : (s.units i).alive) (hs : (s.units i).side = .enemy) : sWait s i q ∈ succsAO I s := by
  simp [succsAO, hq, ha, hs, hp]

theorem skip_mem_succsAO {i : ℕ} {q : List ℕ} (hq : s.queue = i :: q)
    (ha : ¬ (s.units i).alive) : sSkip s q ∈ succsAO I s := by
  simp [succsAO, hq, ha]

/-- Every position can be completed to a finished battle by an attack-only play. -/
theorem exists_doneAO (I : Instance) (s : State) :
    ∃ s', Relation.ReflTransGen (fun s s' => s' ∈ succsAO I s) s s' ∧ Done s' := by
  induction hμ : μ I s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hd : Done s
    · exact ⟨s, .refl, hd⟩
    · obtain ⟨s1, hs1⟩ := List.exists_mem_of_ne_nil _ (succsAO_ne_nil (I := I) hd)
      obtain ⟨s2, h2, hd2⟩ := ih _ (hμ ▸ (step_of_mem_succsAO hs1).μ_lt) s1 rfl
      exact ⟨s2, .head hs1 h2, hd2⟩

theorem rtg_step_of_AO {s₁ s₂ : State}
    (h : Relation.ReflTransGen (fun s s' => s' ∈ succsAO I s) s₁ s₂) :
    Relation.ReflTransGen (Step I) s₁ s₂ := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_of_mem_succsAO hst)

/-- The attacker of a `WALK_AND_ATTACK` ends on its approach hex. -/
theorem resolveAttack_self_hex {us : ℕ → Stack} {i t : ℕ} {dest : Hex} (hit : i ≠ t) :
    (resolveAttack us i t dest i).hex = dest := by
  unfold resolveAttack
  split_ifs <;> simp [hit, Stack.hit, activate]

end AO

/-! ## The instance `G_F(a, T)` -/

namespace ThmF

/-- `e_g = (X_g, 3)`, `X_g = 4g + 2`. -/
def ehex (g : ℕ) : Hex := ⟨4 * (g : ℤ) + 2, 3⟩

/-- `(Q)`: `q_g^1 = (X_g − 1, 2)`, `q_g^2 = (X_g, 2)`, `q_g^3 = (X_g + 1, 3)`. -/
def seat (g r : ℕ) : Hex :=
  if r = 0 then ⟨4 * (g : ℤ) + 1, 2⟩ else if r = 1 then ⟨4 * (g : ℤ) + 2, 2⟩
  else ⟨4 * (g : ℤ) + 3, 3⟩

/-- `p_j = (j, 0)` (the paper's `p_{j+1} = (j, 0)`). -/
def phex (j : ℕ) : Hex := ⟨(j : ℤ), 0⟩

/-- The layout of `G_F` with `m` enemies: `6 × (4m + 2)`, speed `s = w + h = 4m + 8`. -/
def layout (m : ℕ) : Layout where
  width := 4 * m + 2
  height := 6
  slots := (List.range (3 * m)).map phex
  ehex := (List.range m).map ehex
  spd := 4 * m + 8

end ThmF

/-- **The instance `G_F(a, T)`.** -/
def GF (a : List ℕ) (T : ℕ) : Instance := famInst (ThmF.layout (a.length / 3)) a T

namespace ThmF

variable {a : List ℕ} {T : ℕ}

@[simp] theorem slots_len (m : ℕ) : (layout m).slots.length = 3 * m := by simp [layout]
@[simp] theorem ehex_len (m : ℕ) : (layout m).ehex.length = m := by simp [layout]

theorem k_eq : (GF a T).k = 3 * (a.length / 3) := by simp [GF]
theorem n_eq : (GF a T).n = a.length / 3 := by simp [GF]
theorem W_eq : (GF a T).W = a.length / 3 := by simp [GF]
theorem N_eq : (GF a T).N = 3 * (a.length / 3) + a.length / 3 := by
  unfold Instance.N; rw [k_eq, n_eq]

theorem slotHex_eq {j : ℕ} (hj : j < 3 * (a.length / 3)) : (GF a T).slotHex j = phex j := by
  simp [GF, Fam.slotHex_eq, layout, hj]

theorem enemy_eq' {g : ℕ} (hg : g < a.length / 3) :
    (GF a T).enemy g = ⟨famEnemy T, 1, ehex g⟩ := by
  unfold GF; rw [Fam.enemy_eq (by simpa using hg)]; simp [layout, hg]

theorem spd_of_mem {x : CType × ℕ} (hx : x ∈ (GF a T).army) : x.1.spd = 4 * (a.length / 3) + 8 := by
  simp only [GF, famInst, List.mem_map] at hx
  obtain ⟨ai, -, rfl⟩ := hx; rfl

/-! ## Lemma E.15 -/

/-- `(N)`: row 3 is odd, so the neighbours of `e_g` are `(X_g ∓ 1, 3)`, `(X_g − 1, 2)`,
`(X_g, 2)`, `(X_g − 1, 4)`, `(X_g, 4)`. -/
theorem nbrs_ehex (g : ℕ) : (ehex g).nbrs =
    [⟨4 * (g : ℤ) + 1, 3⟩, ⟨4 * (g : ℤ) + 3, 3⟩, ⟨4 * (g : ℤ) + 1, 2⟩, ⟨4 * (g : ℤ) + 2, 2⟩,
      ⟨4 * (g : ℤ) + 1, 4⟩, ⟨4 * (g : ℤ) + 2, 4⟩] := by
  simp only [ehex, Hex.nbrs, List.cons.injEq, Hex.mk.injEq, and_true]
  norm_num; omega

/-- **Lemma E.15**: the three hexes of `(Q)` are neighbours of `e_g`. -/
theorem seat_mem_nbrs (g : ℕ) {r : ℕ} (hr : r < 3) : seat g r ∈ (ehex g).nbrs := by
  rw [nbrs_ehex]; interval_cases r <;> simp [seat]

theorem seat_adj (g : ℕ) {r : ℕ} (hr : r < 3) : Hex.Adj (seat g r) (ehex g) :=
  Hex.adj_symm (seat_mem_nbrs g hr)

/-- **Lemma E.15**: the `3m` seats are pairwise distinct. -/
theorem seat_inj {g r g' r' : ℕ} (hr : r < 3) (hr' : r' < 3) (h : seat g r = seat g' r') :
    g = g' ∧ r = r' := by
  interval_cases r <;> interval_cases r' <;> simp [seat] at h <;> omega

/-- **Lemma E.15**: seats lie in rows 2 and 3, off the deployment row. -/
theorem seat_y (g : ℕ) {r : ℕ} (hr : r < 3) : (seat g r).y = 2 ∨ (seat g r).y = 3 := by
  interval_cases r <;> simp [seat]

theorem seat_ne_ehex (g r g' : ℕ) (hr : r < 3) : seat g r ≠ ehex g' := by
  interval_cases r <;> simp [seat, ehex] <;> omega

theorem ehex_inj {g g' : ℕ} (h : ehex g = ehex g') : g = g' := by
  simp [ehex] at h; omega

/-- The board fits: seats, enemy hexes and deployment hexes are on the `6 × (4m + 2)` board. -/
theorem inBounds_seat {g r : ℕ} (hg : g < a.length / 3) (hr : r < 3) :
    (GF a T).inBounds (seat g r) := by
  simp only [Instance.inBounds, GF, famInst, layout]
  interval_cases r <;> simp [seat] <;> omega

theorem inBounds_row {x y : ℤ} (hx0 : 0 ≤ x) (hx : x < 4 * (a.length / 3 : ℕ) + 2) (hy0 : 0 ≤ y)
    (hy : y < 6) : (GF a T).inBounds ⟨x, y⟩ := by
  simp only [Instance.inBounds, GF, famInst, layout]; push_cast at hx ⊢; omega

variable {α : ℕ → SlotAlloc} {s : State}

theorem hex_enemy (h : Reach (GF a T) α s) {g : ℕ} (hg : g < a.length / 3) :
    (s.units ((GF a T).k + g)).hex = ehex g := by
  have hf := h.frame
  have hg' : g < (GF a T).n := by rw [n_eq]; exact hg
  rw [hf.ehex _ (by rw [initUnits_enemy hg']), initUnits_enemy hg', enemy_eq' hg]

theorem hex_of_Q (h : Reach (GF a T) α s) {i : ℕ} (hi : i < 3 * (a.length / 3)) (hiQ : i ∈ s.Q) :
    (s.units i).hex = phex i := by
  obtain ⟨-, -, hhex⟩ := lemmaE1 rfl h
  rw [hhex i hiQ, initUnits_player (by rw [k_eq]; exact hi)]
  exact slotHex_eq hi

/-! ## Lemma E.16 -/

/-- **Lemma E.16 (row 1 stays clear)**: along every attack-only play of round 1, every stack's
hex is in row 0, is an enemy hex, or is adjacent to an enemy hex. -/
theorem lemmaE16 (h : AOReach (GF a T) α s) : ∀ i < (GF a T).N,
    (s.units i).hex.y = 0 ∨ ∃ g < a.length / 3,
      (s.units i).hex = ehex g ∨ Hex.Adj (s.units i).hex (ehex g) := by
  induction h with
  | refl =>
    intro i hi
    by_cases hik : i < (GF a T).k
    · left
      simp only [initState]
      rw [initUnits_player hik, slotHex_eq (by rw [← k_eq]; exact hik)]; rfl
    · right
      obtain ⟨g, hg, rfl⟩ : ∃ g < (GF a T).n, i = (GF a T).k + g :=
        ⟨i - (GF a T).k, by unfold Instance.N at hi; omega, by omega⟩
      rw [n_eq] at hg
      refine ⟨g, hg, Or.inl ?_⟩
      simp only [initState]
      rw [initUnits_enemy (by rw [n_eq]; exact hg), enemy_eq' hg]
  | @tail s₁ s₂ h₁ hst ih =>
    intro i hi
    rcases succsAO_cases hst with hall | ⟨i0, q, dest, t, hq, hs, ht, hta, hts, hadj, hus⟩
    · rw [hall]; exact ih i hi
    · have hf := Reach.frame (AOReach.reach h₁)
      have hi0 : i0 < (GF a T).k := initUnits_side_player (by rw [← hf.side]; exact hs)
      obtain ⟨g, hg, rfl⟩ := enemy_index ht (by rw [← hf.side]; exact hts)
      rw [n_eq] at hg
      rw [hus]
      by_cases hii : i = i0
      · subst hii
        rw [resolveAttack_self_hex (by omega)]
        rw [hex_enemy (AOReach.reach h₁) hg] at hadj
        exact Or.inr ⟨g, hg, Or.inr hadj⟩
      · rw [resolveAttack_hex_of_ne hii]; exact ih i hi

/-- The hexes the routing of Lemma E.17 walks through: all of row 1, and `(X_g + 1, 2)`. -/
def Clear (a : List ℕ) (T : ℕ) (s : State) : Prop :=
  ∀ i < (GF a T).N, (s.units i).alive →
    (s.units i).hex.y ≠ 1 ∧ ∀ g < a.length / 3, (s.units i).hex ≠ ⟨4 * (g : ℤ) + 3, 2⟩

/-- **Lemma E.16, consequence**: rows 1 and 5, and every `(X_g + 1, 2)`, are free throughout an
attack-only play. -/
theorem clear_of_AO (h : AOReach (GF a T) α s) : Clear a T s ∧
    ∀ i < (GF a T).N, (s.units i).hex.y ≠ 5 := by
  have key : ∀ i < (GF a T).N, (s.units i).hex.y ≠ 1 ∧ (s.units i).hex.y ≠ 5 ∧
      ∀ g < a.length / 3, (s.units i).hex ≠ ⟨4 * (g : ℤ) + 3, 2⟩ := by
    intro i hi
    rcases lemmaE16 h i hi with h0 | ⟨g, hg, he | hadj⟩
    · refine ⟨by omega, by omega, fun g _ e => ?_⟩
      rw [e] at h0; simp at h0
    · rw [he]; refine ⟨by simp [ehex], by simp [ehex], fun g' _ e => ?_⟩
      simp [ehex] at e
    · have hm := Hex.adj_symm hadj
      unfold Hex.Adj at hm
      rw [nbrs_ehex] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e' | e' | e' | e' | e' | e' <;> rw [e'] <;>
        refine ⟨by simp, by simp, fun g' _ e => ?_⟩ <;> simp at e <;> omega
  exact ⟨fun i hi _ => ⟨(key i hi).1, (key i hi).2.2⟩, fun i hi => (key i hi).2.1⟩

/-! ## Lemma E.17 -/

/-- A hex no living stack but `j` stands on, on the board, is enterable by `j`. -/
theorem free_of {us : ℕ → Stack} {j : ℕ} {h : Hex} (hb : (GF a T).inBounds h)
    (hno : ∀ i < (GF a T).N, i ≠ j → (us i).alive → (us i).hex ≠ h) : free (GF a T) us j h :=
  ⟨hb, by simp [GF, famInst], hno⟩

/-- **Lemma E.17 (routing)**: a stack on `p_j` whose seat `q_g^r` is free reaches it, via
row 1, within `w + 2 ≤ s` steps, whatever the order of activation. -/
theorem route (hC : Clear a T s) {j : ℕ} (hj : j < 3 * (a.length / 3))
    (hpos : (s.units j).hex = phex j) (hspd : (s.units j).type.spd = 4 * (a.length / 3) + 8)
    {g r : ℕ} (hg : g < a.length / 3) (hr : r < 3)
    (hfree : free (GF a T) s.units j (seat g r)) : seat g r ∈ reachOf (GF a T) s.units j := by
  set m := a.length / 3 with hm
  have hrow : ∀ x : ℤ, 0 ≤ x → x < 4 * (m : ℤ) + 2 → free (GF a T) s.units j ⟨x, 1⟩ := by
    intro x hx0 hxw
    refine free_of (inBounds_row hx0 (by push_cast; omega) (by norm_num) (by norm_num)) ?_
    intro i hi _ hal e
    exact (hC i hi hal).1 (by rw [e])
  have hmid : free (GF a T) s.units j ⟨4 * (g : ℤ) + 3, 2⟩ := by
    refine free_of (inBounds_row (by omega) (by push_cast; omega) (by norm_num) (by norm_num)) ?_
    intro i hi _ hal e
    exact (hC i hi hal).2 g hg e
  unfold reachOf
  rw [hpos, hspd]
  -- one step down into row 1
  have h1 : (⟨(j : ℤ), 1⟩ : Hex) ∈ reach (free (GF a T) s.units j) (phex j) 1 := by
    refine reach_succ (start_mem_reach _ 0) ?_ (hrow _ (by omega) (by push_cast; omega))
    simp [phex, Hex.Adj, Hex.nbrs]
  -- along row 1 to the column above the seat
  set c : ℤ := if r = 2 then 4 * (g : ℤ) + 3 else if r = 1 then 4 * (g : ℤ) + 2 else 4 * g + 1
    with hc
  have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> omega
  have hcw : c < 4 * (m : ℤ) + 2 := by rw [hc]; split_ifs <;> omega
  have h2 := reach_row hrow (c - j).natAbs j c 1 (by omega) (by push_cast; omega) hc0 hcw rfl h1
  have hd : (c - j).natAbs ≤ 4 * m - 1 := by
    rw [hc]; split_ifs <;> omega
  -- and down to the seat
  have hmono : ∀ t, t ≤ 4 * m + 8 → seat g r ∈ reach (free (GF a T) s.units j) (phex j) t →
      seat g r ∈ reach (free (GF a T) s.units j) (phex j) (4 * m + 8) :=
    fun t ht hmem => reach_mono _ ht hmem
  interval_cases r
  · refine hmono _ (by omega) (reach_succ h2 ?_ hfree)
    simp [hc, seat, Hex.Adj, Hex.nbrs]
  · refine hmono _ (by omega) (reach_succ h2 ?_ hfree)
    simp [hc, seat, Hex.Adj, Hex.nbrs]
  · have h3 := reach_succ h2 (q := ⟨4 * (g : ℤ) + 3, 2⟩) (by simp [hc, Hex.Adj, Hex.nbrs]) hmid
    refine hmono _ (by omega) (reach_succ h3 ?_ hfree)
    simp [seat, Hex.Adj, Hex.nbrs]

/-! ## Lemma E.18 -/

/-- **Lemma E.18 (complete reachability)**: in the starting position of `G_F`, under every
feasible allocation (in particular with all `3m` slots occupied), every player stack can
attack every enemy stack. -/
theorem lemmaE18 (hT : 1 ≤ T) (hα : Feasible (GF a T) α) {j : ℕ} (hj : j < (GF a T).k)
    (hal : (initUnits (GF a T) α j).alive) {g : ℕ} (hg : g < a.length / 3) :
    CanStrike (GF a T) (initState (GF a T) α).units j ((GF a T).k + g) := by
  have hj' : j < 3 * (a.length / 3) := by rw [← k_eq]; exact hj
  obtain ⟨x, hx, hty⟩ := slotType_mem hα hj hal
  have hC : Clear a T (initState (GF a T) α) := (clear_of_AO (α := α) .refl).1
  have hpos : ((initState (GF a T) α).units j).hex = phex j := by
    simp only [initState]; rw [initUnits_player hj, slotHex_eq hj']
  have hspd : ((initState (GF a T) α).units j).type.spd = 4 * (a.length / 3) + 8 := by
    simp only [initState]; rw [initUnits_player hj]; simp only; rw [hty]; exact spd_of_mem hx
  have hfree : free (GF a T) (initState (GF a T) α).units j (seat g 0) := by
    refine free_of (inBounds_seat hg (by norm_num)) ?_
    intro i hi _ _ e
    simp only [initState] at e
    by_cases hik : i < (GF a T).k
    · rw [initUnits_player hik, slotHex_eq (by rw [← k_eq]; exact hik)] at e
      simp [phex, seat] at e
    · obtain ⟨g', hg', rfl⟩ : ∃ g' < (GF a T).n, i = (GF a T).k + g' :=
        ⟨i - (GF a T).k, by unfold Instance.N at hi; omega, by omega⟩
      rw [n_eq] at hg'
      rw [initUnits_enemy (by rw [n_eq]; exact hg'), enemy_eq' hg'] at e
      exact seat_ne_ehex g 0 g' (by norm_num) e.symm
  refine ⟨by rw [N_eq, k_eq]; omega, ?_, ?_, seat g 0, route hC hj' hpos hspd hg (by norm_num) hfree,
    ?_⟩
  · simp only [initState]; rw [initUnits_enemy (by rw [n_eq]; exact hg)]
  · simp only [initState, Stack.alive]
    rw [initUnits_enemy (by rw [n_eq]; exact hg), enemy_eq' hg]
    simp [famEnemy]; omega
  · simp only [initState]
    rw [initUnits_enemy (by rw [n_eq]; exact hg), enemy_eq' hg]
    exact seat_adj g (by norm_num)

end ThmF

/-! ## The end of the round is frozen once the player has acted -/

/-- After the `NORMAL` phase of the last round, if no player stack is left to act, nothing
moves and no pool changes. -/
def Frozen (s : State) : Prop :=
  s.roundsLeft = 1 ∧ ((s.phase = .normal ∧ s.queue = [] ∧ ∀ i ∈ s.bucket, (s.units i).side = .enemy) ∨
    (s.phase = .wait ∧ ∀ i ∈ s.queue, (s.units i).side = .enemy))

theorem Frozen.step {I : Instance} {s s' : State} (hz : Frozen s) (h : Step I s s') :
    Frozen s' ∧ ∀ j, (s'.units j).pool = (s.units j).pool ∧ (s'.units j).hex = (s.units j).hex := by
  obtain ⟨hr, hc⟩ := hz
  cases h with
  | skip hq ha =>
    refine ⟨⟨hr, ?_⟩, fun j => ⟨rfl, rfl⟩⟩
    rcases hc with ⟨-, hq', -⟩ | ⟨hp, hQ⟩
    · rw [hq'] at hq; cases hq
    · exact Or.inr ⟨hp, fun x hx => hQ x (by rw [hq]; exact List.mem_cons_of_mem _ hx)⟩
  | enemyWait hp hq =>
    rcases hc with ⟨-, hq', -⟩ | ⟨hp', -⟩
    · rw [hq'] at hq; cases hq
    · rw [hp] at hp'; cases hp'
  | enemyDefend hp hq ha hs =>
    rcases hc with ⟨hp', -⟩ | ⟨-, hQ⟩
    · rw [hp] at hp'; cases hp'
    refine ⟨⟨hr, Or.inr ⟨hp, fun x hx => ?_⟩⟩, fun j => ?_⟩
    · simp only [update_apply]; split_ifs with he
      · subst he; simpa [activate] using hs
      · exact hQ x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
    · simp only [update_apply]; split_ifs with he
      · subst he; simp [activate]
      · exact ⟨rfl, rfl⟩
  | playerWait hp hq _ hs =>
    rcases hc with ⟨-, hq', -⟩ | ⟨hp', -⟩
    · rw [hq'] at hq; cases hq
    · rw [hp] at hp'; cases hp'
  | playerDefend hq _ hs | playerMove hq _ hs | playerAttack hq _ hs =>
    rcases hc with ⟨-, hq', -⟩ | ⟨-, hQ⟩
    · rw [hq'] at hq; cases hq
    · have := hQ _ (by rw [hq]; exact List.mem_cons_self); rw [hs] at this; cases this
  | toWait hp hq =>
    rcases hc with ⟨-, -, hB⟩ | ⟨hp', -⟩
    · refine ⟨⟨hr, Or.inr ⟨rfl, fun x hx => hB x ((List.mergeSort_perm _ _).mem_iff.mp hx)⟩⟩,
        fun j => ⟨rfl, rfl⟩⟩
    · rw [hp] at hp'; cases hp'
  | nextRound _ _ h1 => omega

theorem Frozen.run {I : Instance} {s s' : State} (hz : Frozen s)
    (h : Relation.ReflTransGen (Step I) s s') :
    ∀ j, (s'.units j).pool = (s.units j).pool ∧ (s'.units j).hex = (s.units j).hex := by
  have : Frozen s' ∧ ∀ j, (s'.units j).pool = (s.units j).pool ∧
      (s'.units j).hex = (s.units j).hex := by
    induction h with
    | refl => exact ⟨hz, fun j => ⟨rfl, rfl⟩⟩
    | tail _ hst ih =>
      obtain ⟨hz1, h1⟩ := ih
      obtain ⟨hz2, h2⟩ := hz1.step hst
      exact ⟨hz2, fun j => ⟨(h2 j).1.trans (h1 j).1, (h2 j).2.trans (h1 j).2⟩⟩
  exact this.2

namespace ThmF

variable {a : List ℕ} {T : ℕ}

/-! ## Lemma E.19: simultaneous realizability -/

/-- A seating of the `3m` slots, three per enemy: slot `st g r` is sent to `q_g^{r+1}`. -/
structure Seating (m : ℕ) (st : ℕ → ℕ → ℕ) : Prop where
  lt : ∀ g < m, ∀ r < 3, st g r < 3 * m
  inj : ∀ g < m, ∀ r < 3, ∀ g' < m, ∀ r' < 3, st g r = st g' r' → g = g' ∧ r = r'
  cover : ∀ j < 3 * m, ∃ g < m, ∃ r < 3, st g r = j

/-- A full allocation: slot `j` holds one creature of type `π j`. -/
def απ (π : ℕ → ℕ) (j : ℕ) : SlotAlloc := ⟨π j, 1⟩

/-- The allocation of Lemma E.21 and Corollary 4.1: `C_i ↦ slot i`. -/
def αId : ℕ → SlotAlloc := απ id

/-- `π` is an injection of the slots `[3m]` into the types `[|a|]`. -/
structure Inj (a : List ℕ) (π : ℕ → ℕ) : Prop where
  lt : ∀ j < 3 * (a.length / 3), π j < a.length
  inj : ∀ j < 3 * (a.length / 3), ∀ j' < 3 * (a.length / 3), π j = π j' → j = j'

theorem Inj.id : Inj a id := ⟨fun j hj => by simp; omega, fun _ _ _ _ h => h⟩

variable {π : ℕ → ℕ} {st : ℕ → ℕ → ℕ}

theorem απ_feasible (hπ : Inj a π) : Feasible (GF a T) (απ π) := by
  refine ⟨fun j hj _ => ?_, fun t ht => ?_⟩
  · rw [k_eq] at hj
    simp only [απ, GF, Fam.army_len]
    exact hπ.lt j hj
  · have ht' : t < a.length := by simpa [GF, Fam.army_len] using ht
    have h1 : ((GF a T).army.getD t default).2 = 1 := by
      unfold GF; rw [Fam.army_getD ht']
    rw [h1]
    simp only [απ]
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    apply Finset.card_le_one.mpr
    intro j hj j' hj'
    simp only [Finset.mem_filter, Finset.mem_range, k_eq] at hj hj'
    exact hπ.inj j hj.1 j' hj'.1 (hj.2.trans hj'.2.symm)

theorem init_player_απ (hπ : Inj a π) {j : ℕ} (hj : j < (GF a T).k) :
    initUnits (GF a T) (απ π) j =
      ⟨.player, j, famPlayer (4 * (a.length / 3) + 8) (a.getD (π j) 0), phex j, 5, 1, 1, false⟩ := by
  have hj' : j < 3 * (a.length / 3) := by rw [← k_eq]; exact hj
  have hty : (GF a T).slotType (απ π) j = famPlayer (4 * (a.length / 3) + 8) (a.getD (π j) 0) :=
    Fam.slotType_eq (L := layout (a.length / 3)) (α := απ π) (by simp [απ]) (hπ.lt j hj')
  rw [initUnits_player hj, hty, slotHex_eq hj']
  simp [απ, famPlayer]

theorem init_enemy_GF {α : ℕ → SlotAlloc} {g : ℕ} (hg : g < a.length / 3) :
    initUnits (GF a T) α ((GF a T).k + g) = ⟨.enemy, g, famEnemy T, ehex g, T, 1, 1, false⟩ := by
  rw [initUnits_enemy (by rw [n_eq]; exact hg), enemy_eq' hg]
  simp [famEnemy]

/-- Invariant of the witness run of Lemma E.19 in the `NORMAL` phase. -/
structure WF (a : List ℕ) (T : ℕ) (π : ℕ → ℕ) (st : ℕ → ℕ → ℕ) (s : State) : Prop where
  reach : AOReach (GF a T) (απ π) s
  phase : s.phase = .normal
  bucket : ∀ i ∈ s.bucket, (s.units i).side = .enemy
  fresh : ∀ j < (GF a T).k, j ∈ s.queue → (s.units j).pool = 5
  seated : ∀ g < a.length / 3, ∀ r < 3, st g r ∉ s.queue → (s.units (st g r)).hex = seat g r
  edef : ∀ g < a.length / 3, (s.units ((GF a T).k + g)).defending = false
  epool : ∀ g < a.length / 3, (s.units ((GF a T).k + g)).pool =
    T - ∑ r ∈ (Finset.range 3).filter (fun r => st g r ∉ s.queue), a.getD (π (st g r)) 0

theorem WF.init (hπ : Inj a π) (hst : Seating (a.length / 3) st) :
    WF a T π st (initState (GF a T) (απ π)) where
  reach := .refl
  phase := rfl
  bucket := by simp [initState]
  fresh j hj _ := by simp only [initState]; rw [init_player_απ hπ hj]
  seated g hg r hr hq := by
    exfalso; apply hq
    have hj : st g r < (GF a T).k := by rw [k_eq]; exact hst.lt g hg r hr
    apply Prop11.mem_initQueue (by unfold Instance.N; omega)
    rw [init_player_απ hπ hj]; unfold Stack.alive; norm_num
  edef g hg := by simp only [initState]; rw [init_enemy_GF hg]
  epool g hg := by
    simp only [initState]
    rw [init_enemy_GF hg]
    have : (Finset.range 3).filter (fun r => st g r ∉ (initState (GF a T) (απ π)).queue) = ∅ := by
      apply Finset.filter_false_of_mem
      intro r hr
      simp only [Finset.mem_range] at hr
      have hj : st g r < (GF a T).k := by rw [k_eq]; exact hst.lt g hg r hr
      rw [not_not]
      apply Prop11.mem_initQueue (by unfold Instance.N; omega)
      rw [init_player_απ hπ hj]; unfold Stack.alive; norm_num
    simp only [initState] at this
    rw [this]; simp

/-- One step of the witness run: the stack `st g r` walks to `q_g^{r+1}` and strikes `E_g`;
an enemy `WAIT`s; a dead stack is skipped. -/
theorem WF.step (hT : 1 ≤ T) (hbd : ∀ x ∈ a, 1 ≤ x ∧ 2 * x < T) (hπ : Inj a π)
    (hst : Seating (a.length / 3) st) {s : State} (hw : WF a T π st s) {i : ℕ} {q : List ℕ}
    (hq : s.queue = i :: q) :
    ∃ s', s' ∈ succsAO (GF a T) s ∧ WF a T π st s' ∧ s'.queue = q := by
  have hreach := AOReach.reach hw.reach
  obtain ⟨-, hn, -⟩ := lemmaE1 rfl hreach
  have hf := Reach.frame hreach
  have hnq := head_not_mem_after hq hn
  have hmem : ∀ j, j ∈ q ↔ j ∈ s.queue ∧ j ≠ i := by
    intro j; rw [hq, List.mem_cons]
    constructor
    · intro hj; exact ⟨Or.inr hj, fun e => hnq (e ▸ List.mem_append_left _ hj)⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
  have hfilt_ne : ∀ g', (∀ x < 3, st g' x ≠ i) →
      (Finset.range 3).filter (fun r' => st g' r' ∉ q) =
        (Finset.range 3).filter (fun r' => st g' r' ∉ s.queue) := by
    intro g' hne
    apply Finset.filter_congr
    intro x hx
    rw [Finset.mem_range] at hx
    rw [hmem]
    constructor
    · intro h h'; exact h ⟨h', hne x hx⟩
    · rintro h ⟨h', -⟩; exact h h'
  have hK := k_eq (a := a) (T := T)
  by_cases ha : (s.units i).alive
  · rcases hside : (s.units i).side with _ | _
    · -- a player stack: walk to its seat and strike
      have hi : i < (GF a T).k := initUnits_side_player (by rw [← hf.side]; exact hside)
      obtain ⟨g, hg, r, hr, hgr⟩ := hst.cover i (by omega)
      have hiQ : i ∈ s.Q := by simp [State.Q, hq]
      have hpool : (s.units i).pool = 5 := hw.fresh i hi (by rw [hq]; exact List.mem_cons_self)
      have hty : (s.units i).type = famPlayer (4 * (a.length / 3) + 8) (a.getD (π i) 0) := by
        rw [hf.type, init_player_απ hπ hi]
      set ai := a.getD (π i) 0 with haidef
      have hai := hbd _ (ThreeP.getD_mem (hπ.lt i (by omega)))
      set F := (Finset.range 3).filter (fun r' => st g r' ∉ s.queue) with hFdef
      have hrF : r ∉ F := by
        simp only [hFdef, Finset.mem_filter, not_and, not_not]
        intro _; rw [hgr, hq]; exact List.mem_cons_self
      -- two other blows sum to less than `T`: `E_g` is alive
      have hFsub : F ⊆ (Finset.range 3).erase r := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun e => hrF (e ▸ hx), (Finset.mem_filter.mp hx).1⟩
      have hFc : F.card ≤ 2 := by
        have := Finset.card_le_card hFsub
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hr)] at this; simpa using this
      have hsumF : ∑ r' ∈ F, a.getD (π (st g r')) 0 < T := by
        have h2 : ∀ r' ∈ F, 2 * a.getD (π (st g r')) 0 + 1 ≤ T := by
          intro r' hr'
          have hr3 : r' < 3 := Finset.mem_range.mp (Finset.mem_filter.mp hr').1
          have := (hbd _ (ThreeP.getD_mem (hπ.lt _ (hst.lt g hg r' hr3)))).2
          omega
        have hs := Finset.sum_le_sum h2
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.sum_const, smul_eq_mul] at hs
        have : F.card * T ≤ 2 * T := Nat.mul_le_mul_right T hFc
        have h0 : F.card = 0 → ∑ r' ∈ F, a.getD (π (st g r')) 0 = 0 := fun h => by
          rw [Finset.card_eq_zero.mp h, Finset.sum_empty]
        generalize F.card * T = P at hs this
        by_cases hk : F.card = 0
        · rw [h0 hk]; omega
        · omega
      have hepool := hw.epool g hg
      rw [← hFdef] at hepool
      have hta : (s.units ((GF a T).k + g)).alive := by unfold Stack.alive; rw [hepool]; omega
      have htN : (GF a T).k + g < (GF a T).N := by rw [N_eq, hK]; omega
      have hts : (s.units ((GF a T).k + g)).side = .enemy := by
        rw [hf.side, init_enemy_GF hg]
      -- the seat is free: only `st g r = i` is ever sent there
      have hfree : free (GF a T) s.units i (seat g r) := by
        refine free_of (inBounds_seat hg hr) ?_
        intro i' hi' hne _ e
        by_cases hik : i' < (GF a T).k
        · by_cases hiq : i' ∈ s.queue
          · rw [hex_of_Q hreach (by omega) (by simp [State.Q, hiq])] at e
            rcases seat_y g hr with hy | hy <;> rw [← e] at hy <;> simp [phex] at hy
          · obtain ⟨g', hg', r', hr', hgr'⟩ := hst.cover i' (by omega)
            rw [← hgr', hw.seated g' hg' r' hr' (by rw [hgr']; exact hiq)] at e
            obtain ⟨rfl, rfl⟩ := seat_inj hr' hr e
            exact hne (by rw [← hgr', ← hgr])
        · obtain ⟨g', hg', rfl⟩ : ∃ g' < a.length / 3, i' = (GF a T).k + g' :=
            ⟨i' - (GF a T).k, by rw [N_eq] at hi'; omega, by omega⟩
          rw [hex_enemy hreach hg'] at e
          exact seat_ne_ehex g r g' hr e.symm
      have hC := (clear_of_AO hw.reach).1
      have hd : seat g r ∈ reachOf (GF a T) s.units i :=
        route hC (by omega) (hex_of_Q hreach (by omega) hiQ)
          (by rw [hty]; rfl) hg hr hfree
      have hadj : Hex.Adj (seat g r) (s.units ((GF a T).k + g)).hex := by
        rw [hex_enemy hreach hg]; exact seat_adj g hr
      have hmemAO : ({ s with units := resolveAttack s.units i ((GF a T).k + g) (seat g r), queue := q } : State) ∈ succsAO (GF a T) s :=
        attack_mem_succsAO hq ha hside hd htN hta hts hadj
      have hstep := step_of_mem_succsAO hmemAO
      refine ⟨_, hmemAO, ?_, rfl⟩
      have hit : i ≠ (GF a T).k + g := by omega
      have hb : blow { activate (s.units i) with hex := seat g r }
          (s.units ((GF a T).k + g)) = ai := by
        have := Prop11.blow_eq (C := famPlayer (4 * (a.length / 3) + 8) ai) (c := 1)
          (a := { activate (s.units i) with hex := seat g r })
          (tg := s.units ((GF a T).k + g))
          (by simp only [activate]; exact hty) (by simp [famPlayer]; exact hai.1)
          (by simp [famPlayer]) (by simp only [activate]; rw [hpool]; rfl) le_rfl
          (by
            unfold Stack.defEff
            rw [hw.edef g hg, hf.type, init_enemy_GF hg]; simp [famEnemy, famPlayer])
        rw [this, one_mul]; rfl
      refine ⟨hw.reach.tail hmemAO, hw.phase, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx; rw [hstep.side]; exact hw.bucket x hx
      · intro j hj hjq
        obtain ⟨hjq', hji⟩ := (hmem j).mp hjq
        simp only
        rw [resolveAttack_of_ne hji (by omega)]
        exact hw.fresh j hj hjq'
      · intro g' hg' r' hr' hq'
        simp only at hq' ⊢
        by_cases hei : st g' r' = i
        · obtain ⟨rfl, rfl⟩ := hst.inj g' hg' r' hr' g hg r hr (hei.trans hgr.symm)
          rw [hei, resolveAttack_self_hex hit]
        · rw [resolveAttack_hex_of_ne hei]
          exact hw.seated g' hg' r' hr' (fun h => hq' ((hmem _).mpr ⟨h, hei⟩))
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
          have hF' : (Finset.range 3).filter (fun r' => st g' r' ∉ q) = insert r F := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range, hFdef]
            rw [hmem]
            constructor
            · rintro ⟨hx, h⟩
              by_cases hxr : x = r
              · exact Or.inl hxr
              · refine Or.inr ⟨hx, fun h' => h ⟨h', fun e => hxr ?_⟩⟩
                exact (hst.inj g' hg' x hx g' hg' r hr (e.trans hgr.symm)).2
            · rintro (rfl | ⟨hx, h⟩)
              · exact ⟨hr, fun ⟨_, h2⟩ => h2 hgr⟩
              · exact ⟨hx, fun ⟨h1, _⟩ => h h1⟩
          rw [hF', Finset.sum_insert hrF, Nat.sub_sub, hgr, add_comm]
        · rw [resolveAttack_of_ne (by omega) (by omega), hw.epool g' hg',
            hfilt_ne g' (fun x hx e => hgg (hst.inj g' hg' x hx g hg r hr (e.trans hgr.symm)).1)]
    · -- an enemy stack: `(‡)` makes it `WAIT`
      have hmemAO : ({ s with units := update s.units i (activate (s.units i)), queue := q, bucket := s.bucket ++ [i] } : State) ∈ succsAO (GF a T) s :=
        wait_mem_succsAO hw.phase hq ha hside (I := GF a T)
      have hstep := step_of_mem_succsAO hmemAO
      refine ⟨_, hmemAO, ?_, rfl⟩
      have hik : ∀ j < (GF a T).k, j ≠ i := by
        intro j hj e; subst e
        rw [hf.side, initUnits_side_of_lt hj] at hside; cases hside
      have hsti : ∀ g' < a.length / 3, ∀ x < 3, st g' x ≠ i :=
        fun g' hg' x hx => hik _ (by rw [hK]; exact hst.lt g' hg' x hx)
      refine ⟨hw.reach.tail hmemAO, hw.phase, ?_, ?_, ?_, ?_, ?_⟩
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
      · intro g' hg' r' hr' hq'
        simp only at hq' ⊢
        rw [update_of_ne (hsti g' hg' r' hr')]
        exact hw.seated g' hg' r' hr' (fun h => hq' ((hmem _).mpr ⟨h, hsti g' hg' r' hr'⟩))
      · intro g' hg'
        simp only [update_apply]
        split_ifs with he
        · simp [activate]
        · exact hw.edef g' hg'
      · intro g' hg'
        simp only
        rw [hfilt_ne g' (hsti g' hg'), ← hw.epool g' hg', update_apply]
        split_ifs with he
        · rw [he]; simp [activate]
        · rfl
  · -- a dead stack is skipped; it cannot be a player slot (those are fresh)
    have hmemAO : ({ s with queue := q } : State) ∈ succsAO (GF a T) s :=
      skip_mem_succsAO hq ha (I := GF a T)
    have hik : ∀ j < (GF a T).k, j ≠ i := by
      intro j hj e; subst e
      exact ha (by unfold Stack.alive; rw [hw.fresh j hj (by rw [hq]; exact List.mem_cons_self)]; norm_num)
    have hsti : ∀ g' < a.length / 3, ∀ x < 3, st g' x ≠ i :=
      fun g' hg' x hx => hik _ (by rw [hK]; exact hst.lt g' hg' x hx)
    refine ⟨_, hmemAO, ⟨hw.reach.tail hmemAO, hw.phase, hw.bucket, ?_, ?_, hw.edef, ?_⟩, rfl⟩
    · intro j hj hjq; exact hw.fresh j hj ((hmem j).mp hjq).1
    · intro g' hg' r' hr' hq'
      exact hw.seated g' hg' r' hr' (fun h => hq' ((hmem _).mpr ⟨h, hsti g' hg' r' hr'⟩))
    · intro g' hg'
      simp only
      rw [hfilt_ne g' (hsti g' hg')]; exact hw.epool g' hg'

theorem WF.run (hT : 1 ≤ T) (hbd : ∀ x ∈ a, 1 ≤ x ∧ 2 * x < T) (hπ : Inj a π)
    (hst : Seating (a.length / 3) st) :
    ∀ (L : List ℕ) (s : State), WF a T π st s → s.queue = L →
      ∃ s', Relation.ReflTransGen (fun s s' => s' ∈ succsAO (GF a T) s) s s' ∧
        WF a T π st s' ∧ s'.queue = []
  | [], s, hw, hq => ⟨s, .refl, hw, hq⟩
  | i :: q, s, hw, hq => by
    obtain ⟨s1, h1, hw1, hq1⟩ := hw.step hT hbd hπ hst hq
    obtain ⟨s2, h2, hw2, hq2⟩ := WF.run hT hbd hπ hst q s1 hw1 hq1
    exact ⟨s2, Relation.ReflTransGen.head h1 h2, hw2, hq2⟩

/-- **Lemma E.19 (simultaneous realizability).** For every full allocation (`π` an injection
of the `3m` slots into the types) and every three-per-enemy seating `st`, there is a complete
attack-only play of round 1 in which stack `st g r` ends on `q_g^{r+1}` and each `E_g` has lost
exactly the blows of its three assigned stacks.  It uses only `a_i ≥ 1` and `2 a_i < T`. -/
theorem lemmaE19 (hT : 1 ≤ T) (hbd : ∀ x ∈ a, 1 ≤ x ∧ 2 * x < T) (hπ : Inj a π)
    (hst : Seating (a.length / 3) st) :
    ∃ s, AOReach (GF a T) (απ π) s ∧ Done s ∧
      (∀ g < a.length / 3, ∀ r < 3, (s.units (st g r)).hex = seat g r) ∧
      ∀ g < a.length / 3, (s.units ((GF a T).k + g)).pool =
        T - ∑ r ∈ Finset.range 3, a.getD (π (st g r)) 0 := by
  obtain ⟨s1, h1, hw1, hq1⟩ := WF.run hT hbd hπ hst _ _ (WF.init hπ hst) rfl
  obtain ⟨s2, h2, hd2⟩ := exists_doneAO (GF a T) s1
  have hz : Frozen s1 := by
    refine ⟨(lemmaE1 rfl (AOReach.reach hw1.reach)).1, Or.inl ⟨hw1.phase, hq1, hw1.bucket⟩⟩
  have hfr := hz.run (rtg_step_of_AO h2)
  refine ⟨s2, hw1.reach.trans h2, hd2, fun g hg r hr => ?_, fun g hg => ?_⟩
  · rw [(hfr _).2]; exact hw1.seated g hg r hr (by rw [hq1]; exact List.not_mem_nil)
  · rw [(hfr _).1, hw1.epool g hg, hq1]
    simp

/-! ## Lemmas E.21, E.22 and Theorem 4 -/

/-- The seating of a 3-partition: `pick S g r`, the `r`-th element of triple `g`. -/
theorem seating_of_parts {S : ℕ → Finset ℕ} (hS : ThreeP.Parts a T S) :
    Seating (a.length / 3) (ThreeP.pick S) :=
  ⟨fun g hg r hr => by have := hS.pick_lt hg hr; have := hS.len; omega,
   fun g hg r hr g' hg' r' hr' h => hS.pick_inj hg hg' hr hr' h,
   fun j hj => hS.pick_cover (by have := hS.len; omega)⟩

theorem bd_of_promise (hP : Promise3P a T) : ∀ x ∈ a, 1 ≤ x ∧ 2 * x < T :=
  fun x hx => ⟨by have := (hP.2.2 x hx).1; omega, (hP.2.2 x hx).2⟩

/-- **Lemma E.21 (`3-PARTITION` yes ⟹ game yes)**, with the allocation `C_i ↦ slot i`: a
complete play destroying every enemy. -/
theorem lemmaE21 (hP : Promise3P a T) (h3 : THREE_PARTITION a T) :
    ∃ s, Reach (GF a T) αId s ∧ Done s ∧
      ∀ g < a.length / 3, (s.units ((GF a T).k + g)).pool = 0 := by
  obtain ⟨S, hS⟩ := ThreeP.parts_of h3
  by_cases hm0 : a.length / 3 = 0
  · obtain ⟨s, hs, hd⟩ := exists_done (GF a T) (initState (GF a T) αId)
    exact ⟨s, hs, hd, fun g hg => by omega⟩
  have hT : 1 ≤ T := by
    have := (hP.2.2 _ (ThreeP.getD_mem (a := a) (i := 0) (by omega))).2; omega
  obtain ⟨s, hs, hd, -, hpool⟩ := lemmaE19 (π := id) hT (bd_of_promise hP) Inj.id
    (seating_of_parts hS)
  refine ⟨s, AOReach.reach hs, hd, fun g hg => ?_⟩
  rw [hpool g hg]
  simp only [id]
  rw [hS.sum_pick_T hg, Nat.sub_self]

theorem αId_feasible (hP : Promise3P a T) : Feasible (GF a T) αId := απ_feasible Inj.id

theorem destroyed_all (hP : Promise3P a T) {s : State} (hs : Reach (GF a T) αId s)
    (h0 : ∀ g < a.length / 3, (s.units ((GF a T).k + g)).pool = 0) :
    (GF a T).W ≤ destroyed (GF a T) s := by
  by_cases hm0 : a.length / 3 = 0
  · rw [W_eq, hm0]; exact Nat.zero_le _
  have hT : 1 ≤ T := by
    have := (hP.2.2 _ (ThreeP.getD_mem (a := a) (i := 0) (by omega))).2; omega
  unfold GF at hs ⊢
  rw [Fam.destroyed_eq hT (Reach.frame hs)]
  simp only [ehex_len, slots_len, Fam.W_eq]
  have : ∀ g ∈ Finset.range (a.length / 3),
      (if (s.units (3 * (a.length / 3) + g)).pool = 0 then 1 else 0) = 1 := by
    intro g hg
    have := h0 g (Finset.mem_range.mp hg)
    rw [k_eq] at this
    simp [this]
  rw [Finset.sum_congr rfl this]
  simp

/-- **Lemma E.22 (game yes ⟹ `3-PARTITION` yes)**: geometry-free (`Fam.fam_no`). -/
theorem lemmaE22 (hP : Promise3P a T) (h : ArmyAllocation (GF a T)) : THREE_PARTITION a T :=
  Fam.fam_no hP (by simp [layout]) h

/-- **Theorem 4.** On the promise of `3-PARTITION`, `(a, T)` is a yes-instance iff `G_F(a, T)`
is a yes-instance of `ARMY-ALLOCATION`. -/
theorem theorem4 (a : List ℕ) (T : ℕ) (hP : Promise3P a T) :
    THREE_PARTITION a T ↔ ArmyAllocation (GF a T) := by
  refine ⟨fun h3 => ?_, lemmaE22 hP⟩
  obtain ⟨s, hs, hd, h0⟩ := lemmaE21 hP h3
  exact ⟨αId, αId_feasible hP, s, hs, hd, destroyed_all hP hs h0⟩

/-! ## Corollary 4.1: the allocation given -/

/-- **`BATTLE-PLAY`**: with the allocation `α` given, some play destroys value at least `W`. -/
def BattlePlay (I : Instance) (α : ℕ → SlotAlloc) : Prop :=
  ∃ s, Reach I α s ∧ Done s ∧ I.W ≤ destroyed I s

/-- **Corollary 4.1**: with the allocation `C_i ↦ slot i` fixed, targeting alone is hard. -/
theorem cor41 (a : List ℕ) (T : ℕ) (hP : Promise3P a T) :
    THREE_PARTITION a T ↔ BattlePlay (GF a T) αId := by
  constructor
  · intro h3
    obtain ⟨s, hs, hd, h0⟩ := lemmaE21 hP h3
    exact ⟨s, hs, hd, destroyed_all hP hs h0⟩
  · rintro ⟨s, hs, hd, hW⟩
    exact lemmaE22 hP ⟨αId, αId_feasible hP, s, hs, hd, hW⟩

/-! ## Corollary 4.2: the hit-point objective -/

/-- Enemy hit points removed: `Σ_E (initial pool − final pool)`, i.e. `Σ_E min(delivered, pool)`
(R8, overkill discarded; `Ledger.absorbed`). -/
def absorbed (I : Instance) (s : State) : ℕ :=
  ∑ g ∈ Finset.range I.n, ((I.enemy g).count * (I.enemy g).type.hp - (s.units (I.k + g)).pool)

/-- `ARMY-ALLOCATION` with the hit-point objective and target `W_hp`. -/
def HpAllocation (I : Instance) (Whp : ℕ) : Prop :=
  ∃ α, Feasible I α ∧ ∃ s, Reach I α s ∧ Done s ∧ Whp ≤ absorbed I s

/-- `BATTLE-PLAY` with the hit-point objective. -/
def HpPlay (I : Instance) (α : ℕ → SlotAlloc) (Whp : ℕ) : Prop :=
  ∃ s, Reach I α s ∧ Done s ∧ Whp ≤ absorbed I s

/-- The no-direction of Corollary 4.2, on every layout: removing `mT` hit points forces a
3-partition. -/
theorem Fam.hp_no {L : Layout} (hP : Promise3P a T) (hm : L.ehex.length = a.length / 3)
    {α : ℕ → SlotAlloc} (hα : Feasible (famInst L a T) α) {s : State}
    (hs : Reach (famInst L a T) α s) (hW : a.length / 3 * T ≤ absorbed (famInst L a T) s) :
    THREE_PARTITION a T := by
  by_cases hm0 : L.ehex.length = 0
  · have hlen : a.length = 0 := by have := hP.1; omega
    exact ⟨hP.1, fun _ => ∅, fun g hg => by omega, fun g hg => by omega, fun i hi => by omega⟩
  have hT : 1 ≤ T := by
    have := (hP.2.2 _ (ThreeP.getD_mem (a := a) (i := 0) (by omega))).2; omega
  have ha : ∀ x ∈ a, 1 ≤ x := fun x hx => by have := (hP.2.2 x hx).1; omega
  obtain ⟨τ, β, hL⟩ := ledger (Fam.acctHyp (L := L) hT ha) hα (P := fun _ _ => True)
    (fun _ _ _ _ _ _ _ _ => trivial) hs
  have hterm : ∀ g < L.ehex.length, (famInst L a T).enemy g = ⟨famEnemy T, 1, L.ehex.getD g ⟨0, 0⟩⟩ :=
    fun g hg => Fam.enemy_eq hg
  -- every term is at most `T`, and they sum to at least `mT`: each is exactly `T`
  have hle : ∀ g ∈ Finset.range L.ehex.length,
      (1 * T - (s.units (L.slots.length + g)).pool) ≤ T := fun g _ => by omega
  have hsum : ∑ g ∈ Finset.range L.ehex.length, (1 * T - (s.units (L.slots.length + g)).pool) =
      ∑ g ∈ Finset.range L.ehex.length, T := by
    apply le_antisymm (Finset.sum_le_sum hle)
    have : absorbed (famInst L a T) s =
        ∑ g ∈ Finset.range L.ehex.length, (1 * T - (s.units (L.slots.length + g)).pool) := by
      unfold absorbed
      simp only [Fam.n_eq, Fam.k_eq]
      apply Finset.sum_congr rfl
      intro g hg; rw [hterm g (Finset.mem_range.mp hg)]; rfl
    rw [this, ← hm] at hW
    simpa [mul_comm] using hW
  refine Fam.three_partition_of_ledger hP hα hm hL (fun g hg => ?_)
  have hg' : g < (famInst L a T).n := by simpa using hg
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsum g (Finset.mem_range.mpr hg)
  have habs := hL.absorbed hg'
  rw [hterm g hg] at habs
  simp only [Fam.k_eq] at habs heq
  have h1 : T ≤ ∑ j ∈ strikers (famInst L a T) τ g, β j := by
    simp only [famEnemy] at habs; omega
  exact h1.trans (Finset.sum_le_sum (fun j _ => hL.blow j))

theorem absorbed_all {s : State}
    (h0 : ∀ g < a.length / 3, (s.units ((GF a T).k + g)).pool = 0) :
    a.length / 3 * T ≤ absorbed (GF a T) s := by
  unfold absorbed
  rw [n_eq]
  have : ∀ g ∈ Finset.range (a.length / 3),
      ((GF a T).enemy g).count * ((GF a T).enemy g).type.hp - (s.units ((GF a T).k + g)).pool
        = T := by
    intro g hg
    rw [enemy_eq' (Finset.mem_range.mp hg), h0 g (Finset.mem_range.mp hg)]
    simp [famEnemy]
  rw [Finset.sum_congr rfl this]
  simp

/-- **Corollary 4.2 (hit-point objective)**, allocation free and allocation given: on the
promise, `(a, T)` is a yes-instance iff some (resp. the given) allocation admits a play
removing `W_hp = mT` enemy hit points. -/
theorem cor42 (a : List ℕ) (T : ℕ) (hP : Promise3P a T) :
    (THREE_PARTITION a T ↔ HpAllocation (GF a T) (a.length / 3 * T)) ∧
    (THREE_PARTITION a T ↔ HpPlay (GF a T) αId (a.length / 3 * T)) := by
  have yes : THREE_PARTITION a T → HpPlay (GF a T) αId (a.length / 3 * T) := by
    intro h3
    obtain ⟨s, hs, hd, h0⟩ := lemmaE21 hP h3
    exact ⟨s, hs, hd, absorbed_all h0⟩
  have no : HpAllocation (GF a T) (a.length / 3 * T) → THREE_PARTITION a T := by
    rintro ⟨α, hα, s, hs, -, hW⟩
    exact Fam.hp_no (L := layout (a.length / 3)) hP (by simp [layout]) hα hs hW
  refine ⟨⟨fun h3 => ?_, no⟩, ⟨yes, fun h => no ?_⟩⟩
  · obtain ⟨s, hs, hd, hW⟩ := yes h3
    exact ⟨αId, αId_feasible hP, s, hs, hd, hW⟩
  · obtain ⟨s, hs, hd, hW⟩ := h
    exact ⟨αId, αId_feasible hP, s, hs, hd, hW⟩

end ThmF

/-! ## Totality -/

/-- **Theorem 4, total form** ("the totality branch is that of the Theorem 2 section
verbatim, with `G_F((1,1,1), 3)` as the fixed yes-instance"). -/
theorem theorem4_total (a : List ℤ) (T : ℤ) :
    THREE_PARTITIONℤ a T ↔ ArmyAllocation (reduction3P GF a T) :=
  reduction3P_iff GF ThmF.theorem4 a T

/-- The fixed allocation for `G_no` (one creature of the one type in the one slot). -/
def αGno : ℕ → SlotAlloc := fun _ => ⟨0, 1⟩

theorem αGno_feasible : Feasible Corridor.Gno αGno := by
  refine ⟨fun j hj _ => by simp [αGno, Corridor.Gno], fun t ht => ?_⟩
  have : t = 0 := by simpa [Corridor.Gno] using ht
  subst this
  simp [αGno, Corridor.Gno, Instance.k]

/-- The total reduction of Corollary 4.1: an instance together with its given allocation. -/
def reduction41 (a : List ℤ) (T : ℤ) : Instance × (ℕ → SlotAlloc) :=
  if InDomain3P a T then
    (if a = [] then (GF [1, 1, 1] 3, ThmF.αId) else (GF (a.map Int.toNat) T.toNat, ThmF.αId))
  else (Corridor.Gno, αGno)

/-- **Corollary 4.1, total form.** -/
theorem cor41_total (a : List ℤ) (T : ℤ) :
    THREE_PARTITIONℤ a T ↔ ThmF.BattlePlay (reduction41 a T).1 (reduction41 a T).2 := by
  unfold reduction41
  split_ifs with hd hnil
  · subst hnil
    exact ⟨fun _ => (ThmF.cor41 _ _ ThreeP.promise_111).mp ThreeP.yes_111,
      fun _ => ThreeP.nil_iff T⟩
  · rw [ThreeP.toNat_iff hd]; exact ThmF.cor41 _ _ (ThreeP.promise_toNat hd hnil)
  · refine ⟨fun h => absurd h.1 hd, fun ⟨s, hs, hdn, hW⟩ => absurd ?_ Corridor.Gno_no⟩
    exact ⟨αGno, αGno_feasible, s, hs, hdn, hW⟩

/-- The total reduction of Corollary 4.2: an instance together with its target `W_hp`. -/
def reduction42 (a : List ℤ) (T : ℤ) : Instance × ℕ :=
  if InDomain3P a T then
    (if a = [] then (GF [1, 1, 1] 3, 3)
     else (GF (a.map Int.toNat) T.toNat, a.length / 3 * T.toNat))
  else (Corridor.Gno, 1)

theorem absorbed_Gno (s : State) : ThmF.absorbed Corridor.Gno s = 0 := by
  simp [ThmF.absorbed, Instance.n, Corridor.Gno]

/-- **Corollary 4.2, total form** (allocation free). -/
theorem cor42_total (a : List ℤ) (T : ℤ) :
    THREE_PARTITIONℤ a T ↔ ThmF.HpAllocation (reduction42 a T).1 (reduction42 a T).2 := by
  unfold reduction42
  split_ifs with hd hnil
  · subst hnil
    exact ⟨fun _ => (ThmF.cor42 _ _ ThreeP.promise_111).1.mp ThreeP.yes_111,
      fun _ => ThreeP.nil_iff T⟩
  · rw [ThreeP.toNat_iff hd]
    have := (ThmF.cor42 _ _ (ThreeP.promise_toNat hd hnil)).1
    simpa using this
  · refine ⟨fun h => absurd h.1 hd, fun ⟨α, _, s, _, _, hW⟩ => ?_⟩
    rw [absorbed_Gno] at hW; omega

end Homm3
