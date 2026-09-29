import Homm3.BattleFacts
import Homm3.Corridor
import Homm3.Knapsack

/-!
# Stage 4c. The corridor family as a game

The Theorem 1 / Proposition 1.1 family, parametrized as in Proposition 1.1: `n` blocks,
enemy `j` a single creature of `t j` hit points and value `v j`, one player type of flat
damage `d`, stock `B`, target `W`.  Everything else is `G(a)` verbatim (paper Appendix E,
"The instance `G(a)`"): one row of `5n` hexes, no obstacles, `p j = 5j`, `e j = 5j + 1`,
player `att = def = 1, hp = 5, spd = 2, value = 0`; enemy `att = def = 1`, flat damage 1,
`spd = 1`; `R = 1`.  `G(a)` itself is `inst n a a 1 B B`.
-/

namespace Homm3.Corridor

open Function

def playerType (d : ℕ) : CType := ⟨1, 1, d, 5, 2, 0⟩
def enemyType (t v : ℕ) : CType := ⟨1, 1, 1, t, 1, v⟩

def inst (n : ℕ) (t v : ℕ → ℕ) (d B W : ℕ) : Instance where
  width := 5 * n
  height := 1
  obstacles := ∅
  slots := (List.range n).map p
  army := [(playerType d, B)]
  enemies := (List.range n).map (fun j => ⟨enemyType (t j) (v j), 1, e j⟩)
  R := 1
  W := W

variable {n : ℕ} {t v : ℕ → ℕ} {d B W : ℕ}

@[simp] theorem inst_k : (inst n t v d B W).k = n := by simp [inst, Instance.k]
@[simp] theorem inst_n : (inst n t v d B W).n = n := by simp [inst, Instance.n]
@[simp] theorem inst_N : (inst n t v d B W).N = n + n := by simp [Instance.N]
@[simp] theorem inst_R : (inst n t v d B W).R = 1 := rfl

/-- The player type actually deployed in slot `j`: the army has one entry, index `0`. -/
def slotType (d : ℕ) (α : ℕ → SlotAlloc) (j : ℕ) : CType :=
  if 0 < (α j).count ∧ (α j).type = 0 then playerType d else default

theorem slotType_of {α : ℕ → SlotAlloc} {j : ℕ} (hc : 0 < (α j).count) (h0 : (α j).type = 0) :
    slotType d α j = playerType d := by
  simp [slotType, hc, h0]

/-- The initial pool of a slot whose type index is `0`: `5 · count` (also when empty). -/
theorem pool_slotType {α : ℕ → SlotAlloc} {j : ℕ} (h0 : (α j).type = 0) :
    (α j).count * (slotType d α j).hp = (α j).count * 5 := by
  by_cases hc : 0 < (α j).count
  · rw [slotType_of hc h0]; rfl
  · have : (α j).count = 0 := by omega
    simp [this]

theorem init_player (α : ℕ → SlotAlloc) {j : ℕ} (hj : j < n) :
    initUnits (inst n t v d B W) α j =
      ⟨.player, j, slotType d α j, p j, (α j).count * (slotType d α j).hp, (α j).count, 1,
        false⟩ := by
  unfold initUnits slotType
  rw [if_pos (by simpa using hj)]
  have hget : ∀ x, ((inst n t v d B W).army.getD x default).1 =
      if x = 0 then playerType d else default := by
    intro x; rcases x with _ | x <;> simp [inst]; rfl
  simp only [hget]
  by_cases hc : 0 < (α j).count <;> by_cases h0 : (α j).type = 0 <;>
    simp [inst, h0, hj, hc]

theorem init_enemy (α : ℕ → SlotAlloc) {j : ℕ} (hj : j < n) :
    initUnits (inst n t v d B W) α (n + j) =
      ⟨.enemy, j, enemyType (t j) (v j), e j, t j, 1, 1, false⟩ := by
  unfold initUnits
  simp only [inst_k, inst_N, Nat.add_sub_cancel_left]
  rw [if_neg (by omega), if_pos (by omega)]
  simp [inst, hj, enemyType]

theorem init_side_player {α : ℕ → SlotAlloc} {i : ℕ}
    (h : (initUnits (inst n t v d B W) α i).side = .player) : i < n := by
  by_contra hi
  unfold initUnits at h
  rw [if_neg (by simpa using hi)] at h
  split_ifs at h <;> cases h

/-- Enemy ids are exactly `n + j`, `j < n`. -/
theorem enemy_id {α : ℕ → SlotAlloc} {i : ℕ} (hi : i < n + n)
    (h : (initUnits (inst n t v d B W) α i).side = .enemy) : ∃ j < n, i = n + j := by
  by_cases hin : i < n
  · rw [init_player α hin] at h; cases h
  · exact ⟨i - n, by omega, by omega⟩

/-! ## Value destroyed -/

/-- The static data and the pool bound every reachable state keeps (from `Step.St` and
`Step.pool_le`). -/
structure Frame (α : ℕ → SlotAlloc) (s : State) : Prop where
  St : ∀ i, (s.units i).St = (initUnits (inst n t v d B W) α i).St
  pool : ∀ i, (s.units i).pool ≤ (initUnits (inst n t v d B W) α i).pool

theorem Frame.init (α : ℕ → SlotAlloc) :
    Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α (initState (inst n t v d B W) α) :=
  ⟨fun _ => rfl, fun _ => le_rfl⟩

theorem Frame.step {α : ℕ → SlotAlloc} {s s' : State} (hf : Frame (n := n) (t := t) (v := v)
    (d := d) (B := B) (W := W) α s) (h : Step (inst n t v d B W) s s') :
    Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s' :=
  ⟨fun i => (h.St i).trans (hf.St i), fun i => (h.pool_le i).trans (hf.pool i)⟩

theorem Frame.side {α : ℕ → SlotAlloc} {s : State}
    (hf : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s) (i : ℕ) :
    (s.units i).side = (initUnits (inst n t v d B W) α i).side :=
  congrArg Prod.fst (hf.St i)

theorem Frame.type {α : ℕ → SlotAlloc} {s : State}
    (hf : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s) (i : ℕ) :
    (s.units i).type = (initUnits (inst n t v d B W) α i).type :=
  congrArg (fun x => x.2.2.1) (hf.St i)

theorem Frame.initc {α : ℕ → SlotAlloc} {s : State}
    (hf : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s) (i : ℕ) :
    (s.units i).init = (initUnits (inst n t v d B W) α i).init :=
  congrArg (fun x => x.2.2.2) (hf.St i)

/-- A single-creature enemy of `t ≥ 1` hit points with pool `≤ t` counts `1` iff alive. -/
theorem count_single {u : Stack} {tj : ℕ} (ht : 1 ≤ tj) (hty : u.type.hp = tj)
    (hp : u.pool ≤ tj) : u.count = if u.pool = 0 then 0 else 1 := by
  unfold Stack.count; rw [hty]
  split_ifs with h
  · rw [h, zero_add]; exact Nat.div_eq_of_lt (by omega)
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- **Value destroyed in the corridor**: exactly the values of the enemies whose pool is
empty. -/
theorem destroyed_eq {α : ℕ → SlotAlloc} {s : State} (ht : ∀ j < n, 1 ≤ t j)
    (hf : Frame (n := n) (t := t) (v := v) (d := d) (B := B) (W := W) α s) :
    destroyed (inst n t v d B W) s =
      ∑ j ∈ Finset.range n, if (s.units (n + j)).pool = 0 then v j else 0 := by
  unfold destroyed
  rw [inst_N, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range n, (if (s.units x).side = .enemy then
      ((s.units x).init - (s.units x).count) * (s.units x).type.value else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hf.side, init_player α (Finset.mem_range.mp hj)]
    simp
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hj := Finset.mem_range.mp hj
  have hty := hf.type (n + j)
  have hin := hf.initc (n + j)
  have hpl := hf.pool (n + j)
  rw [init_enemy α hj] at hty hin hpl
  rw [hf.side, init_enemy α hj, hin, hty,
    count_single (ht j hj) (by rw [hty]; rfl) hpl]
  simp only [↓reduceIte, enemyType]
  split_ifs <;> simp

end Homm3.Corridor
