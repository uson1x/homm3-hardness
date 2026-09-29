import Homm3.Hex
import Homm3.Damage

/-!
# Stage 4a. Instances, allocations and the round semantics of `H3-det-melee` against `(‡)`

Source of truth: `homm3/MODEL.md` §§3, 5, 6, 9; `homm3/paper/main.md` §2.2–2.4;
`homm3/scripts/homm3_model.py` (`Stack`, `compute_damage`, `Battle.reachable`,
`resolve_attack`, `turn_order`, `wait_phase_order`, `activate`, `act_wait`, `act_defend`,
`end_round`) and `brute_force.policy_wait_defend`.

## What is modelled

* Fragment `H3-det-melee` (MODEL.md Def. 7.1a): every creature is melee, single-hex,
  `flags = ∅`, flat damage, one retaliation charge per round.  So the creature tuple is
  `(att, def, dmg, hp, spd, value)`.
* Health is the pool `avail` (R5) and `count = ⌈avail / hp⌉` (R6).  Under the engine's
  invariant `firstHPleft ∈ (0, hp]` this is `fullUnits + [firstHPleft > 0]`; damage is
  `avail ← avail − D` truncated at `0` (R8, overkill discarded).
* Scheduling (R9): at the start of a round, every living stack is queued in `NORMAL` order
  (speed descending, then side — player first — then slot); stacks that `WAIT` go to a
  bucket, which after the `NORMAL` phase is replayed in `WAIT` order (speed ascending, then
  side, then slot).  Dead stacks are skipped when they come up.  Each activation clears the
  `DEFEND` bonus (STACK_GETS_TURN).
* Player actions (nondeterministic, R11, R13): `WAIT` (`NORMAL` phase only), `DEFEND`,
  move to a hex of the BFS reach, `WALK_AND_ATTACK` = move to a hex `h` of the BFS reach
  adjacent to a living enemy, then strike; the target retaliates (R12) if still alive, the
  attacker is alive, and it has a charge.
* Defence: the fixed policy `(‡)` — `WAIT` at the `NORMAL` activation, `DEFEND` at the
  postponed one.
* Rounds: `R` rounds; at the boundary retaliation charges reset to `1` and the `DEFEND`
  flag persists (it expires at the stack's next activation).  The model assumes `R ≥ 1`
  (with `R = 0` it would still play one round); all theorems use `R = 1`.

The semantics is a *relation* (`Step`), so "a sequence of player actions" is a path of
`Step`s; the defence's steps are forced.
-/

namespace Homm3

inductive Side | player | enemy
  deriving DecidableEq, Repr

/-- A creature type of `H3-det-melee`: `(att, def, dmg_min = dmg_max, hp, spd)` + value. -/
structure CType where
  att : ℕ
  dfn : ℕ
  dmg : ℕ
  hp : ℕ
  spd : ℕ
  value : ℕ
  deriving DecidableEq, Repr

instance : Inhabited CType := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- An enemy stack of the fixed defence. -/
structure EnemySpec where
  type : CType
  count : ℕ
  hex : Hex

/-- An `ARMY-ALLOCATION` instance (paper §2.3). -/
structure Instance where
  width : ℕ
  height : ℕ
  obstacles : Finset Hex
  /-- deployment hexes `p_0, …, p_{k−1}` -/
  slots : List Hex
  /-- the multiset `A`, as (type, stock) pairs -/
  army : List (CType × ℕ)
  enemies : List EnemySpec
  R : ℕ
  W : ℕ

namespace Instance
variable (I : Instance)
def k : ℕ := I.slots.length
def n : ℕ := I.enemies.length
/-- Stack ids: `0 … k−1` are the player slots, `k … k+n−1` the enemy stacks. -/
def N : ℕ := I.k + I.n
def inBounds (h : Hex) : Prop := 0 ≤ h.x ∧ h.x < I.width ∧ 0 ≤ h.y ∧ h.y < I.height
end Instance

/-- What slot `j` receives: `count` creatures of army entry `type` (`count = 0`: empty). -/
structure SlotAlloc where
  type : ℕ
  count : ℕ

/-- Feasibility: a nonempty slot names an existing army entry (so it holds one type), and
each entry's total over the slots is at most its stock. -/
def Feasible (I : Instance) (α : ℕ → SlotAlloc) : Prop :=
  (∀ j < I.k, 0 < (α j).count → (α j).type < I.army.length) ∧
  ∀ t < I.army.length,
    ∑ j ∈ (Finset.range I.k).filter (fun j => (α j).type = t), (α j).count
      ≤ (I.army.getD t default).2

/-- A stack on the board (MODEL.md Def. 3.2). -/
structure Stack where
  side : Side
  slot : ℕ
  type : CType
  hex : Hex
  /-- remaining health pool `avail` (R5) -/
  pool : ℕ
  /-- creature count at the start of the battle -/
  init : ℕ
  /-- retaliation charges left this round -/
  retal : ℕ
  /-- the `DEFEND` bonus is up -/
  defending : Bool

instance : Inhabited Stack := ⟨⟨.enemy, 0, default, ⟨0, 0⟩, 0, 0, 0, false⟩⟩

namespace Stack
/-- R6: effective count `⌈avail / hp⌉`. -/
def count (u : Stack) : ℕ := (u.pool + u.type.hp - 1) / u.type.hp
def alive (u : Stack) : Prop := 0 < u.pool
instance (u : Stack) : Decidable u.alive := inferInstanceAs (Decidable (0 < u.pool))
/-- R8: damage accumulates in the pool, overkill is discarded. -/
def hit (u : Stack) (D : ℕ) : Stack := { u with pool := u.pool - D }
/-- Effective defence, with the `DEFEND` bonus (R13). -/
def defEff (u : Stack) : ℕ := u.type.dfn + if u.defending then defendBonus u.type.dfn else 0
end Stack

/-- R7: the blow of `a` on `t`. -/
def blow (a t : Stack) : ℕ := damage a.count a.type.dmg ((a.type.att : ℤ) - t.defEff)

inductive Phase | normal | wait
  deriving DecidableEq, Repr

structure State where
  units : ℕ → Stack
  phase : Phase
  /-- stacks still to be activated in the current phase, in order -/
  queue : List ℕ
  /-- stacks that issued `WAIT` in the current `NORMAL` phase -/
  bucket : List ℕ
  /-- rounds remaining, the current one included -/
  roundsLeft : ℕ

def sideRank : Side → ℕ
  | .player => 0
  | .enemy => 1

/-- R9, `NORMAL` phase: speed descending, then side (player first), then slot. -/
def normalLe (us : ℕ → Stack) (i j : ℕ) : Bool :=
  let a := us i; let b := us j
  decide (b.type.spd < a.type.spd ∨ (a.type.spd = b.type.spd ∧
    (sideRank a.side < sideRank b.side ∨ (sideRank a.side = sideRank b.side ∧ a.slot ≤ b.slot))))

/-- R9, `WAIT` phase: speed ascending, then side (player first), then slot. -/
def waitLe (us : ℕ → Stack) (i j : ℕ) : Bool :=
  let a := us i; let b := us j
  decide (a.type.spd < b.type.spd ∨ (a.type.spd = b.type.spd ∧
    (sideRank a.side < sideRank b.side ∨ (sideRank a.side = sideRank b.side ∧ a.slot ≤ b.slot))))

/-- The `NORMAL` queue of a round: the living stacks, sorted. -/
def normalQueue (N : ℕ) (us : ℕ → Stack) : List ℕ :=
  ((List.range N).filter (fun i => decide (us i).alive)).mergeSort (normalLe us)

/-- The initial position induced by an allocation. -/
def initUnits (I : Instance) (α : ℕ → SlotAlloc) (i : ℕ) : Stack :=
  if i < I.k then
    -- an empty slot holds no stack (`brute_force.assemble` creates none): it is a dead
    -- placeholder whose type is `default`, whatever type index the allocation names
    let ty := if 0 < (α i).count then (I.army.getD (α i).type default).1 else default
    ⟨.player, i, ty, I.slots.getD i ⟨0, 0⟩, (α i).count * ty.hp, (α i).count, 1, false⟩
  else if i < I.N then
    let es := I.enemies.getD (i - I.k) ⟨default, 0, ⟨0, 0⟩⟩
    ⟨.enemy, i - I.k, es.type, es.hex, es.count * es.type.hp, es.count, 1, false⟩
  else default

def initState (I : Instance) (α : ℕ → SlotAlloc) : State :=
  { units := initUnits I α
    phase := .normal
    queue := normalQueue I.N (initUnits I α)
    bucket := []
    roundsLeft := I.R }

/-- Hexes enterable by stack `i` in position `us`: on the board, not an obstacle, not
occupied by another living stack (R3, R4). -/
def free (I : Instance) (us : ℕ → Stack) (i : ℕ) (h : Hex) : Prop :=
  I.inBounds h ∧ h ∉ I.obstacles ∧ ∀ i' < I.N, i' ≠ i → (us i').alive → (us i').hex ≠ h

instance (I : Instance) (us : ℕ → Stack) (i : ℕ) : DecidablePred (free I us i) := by
  intro h; unfold free Instance.inBounds; infer_instance

/-- BFS movement range of stack `i` (R10, R11). -/
def reachOf (I : Instance) (us : ℕ → Stack) (i : ℕ) : Finset Hex :=
  reach (free I us i) (us i).hex (us i).type.spd

/-- Activation: the `DEFEND` bonus expires when the stack gets a turn. -/
def activate (u : Stack) : Stack := { u with defending := false }

/-- `WALK_AND_ATTACK` by `i` on `t` from approach hex `dest` (R11, R12):
move, strike, then the target retaliates if it is alive, the attacker is alive, and a
charge is left. -/
def resolveAttack (us : ℕ → Stack) (i t : ℕ) (dest : Hex) : ℕ → Stack :=
  let a := { activate (us i) with hex := dest }
  let tg := (us t).hit (blow a (us t))
  let us1 := Function.update (Function.update us i a) t tg
  if tg.alive ∧ a.alive ∧ 0 < tg.retal then
    Function.update (Function.update us1 t { tg with retal := tg.retal - 1 }) i
      (a.hit (blow tg a))
  else us1

/-- Round boundary (R9, R12): charges reset to one, `DEFEND` flags persist. -/
def newRound (I : Instance) (s : State) : State :=
  let us := fun i => { s.units i with retal := 1 }
  { units := us, phase := .normal, queue := normalQueue I.N us, bucket := [],
    roundsLeft := s.roundsLeft - 1 }

/-- One step of the battle.  Player steps are the player's choices; enemy steps are
forced by `(‡)`. -/
inductive Step (I : Instance) : State → State → Prop
  /-- a dead stack's turn is skipped -/
  | skip {s : State} {i : ℕ} {q : List ℕ} :
      s.queue = i :: q → ¬ (s.units i).alive →
      Step I s { s with queue := q }
  /-- `(‡)`, first half: an enemy `WAIT`s at its `NORMAL` activation -/
  | enemyWait {s : State} {i : ℕ} {q : List ℕ} :
      s.phase = .normal → s.queue = i :: q → (s.units i).alive → (s.units i).side = .enemy →
      Step I s { s with units := Function.update s.units i (activate (s.units i)),
                        queue := q, bucket := s.bucket ++ [i] }
  /-- `(‡)`, second half: on its postponed activation, it `DEFEND`s -/
  | enemyDefend {s : State} {i : ℕ} {q : List ℕ} :
      s.phase = .wait → s.queue = i :: q → (s.units i).alive → (s.units i).side = .enemy →
      Step I s { s with units := Function.update s.units i
                                    { activate (s.units i) with defending := true },
                        queue := q }
  /-- player `WAIT` (only in the `NORMAL` phase) -/
  | playerWait {s : State} {i : ℕ} {q : List ℕ} :
      s.phase = .normal → s.queue = i :: q → (s.units i).alive → (s.units i).side = .player →
      Step I s { s with units := Function.update s.units i (activate (s.units i)),
                        queue := q, bucket := s.bucket ++ [i] }
  /-- player `DEFEND` -/
  | playerDefend {s : State} {i : ℕ} {q : List ℕ} :
      s.queue = i :: q → (s.units i).alive → (s.units i).side = .player →
      Step I s { s with units := Function.update s.units i
                                    { activate (s.units i) with defending := true },
                        queue := q }
  /-- player move to a hex of its BFS reach -/
  | playerMove {s : State} {i : ℕ} {q : List ℕ} {dest : Hex} :
      s.queue = i :: q → (s.units i).alive → (s.units i).side = .player →
      dest ∈ reachOf I s.units i →
      Step I s { s with units := Function.update s.units i
                                    { activate (s.units i) with hex := dest },
                        queue := q }
  /-- player `WALK_AND_ATTACK` -/
  | playerAttack {s : State} {i : ℕ} {q : List ℕ} {dest : Hex} {t : ℕ} :
      s.queue = i :: q → (s.units i).alive → (s.units i).side = .player →
      dest ∈ reachOf I s.units i → t < I.N → (s.units t).alive →
      (s.units t).side = .enemy → Hex.Adj dest (s.units t).hex →
      Step I s { s with units := resolveAttack s.units i t dest, queue := q }
  /-- end of the `NORMAL` phase: replay the bucket in `WAIT` order -/
  | toWait {s : State} :
      s.phase = .normal → s.queue = [] →
      Step I s { s with phase := .wait, queue := s.bucket.mergeSort (waitLe s.units),
                        bucket := [] }
  /-- round boundary -/
  | nextRound {s : State} :
      s.phase = .wait → s.queue = [] → 1 < s.roundsLeft →
      Step I s (newRound I s)

/-- The battle is over: the `WAIT` phase of the last round is exhausted. -/
def Done (s : State) : Prop := s.phase = .wait ∧ s.queue = [] ∧ s.roundsLeft ≤ 1

/-- Value destroyed: whole enemy creatures killed, weighted by value. -/
def destroyed (I : Instance) (s : State) : ℕ :=
  ∑ i ∈ Finset.range I.N,
    if (s.units i).side = .enemy then ((s.units i).init - (s.units i).count) * (s.units i).type.value
    else 0

/-- **`ARMY-ALLOCATION`** (paper §2.3): some feasible allocation and some play destroy
value at least `W`. -/
def ArmyAllocation (I : Instance) : Prop :=
  ∃ α, Feasible I α ∧ ∃ s, Relation.ReflTransGen (Step I) (initState I α) s ∧ Done s ∧
    I.W ≤ destroyed I s

end Homm3
