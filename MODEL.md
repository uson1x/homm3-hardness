# A formal model of Heroes of Might and Magic III combat

Working draft, intended as Section 2 of an arXiv cs.CC submission.

Every rule below is cited against the VCMI source tree, an open-source reimplementation
of the HoMM3 engine (https://github.com/vcmi/vcmi), local checkout `$VCMI_CHECKOUT` at
commit `b5cee70` — a fork merge whose every cited path is byte-identical to the public
`vcmi/vcmi` commit `deeab240c8d6db193101669a7702bfc0e4f4e872` (develop, 2026-06-19); the
entire diff between the two across `lib/`, `config/`, `server/`, `test/` is 18 lines in
`lib/callback/AIFactory.cpp`, which nothing here cites. Citations are given
as `path:line`. Where a rule is *not* taken from code, the source is stated explicitly.

VCMI is used as the specification rather than the original binary because it is readable,
publicly auditable, and its combat module is known to reproduce original H3 damage numbers.
This is stated as a modelling assumption, not as a proven fact: see §8.

---

## 1. Why the game must be generalised

Original HoMM3 has a battlefield of fixed size 11 × 17
(`lib/battle/BattleHex.h:19-24`: `BFIELD_WIDTH = 17`, `BFIELD_HEIGHT = 11`,
`BFIELD_SIZE = 187`), at most 7 army slots per side
(`lib/constants/NumericConstants.h:32`: `ARMY_SIZE = 7`), and a fixed creature roster.
A game with a bounded state space is decidable in constant time, so no complexity
statement about the shipped game is meaningful.

We therefore follow the standard practice of the genre (Aloupis et al. on Nintendo games,
Demaine et al. on Zelda) and study a *generalised* game: the battlefield is `n × m`, the
number of slots is `k`, and creature statistics are arbitrary integers given in the input.
Every *rule* of combat — movement, adjacency, damage, kills, retaliation, turn order — is
that of the shipped game, cited line by line below; the one deliberate simplification is
the equal-initiative tie rule (§5 note: the engine alternates sides, this model uses
side-then-slot; the engine's rule is itself pinned by two dedicated engine-check cases,
and no construction here creates a cross-side tie).

One further thing is generalised, and it is not a bound, so it is stated here rather than
left to be discovered: **the deployment cells are part of the input.** In the shipped game
the starting hex of a stack is a function of the slot count and slot index, read from fixed
formation tables (`config/gameConfig.json:635-643, 653-661`, requirement documented at `:625`); in
the generalised game the scenario prescribes them. See §9 and §8.4. The object we study is
therefore a *generalized battle scenario with prescribed deployment cells*, and a claim
that "only the bounds are generalised" would be false.

Encoding convention: all numeric parameters (counts, hit points, damage, attack, defence,
speed) are written in **binary** unless stated otherwise. This matters — the game itself
routinely uses stack sizes in the tens of thousands and hit points in the thousands, so
binary is the honest encoding. Where a result is only weakly NP-hard we say so.

---

## 2. Battlefield

**Definition 2.1 (Battlefield).** A battlefield is a hex grid `H` with `n` rows and `m`
columns. Hexes are indexed `h = x + y·m` with `x ∈ [0,m)`, `y ∈ [0,n)`
(cf. `lib/battle/BattleHex.h:125,133-141` for the shipped instance `m = 17`).

> **Known divergence from the engine (review round 6).** The engine does not make every cell
> usable: `BattleHex::isAvailable()` returns false for the first and last column
> (`lib/battle/BattleHex.h:97-100`), and `getAccessibility` labels both columns
> `SIDE_COLUMN` (`lib/battle/CBattleInfoCallback.cpp:1321-1326`). Definition 2.1 and
> `scripts/homm3_model.py` treat all `n·m` cells as usable, so the transcription is *more
> permissive* than the engine here, and three of the four constructions place a deployment
> hex in column 0. The repair is a coordinate shift plus two padding columns, **with speeds
> left unchanged**; it has not been applied. Translation preserves every hex distance, so
> every reach argument carries over verbatim — but changing speeds does not: raising the
> player's speed by two in Theorem 1 lets slot 2 reach `E_1` on the PARTITION instance
> `(2, 4)`, which destroys the matching-reach lemma. Because the model is more permissive
> than the engine here, no regression test can catch the original gap — the tests compare the
> model against itself.

**Adjacency.** Six directions: `TOP_LEFT, TOP_RIGHT, RIGHT, BOTTOM_RIGHT, BOTTOM_LEFT,
LEFT` (`lib/battle/BattleHex.h:60-73`). The grid uses offset ("even-row shifted", i.e.
even rows sit half a hex to the right)
coordinates: stepping diagonally from an odd row uses `x-1`/`x`, from an even row `x`/`x+1`
(`lib/battle/BattleHex.h:147-178`).

**Distance.** Converting to axial coordinates via `x + ⌊y/2⌋`, the distance is
`max(|dx|,|dy|)` when `dx` and `dy` have the same sign and `|dx| + |dy|` otherwise
(`lib/battle/BattleHex.h:195-210`).

**Obstacles.** A subset of hexes may be marked impassable. In the engine this arises from
three mechanisms which we merge into one: battlefield-specific `impassableHexes`, obstacle
objects, and (in sieges) walls (`lib/battle/CBattleInfoCallback.cpp:1328-1391`). A hex
occupied by a living unit is likewise not enterable
(`lib/battle/CBattleInfoCallback.cpp:1355-1360`).

For the deterministic model we use only *static impassable hexes*; the "stopper" obstacles
(quicksand, moat, land mines) are excluded because they carry randomness or state.

---

## 3. Units

**Definition 3.1 (Creature type).** A creature type `t` is a tuple

```
t = (att, def, dmg_min, dmg_max, hp, spd, flags)
```

with `att, def, hp, spd ∈ ℤ_{>0}`, `1 ≤ dmg_min ≤ dmg_max`, and `flags` a subset of the
ability set (§7). Attack and defence are read via
`lib/battle/DamageCalculator.cpp:135,190`; damage via `:32-33`; speed doubles as
initiative, see §5.

**Definition 3.2 (Stack).** A stack is a pair `(t, c)` with `c ∈ ℤ_{>0}` creatures of type
`t`, occupying one hex (two adjacent hexes for double-wide creatures,
`lib/battle/Unit.cpp:232-245`). Its health is stored as a pair
`(fullUnits, firstHPleft)` (`lib/battle/CUnitState.h:123-125`) representing a pool of

```
avail(S) = firstHPleft + hp · fullUnits          [lib/battle/CUnitState.cpp:183-186]
```

points, of which `firstHPleft ∈ (0, hp]` belongs to the partially wounded "top" creature.

**Definition 3.3 (Effective count).**

```
count(S) = fullUnits + [firstHPleft > 0]         [lib/battle/CUnitState.cpp:282-285]
```

> **This is the single most important rule for our reductions.** A stack's *offensive
> output* is proportional to `count(S)`, not to `avail(S)`. A stack of one Archangel
> reduced to 1 hit point out of 250 attacks exactly as hard as a healthy one. Damage is a
> **step function** of accumulated damage taken: it does not decay smoothly, it drops only
> when a whole creature dies.

**Damage application.** Damage `D` applied to a stack (`lib/battle/CUnitState.cpp:193-218`):

```
if D < firstHPleft:  firstHPleft ← firstHPleft − D            (no creature dies)
else:                total ← max(0, avail(S) − D); recompute (fullUnits, firstHPleft)
                     from total via  firstHPleft = total mod hp,
                                     fullUnits  = total div hp,
                     with the correction  firstHPleft = 0 ∧ fullUnits ≥ 1
                                       ⟹ firstHPleft = hp, fullUnits −= 1
                                                              [:262-273]
```

Excess damage beyond `avail(S)` is discarded (`:202-203` clamps `amount` to `available()`).
This is the **overkill rule**: damage above a stack's remaining pool is wasted.

**Kill count** for damage `D` against a stack (`lib/battle/DamageCalculator.cpp:522-531`):

```
kills(D) = 0                                            if D < firstHPleft
kills(D) = min( 1 + ⌊(D − firstHPleft)/hp⌋ , count )    otherwise
```

---

## 4. Damage

The full engine formula is `lib/battle/DamageCalculator.cpp:556-587`. Stripped of the
abilities we exclude in §7, it is:

**Definition 4.1 (Damage).** Let stack `A` (attacker, type `a`, effective count `c_A`)
strike stack `B` (defender, type `b`). Let

```
Δ = att(a) − def(b)
```

Then

* **Attack factor** (`:210-224`, constants from `config/gameConfig.json:609-611`):

  ```
  f_att = 1 + min(0.05 · Δ , 4.0)          if Δ > 0
  f_att = 1                                otherwise
  ```

* **Defence factor** (`:322-337`, constants from `config/gameConfig.json:613-615`):

  ```
  f_def = 1 − min(0.025 · (−Δ) , 0.7)      if Δ < 0
  f_def = 1                                otherwise
  ```

* **Melee penalty for shooters in melee** (`:385-390`): if `A` is a shooter attacking in
  melee without `NO_MELEE_PENALTY`, multiply `f_def` by `0.5`.

* **Damage:**

  ```
  dmg(A → B) = max( 1 , ⌊ c_A · d · f_att · f_def ⌋ )
  ```

  where `d ∈ [dmg_min, dmg_max]` is the per-creature damage roll
  (`:123-131`: base damage is multiplied by `getCount()`; `:576-577`: floor and the
  lower clamp at 1).

**Arithmetic semantics (round 4, finding 3.4).** In the *mathematical* problem the
constants above are the exact rationals `1/20`, `4`, `1/40`, `7/10`, the products are exact
rational arithmetic, and `⌊·⌋` is the exact integer floor. All theorem statements are about
this exact-rational model. For the theorem constructions the exact and floating readings
provably agree: Theorems 1, 2 and 4 set `Δ = 0` and never form a fractional product at
all, and Theorem 3's damage tables are recomputed and compared under both cap readings
(`verify_x3c.py`, `crosscheck_sol.py`). The *engine* evaluates the same formula in IEEE-754
doubles with constants parsed from JSON; the one observed divergence — the cap `0.7`
loading as `0.7000000000000001`, one ULP high, which changes `⌊base · 0.3⌋` when
`base · 0.3` is an exact integer — is documented in `engine-check/REPORT.md` and dodged by
every construction (candidate-D §3.3). The reference implementation (`scripts/homm3_model.py`)
computes in Python floats, i.e. the engine's semantics; for the empirical instances of
`empirics/` that implementation is the operative definition of the optimum. Where the two
semantics could differ, mathematical statements mean the exact-rational model, and engine
behaviour is reported as an implementation cross-check.

**Determinisation.** The only randomness left in this stripped model is `d`, morale and
luck. We remove morale and luck by forbidding the corresponding abilities and setting
hero morale/luck to 0 (§7), and we fix

```
d := dmg_min = dmg_max
```

i.e. **we require `dmg_min = dmg_max` in every instance we construct**, rather than
picking `max` or the average of a wider range.

*Justification for this choice.* The alternative — setting `d = dmg_max`, or
`d = (dmg_min + dmg_max)/2` — is a modelling decision that invites the objection "you
tuned the model until the proof worked". Constraining the *instances* instead of
reinterpreting the *rules* avoids the objection entirely. The engine treats `dmg_min` and
`dmg_max` as ordinary per-creature integer parameters with no constraint beyond
`dmg_min ≤ dmg_max` (`DamageCalculator.cpp:32-42`, and the schema at
`config/schemas/creature.json` imposes no separation), and in the generalised game
creature statistics are part of the input. So `dmg_min = dmg_max` instances are legal by
construction, and `H3-det` is a genuine *special case* of the generalized game (its flat
statistics are legal creature statistics, not an averaged approximation). Hardness of a
special case implies hardness of the generalized game — not of the shipped game, whose
narrower deployment and roster are a separate matter (§8.2); averaging would only be
needed for a statement about *all* creatures, and we make no such statement.

> **Not verified locally.** Whether the shipped creature roster happens to contain
> flat-damage creatures is a separate question we could not settle from this checkout:
> VCMI reads base creature statistics from the original game's `CRTRAITS.TXT`, which is
> not part of the source tree (`config/creatures/*.json` carries only graphics, sound and
> upgrade data). The claim is not needed — the generalisation supplies the statistics —
> but the paper should not assert it without a check against game data.

---

## 5. Turn structure

**Rounds and initiative.** Combat proceeds in rounds. Within a round every living stack
acts once, in decreasing order of `spd`; ties are broken (in this model, but **not** in the
engine — see the note below) by side and then by **slot
index**, lower slot first (`lib/battle/BattleInfo.cpp:978-1006`,
`lib/battle/CBattleInfoCallback.cpp:474-509`). Initiative equals the `STACKS_SPEED` value,
i.e. the same number as movement range (`lib/battle/CUnitState.cpp:589-592`).

> **The tie rule above is this model's, not the engine's (review rounds 6–7).** VCMI does not
> order equal-initiative stacks by side and slot. `takeOneUnit` prefers a unit of whichever
> side did *not* move last, so equal-speed stacks **alternate** between the sides, and the
> attacker gets priority only on the first turn
> (`lib/battle/CBattleInfoCallback.cpp:474-509`). The `CMP_stack` comparator cited above is
> not the whole scheduler. We keep the simplified rule because in every construction here each
> player stack is strictly faster than every enemy, so no cross-side initiative tie ever
> arises and the two rules agree on the instances we build; but it is a simplification, and
> `scripts/homm3_model.py` shares it, so the mechanics tests compare the transcription against
> itself and cannot detect the difference. Any future construction that relies on equal speeds
> across the two sides must use the engine's rule instead.
>
> The `WAIT` phase runs in *increasing* speed order, and alternates sides on ties by the same
> mechanism (`:495-509`). That matters for the paper's garrison policy `(‡)` =
> `WAIT`-then-`DEFEND` (§9): a player stack that also waits can be scheduled after a slower
> enemy and therefore *can* meet a `DEFEND` bonus, so the policy's justification is a
> one-round witness-plus-upper-bound lemma (`proofs/candidate-A.md` §2.1), not a claim that
> no blow ever meets the bonus.

> Note the coupling: **speed is simultaneously initiative and movement range**
> (`lib/battle/CUnitState.cpp:594-600` returns the same cached value). A construction
> cannot set them independently. This constrains gadget design and is worth stating in the
> paper, because it rules out the obvious trick of "slow but far-reaching" units.

**Phases** (`lib/battle/Unit.h:33-44`): `SIEGE = 0`, `NORMAL = 1`, `WAIT_MORALE = 2`,
`WAIT = 3`. Stacks that used the WAIT action move to the WAIT bucket and act after all
NORMAL stacks, in *increasing* order of initiative
(`lib/battle/CBattleInfoCallback.cpp:496-509, 601-623`). We keep WAIT in the model: it is a
genuine strategic primitive and will matter for candidate B.

**Round boundary.** A new round begins when no living stack still has an action
(`server/battles/BattleFlowProcessor.cpp:311-364`). At the boundary every stack's
retaliation counter is reset (`lib/battle/BattleInfo.cpp:663-670` →
`lib/battle/CUnitState.cpp:920`).

**Movement.** A stack may move to any hex within BFS distance `spd` over enterable hexes
(`lib/battle/CBattleInfoCallback.cpp:1411-1469` unweighted BFS, cost 1 per step;
`:659,672-673` filters by `distances[i] ≤ getMovementRange()`). Flying units use straight
hex distance instead (`:1715-1744`).

**Attack.** The `WALK_AND_ATTACK` action moves the stack to a hex adjacent to the target
and then strikes (`server/battles/BattleActionProcessor.cpp:216-352`). Consequently a
melee stack of speed `s` can strike any enemy at distance at most `s + 1`.

---

## 6. Retaliation

`server/battles/BattleActionProcessor.cpp:298-334`, in order:

1. The attacker's blow is resolved first, but only if both stacks are alive (`:307`,
   and `makeAttack` re-checks at `:1034-1035`).
2. The defender retaliates afterwards (`:326-333`) if and only if
   * the attacker is still alive (`:326`),
   * the attacker does not have `BLOCKS_RETALIATION` (`:327`),
   * this is the attacker's first blow of the action (`:330`),
   * and `ableToRetaliate()` holds — which is `alive() && counterAttacks.canUse()`
     (`lib/battle/CUnitState.cpp:484-488`, `alive()` at `:490`).

**Consequences we rely on:**

* **A stack killed outright does not retaliate.** This is the central tactical fact of
  HoMM3 and the source of the threshold nonlinearity in candidate A.
* **Retaliations are per round, not per turn.** One base retaliation, reset at the round
  boundary (`lib/battle/CUnitState.cpp:127-136` gives `1 + ADDITIONAL_RETALIATION`,
  `:920` resets). So the *first* attacker into a stack absorbs the retaliation and every
  subsequent attacker in the same round strikes free.
* Units with `NO_RETALIATION` or `SIEGE_WEAPON` never retaliate
  (`lib/battle/CUnitState.cpp:120,129-130`).

---

## 7. The deterministic fragment `H3-det`

**Definition 7.1.** `H3-det` is the game defined by §§2–6 subject to:

| Excluded | Reason |
|---|---|
| Morale, luck | randomness (luck factors: `DamageCalculator.cpp:247-259, 408-413`; morale extra turn: `BattleFlowProcessor.cpp:776-781`, used at `:844-850`) |
| `dmg_min < dmg_max` | randomness |
| Spells, heroes, mana | large rule surface, not needed |
| Resurrection, `REBIRTH`, healing | non-monotone state |
| `FEROCITY`, `DEATH_BLOW`, `FIRST_STRIKE`, `JOUSTING`, `HATE`, `REVENGE`, `SLAYER` | conditional multipliers; excluded so that §4 is the whole formula |
| Shooters, ammunition | *not* excluded — retained, see below |
| Double-wide creatures | retained but unused in candidate A |
| Stopper obstacles (moat, quicksand, mines) | randomness / hidden state |

Retained: movement, positioning, static obstacles, melee attack, retaliation, WAIT,
DEFEND, shooting, `NO_RETALIATION`, `BLOCKS_RETALIATION`, `UNLIMITED_RETALIATIONS`,
`ADDITIONAL_RETALIATION`, `NO_MELEE_PENALTY`, `NO_DISTANCE_PENALTY`, flying.

> **The retained list is wider than §4 actually specifies (review round 6), and the gap is
> real.** Two claims elsewhere in this document are false for the *retained* inputs, though
> true for every instance any reduction builds:
>
> * §4 is called "the whole formula". It is not, for a retained shooter: the engine applies a
>   `0.5` distance penalty when `battleHasDistancePenalty` holds, plus wall and obstacle
>   penalties (`lib/battle/DamageCalculator.cpp:362-390, 394-406`), and §4 has no ranged term and does
>   not define a `SHOOT` action at all. A retained shooter with base damage 10 and `Δ = 0`
>   deals 5 in the engine and 10 here.
> * "The first attacker absorbs the retaliation and later attackers strike free" is false with
>   the retained `ADDITIONAL_RETALIATION` / `UNLIMITED_RETALIATIONS`: `CRetaliations::total()`
>   returns `1 + ADDITIONAL_RETALIATION`, or unlimited.
>
> **Definition 7.1a (`H3-det-melee`).** The fragment in which every creature is a melee
> non-shooter without `ADDITIONAL_RETALIATION`, `UNLIMITED_RETALIATIONS` or any conditional
> multiplier, each stack has a single attack per activation, and retaliation is the base one
> charge per round. §4 *is* the whole damage formula on `H3-det-melee`, and **all four
> reductions construct only `H3-det-melee` instances**, so every hardness result stands as
> proved. What does not stand is the wider claim: until the ranged and multi-retaliation
> actions are written out, results should be stated for `H3-det-melee`, and hardness transfers
> upward to `H3-det` exactly as before, since `H3-det-melee` is a restriction of it.
>
> It does **not** transfer to the shipped game, and saying so would contradict §2.1 of the
> paper. `H3-det-melee` is a restriction of the *generalized* prescribed-deployment problem,
> not of shipped HoMM3: Theorem 3 at `q = 3` needs `k = 9` slots against the shipped limit of
> seven, and all four reductions prescribe deployment cells, statistics and board dimensions
> the shipped game does not offer. The correct chain is
> `H3-det-melee ⊂ H3-det ⊂ generalized battle-scenario planning`, and the shipped game is a
> different, finite object.

**Proposition 7.2.** `H3-det` is a finite deterministic two-player perfect-information
game. Given both players' action sequences, the outcome is computable in time polynomial
in the instance size and the number of rounds.

*Proof sketch.* Every rule in §§2–6 is an arithmetic or BFS computation on a state of size
`O(nm + k log C)` where `C` bounds the numeric parameters. ∎

Executable reference implementation: `scripts/homm3_model.py`; conformance tests against
hand-computed engine numbers in `scripts/verify_mechanics.py`.

---

## 8. Modelling assumptions, stated honestly

1. **VCMI ≡ HoMM3.** We assume VCMI's combat module reproduces the original. VCMI's own
   settings file exposes the constants `0.05 / 4.0 / 0.025 / 0.7`
   (`config/gameConfig.json:609-615`) that match the community-documented H3 formula, and
   the file's comments reference HotA and h3assist cross-checks
   (`lib/battle/DamageCalculator.cpp:149-150`). This is strong but not conclusive evidence.
   Because our hardness results only need *some* legal creature statistics, a small
   discrepancy in the original engine would not invalidate them; it would at worst change
   which constants the gadgets use.
2. **The generalisation is the standard one.** Board size, slot count and creature
   statistics become input. We do *not* invent new mechanics, and we do *not* remove
   mechanics in a way that makes the game easier for us: `H3-det` restricts the *instance
   family* of the generalized model, so hardness of `H3-det` transfers upward to that
   generalized model. It does **not** by itself transfer to the shipped game — item 3
   below and §8.2 spell out exactly where the shipped game is narrower (deployment comes
   from formation tables, the roster/board are fixed), and recovering hardness under those
   constraints is an open problem, not a corollary.
3. **Deployment cells are prescribed by the scenario, not derived from a formation table.**
   This is the one place where the generalisation reaches beyond "lift the bounds", and it
   is load-bearing for the reductions: every one of them chooses where the slots start. It
   is a *strictly more general* problem than the shipped game's — a native-formation
   instance is a prescribed-deployment instance — so hardness of the generalized scenario
   does not by itself transfer back to native formations. See §9 and
   `proofs/candidate-A.md` §5.4, `proofs/candidate-D-singletype.md` §8.1. Recovering the
   results under native formations is an explicitly deferred open problem.
4. **Two engine quirks are noted and avoided.** (a) A `FIRST_STRIKE` pre-emptive blow
   consumes the defender's retaliation charge (`BattleActionProcessor.cpp:303` passes
   `counter = true`); we exclude `FIRST_STRIKE`. (b) `getMovementRange(int turn)` ignores
   its argument (`CUnitState.cpp:594-600`); irrelevant to us since we never query future
   turns.

---

## 9. The candidate A problem

Before the battle, an army is a multiset of creatures which the player distributes over
`k` slots. In the shipped game `k = 7`. Two rules make the distribution nontrivial:

* **A slot is homogeneous.** All creatures in one slot have the same type
  (`lib/mapObjects/army/CCreatureSet.cpp:73-83`). So `n` distinct types need `n` slots;
  if `n > k`, some types must be left behind.
* **A type may be split across slots.** Nothing forces stacks of the same type to merge
  (`mergeableStacks`, `CCreatureSet.cpp:227-257`, exists precisely because they can
  coexist). So the number of creatures per slot is a free integer variable.
* **Slot index is not cosmetic.** It determines the deployment hex (the engine's
  `attackerUnitsLoose` / `attackerUnitsTight` tables map the slot count and slot index to
  starting hexes, `config/gameConfig.json:635-643, 653-661`; the requirement is documented at
  `:625`) and
  breaks initiative ties (`CBattleInfoCallback.cpp:484-502`).

**Problem `ARMY-ALLOCATION`.**

> **Input.** A battlefield `(n, m, obstacles)`; `k` player slots with deployment hexes
> `p_1, …, p_k`; a multiset `A` of player creatures given as pairs (type, count), each
> type carrying a nonnegative integer *value* used only by the objective; a fixed defence
> `D`, i.e. a list of enemy stacks with their types, counts and hexes, which plays the
> fixed scripted policy `(‡)` below; a round bound `R` in unary; a target `W ∈ ℤ_{>0}`.
>
> **Question.** Is there an allocation of `A` to the `k` slots (each slot receiving at most
> one type, each type's total across slots at most its stock in `A`) and a sequence of
> player actions, such that after `R` rounds against `(‡)` the total value of enemy
> creatures killed is at least `W`?

Notes on the formulation, and why it is fair:

* **The deployment hexes `p_1, …, p_k` are given in the input, and this is a genuine
  generalisation.** The shipped game computes them from the slot count and slot index via
  the `attackerUnitsLoose` / `attackerUnitsTight` tables
  (`config/gameConfig.json:635-643, 653-661`), which put the army in one or two fixed columns; here
  the scenario prescribes them, exactly as it prescribes the obstacles and the enemy
  placement. The problem is therefore *generalized battle scenario planning*, and the
  hardness results below are statements about it, not about the shipped deployment
  geometry. Every construction in `proofs/` uses this freedom, most heavily
  `candidate-D-singletype.md`, which needs one deployment cell inside each element region.
  Whether hardness survives native formations is open and explicitly deferred (§8.3).
* The enemy policy is **fixed, not an input**: `(‡)` — *if the stack has not waited this
  round, it issues `WAIT`; on its postponed activation, it issues `DEFEND` at its current
  hex*. Both are shipped actions: `WAIT` postpones the terminal action to the round's
  `WAIT` phase (§5), and `DEFEND` (`BattleActionProcessor.cpp:160-212, 693`)
  ends the turn without moving or attacking and grants `+20 %` defence (integer, floor
  `+1`) until the stack next receives a turn (`BattleActionProcessor.cpp:168-196`,
  expiry at `BattleInfo.cpp:676-688`). Because the postponed `DEFEND` sits in the `WAIT`
  phase, it lands after every `NORMAL`-phase player action regardless of relative speeds;
  the precise one-round lemma, its two out-of-scope failure modes (a waiting player, and
  `R ≥ 2`), and the policy's history (review rounds 5–6: an earlier `(‡)` defended at the
  stack's own turn, which made six recorded empirical optima unattainable) are in
  `proofs/candidate-A.md` §2.1. Note that "hold position" on its own does **not**
  determine an action, since `H3-det` retains movement, `WAIT` and `DEFEND`. An earlier
  version of this definition took an arbitrary "deterministic, poly-time computable `π`"
  as part of the input; that is not a clean language definition (an encoded program with
  a *promised* running time is not a syntactically checkable input restriction), a
  circuit encoding would repair it at no gain, and every theorem uses `(‡)` anyway —
  hardness against the one fixed policy is the stronger and cleaner statement (round-4
  review, finding 1.3).
* The enemy is **scripted**, not adversarial. This keeps the problem in NP (the certificate
  is the allocation plus the player's actions) and matches the informal statement "against
  a fixed defence". The adversarial version is a different problem and belongs to
  candidate B.
* "Value of enemy creatures killed" — the objective counts **whole creatures killed**,
  weighted by the per-type value. It is the game's own accounting: a stack at 1 hit point
  is a fully functional stack (§3, Definition 3.3), so hit points removed without a kill
  buy nothing in that round. It is **not**, however, the sole source of hardness: counting
  *hit points removed* instead collapses only the matching-reach family of Theorem 1 to a
  separable concave sum; on the featureless family the hit-point objective remains
  strongly NP-hard (`proofs/candidate-C-featureless.md` Corollary 6.3, machine-checked in
  `scripts/verify_hp_objective.py`). An earlier version of this bullet called the
  hit-point variant "trivially linear" in general, which is false (round-4 review).
* `R` in unary keeps evaluation polynomial.
* Allowing creatures to be left behind models the garrison; §Theorem 2 of
  `proofs/candidate-A.md` does not need this freedom.

The two nonlinearities the reductions exploit are exactly the two we flagged above:

1. **Kill thresholds.** `kills(D)` is a step function of `D` (§3). Damage that fails to
   finish a creature buys nothing in the objective.
2. **Count-based output.** A wounded stack fights at full strength (Definition 3.3), so
   partial damage does not even buy a reduction in the enemy's output. Combined with the
   retaliation rule (§6), killing a stack outright is *strictly superadditive* in value
   compared to damaging it.

These are what make the allocation problem a knapsack rather than a linear program.
