# Army allocation in generalised Heroes of Might and Magic III is NP-complete

Draft. Companion to `../MODEL.md`, which fixes the rules and the citations into the VCMI
source. Bounded-instance machine checking of both constructions: `../scripts/brute_force.py`,
protocol in `../VERIFICATION.md`.

---

## 1. Statement

Recall `ARMY-ALLOCATION` from `MODEL.md` §9. Informally: before the battle the player
distributes a multiset of creatures over `k` homogeneous slots; slots are placed at fixed
deployment hexes; the defence and its policy are fixed; the question is whether some
allocation, together with some play, destroys enemy creatures of total value at least `W`
within `R` rounds.

> **Theorem 1.** `ARMY-ALLOCATION` is NP-complete, already for instances with
> `R = 1`, a **single creature type** in the player's army, a single enemy creature per
> enemy stack, no obstacles, and a battlefield of one row.
>
> **Theorem 2.** `ARMY-ALLOCATION` is **strongly** NP-hard, already for `R = 1` and
> instances in which every creature type has stock exactly one.

Theorem 1 is the more surprising of the two: it says the hardness does not come from
choosing *which* creatures to bring — there is nothing to choose — but purely from
choosing *how many creatures go in each slot*. Theorem 2 upgrades weak to strong hardness
at the cost of a richer roster, and rules out a pseudo-polynomial algorithm.

Both constructions use exactly two mechanics, both established in `MODEL.md` §3:

* **(K) Kill thresholds.** `kills(D)` is a step function: damage that does not finish a
  creature kills nothing (`DamageCalculator.cpp:522-531`).
* **(C) Count-based output.** A stack's damage is proportional to its *creature count*,
  not its remaining hit points (`CUnitState.cpp:282-285`, `DamageCalculator.cpp:123-131`),
  and a stack killed outright does not retaliate
  (`BattleActionProcessor.cpp:326-333`, `CUnitState.cpp:484-490`).

(K) alone suffices for the proofs. (C) is what makes (K) *tactically* meaningful rather
than an accounting artefact, and is discussed in §5.

---

## 2. Notation for the constructions

Theorem 1 uses a **corridor battlefield**: a single row of hexes (`n = 1`), so adjacency
is simply "index differs by one" and the hex distance is `|Δx|` (`MODEL.md` §2). Theorem 2
uses **three rows** — a single row is impossible for it, for the reason given in §4.1.
Neither construction uses obstacles. The conventions below apply to both.

Throughout, fix a constant `α ∈ ℤ_{>0}` and give every player creature type attack `α`
and every enemy creature type defence `α`. Then `Δ = α − α = 0` in `MODEL.md` §4, so
`f_att = f_def = 1` and, for a player stack of `c` creatures of per-creature damage `d`,

```
dmg = max(1, ⌊c · d⌋) = c · d          for c ≥ 1, d ≥ 1.                        (★)
```

All player creatures are melee, non-shooters, so the melee penalty does not apply.

Player creatures have speed `2`; enemy creatures have speed `1`, so within the `NORMAL`
phase every player stack is scheduled before every enemy stack (`MODEL.md` §5) — though
under `(‡)` nothing rests on that: every enemy's terminal `DEFEND` sits in the `WAIT`
phase regardless of speeds (§2.1). By `MODEL.md` §5 a melee stack of speed `s` can
strike any enemy at hex distance at most `s + 1`. So:

```
player stacks reach distance ≤ 3;   enemy stacks reach distance ≤ 2.            (†)
```

### 2.1 The garrison policy `(‡)`, as a complete deterministic policy

`MODEL.md` §9 requires the enemy policy `π` to be a deterministic, polynomial-time
computable map from state to action. "Hold position and never initiate an attack" is a
*description* of intent, not such a map: `H3-det` retains movement, `WAIT` and `DEFEND`
(`MODEL.md` §7), so the description leaves the action undetermined. We therefore fix

```
(‡)   if the stack has not waited this round, issue WAIT;
      on its postponed activation, issue DEFEND at its current hex.
```

Both actions are legal actions of the shipped game. `WAIT` moves the stack's terminal
action to the round's `WAIT` phase, which runs after all `NORMAL`-phase activations, in
*increasing* speed order (`MODEL.md` §5, `CBattleInfoCallback.cpp:495-519`). `DEFEND`
ends the turn without moving and without attacking (`BattleAction.cpp:41`, dispatched at
`BattleActionProcessor.cpp:693`); it grants the acting stack `+20 %` defence, computed as
an integer percentage bonus with a floor of `+1`, lasting until the stack next receives a
turn (`BattleActionProcessor.cpp:168-196`, `BonusDuration::STACK_GETS_TURN`, removed at
`BattleInfo.cpp:676-688`). `(‡)` reads nothing of the state beyond which of its own two
activations this is, is computable in constant time, and so is a legal `π`. The same
definition is used by `candidate-C-featureless.md` and `candidate-D-singletype.md` §2.1.

An earlier version of `(‡)` issued `DEFEND` directly at the stack's own `NORMAL`-phase
turn. That policy satisfies the theorems equally well — every player creature in the
constructions is strictly faster than every enemy — but it diverges from the empirical
corpus of the paper's Section 5 exactly when an enemy is *faster* than a player stack,
and external review round 5 showed six recorded optima to be unattainable under it. The
present `(‡)` was adopted, and verified reduction by reduction, in round 6: postponing
the `DEFEND` into the `WAIT` phase puts it after every non-waiting player action
*regardless of relative speeds*, which is both cleaner for the theorems and exact for
the corpus.

Three consequences, used throughout:

* **(‡a) No enemy ever initiates an attack**, so no player stack ever delivers retaliation
  damage. Neither `WAIT` nor `DEFEND` moves or strikes. This is the property the
  reductions need.
* **(‡b) A waiting or defending enemy still retaliates when struck.** Neither action
  consumes the retaliation charge (`MODEL.md` §6); retaliation is accounted for below.
* **(‡c) One-round lemma.** In round 1 under `(‡)`: *(i)* the blow of every player stack
  that did not wait meets the **un-raised** defence — the blow lands at the striker's
  `NORMAL`-phase activation, and every enemy's terminal `DEFEND` sits in the later `WAIT`
  phase, regardless of relative speeds; *(ii)* the blow of *every* player stack, waiting
  or not, delivers **at most** its nominal damage, since raising the target's defence can
  only lower `f_def` (`MODEL.md` §4). So **a blow delivers at most its nominal damage,
  with equality whenever the striking stack did not wait.**

  The scope of *(i)* is exactly one round, and the two failure modes outside it are worth
  recording, because an earlier justification ("no player blow ever meets the bonus")
  claimed too much and was refuted by review round 6:

  - a player stack that itself waits is scheduled in the `WAIT` phase by *increasing*
    speed, so a slower enemy's postponed `DEFEND` can land first and the player's
    postponed blow then meets the bonus — for such blows only the inequality *(ii)*
    holds;
  - for `R ≥ 2` the bonus persists past the round boundary until the enemy's next
    activation (`BattleInfo.cpp:676-688`), so a fast player striking early in round 2
    meets the bonus left over from round 1. Every theorem here sets `R = 1`; a
    multi-round construction must redo this analysis.

Every statement below that quantifies over an *arbitrary* play is therefore phrased with
"at most the nominal damage"; equalities are asserted only for the constructed witness
plays, which contain no `WAIT` and hence, by `(‡c)(i)`, meet no defence bonus. All the
reductions survive because the yes-witnesses strike in the `NORMAL` phase, before any
postponed `DEFEND`, and because extra enemy defence can only help the defence. The
mechanics `(‡)` stands on — the `WAIT`-phase order, the bonus arithmetic and its
duration, and the retaliation-charge neutrality of both actions — are unit-checked
against the cited engine lines in `../scripts/verify_mechanics.py` (the `defend`/`wait`
test group), and the searches of `../scripts/brute_force.py` run a `waitdefend` variant
in which the defence executes `(‡)` literally, phase by phase.

> **This choice of policy is load-bearing and was found by machine checking on finite instances, not by hand.**
> The first version of this proof used the policy "attack an adjacent player stack" and
> claimed that a slot holding `c_j` creatures delivers `c_j` damage to `E_j`. That is
> false. If `E_j` attacks the player stack in slot `j`, the player stack **retaliates**
> (`MODEL.md` §6), delivering a *second* `c_j` damage to `E_j` in the same round. The
> reduction then decides subset-sum with budget `2B` rather than `B`, and the brute-force
> check reported yes-instances of the game for no-instances of PARTITION. See
> `../VERIFICATION.md`, iteration 1.

Two independent repairs work, and both are machine-checked (`../VERIFICATION.md`,
iteration 2):

* **(‡) the defence never initiates** — it waits, then defends in place. Then no
  retaliation is triggered and a non-waiting slot delivers exactly `c_j`. This is the
  primary construction below.
* **`NO_RETALIATION` on the player creature type.** The defence may then attack freely; the
  player's stacks simply do not counter. `NO_RETALIATION` is a genuine ability of the game
  (`lib/bonuses/BonusEnum.h:101`, applied by blind and paralyse effects and carried by war
  machines), and creature abilities are part of the input in the generalised game.

We adopt (‡) because it uses no abilities at all. Note that (‡) is also a literal
reading of "a fixed defence": a garrison that stands its ground, braced.

Player creatures are given hit points `hp_P = 5`; since every enemy creature has
per-creature damage `1` and stack size `1`, no player creature can die during round 1 under
either repair. So the defence cannot interfere with the player's damage output at all, and
the reduction depends only on the allocation.

Enemy value is `1` per creature in Theorem 2 and `a_j` per creature in Theorem 1; the
per-type value is an input of the problem.

---

## 3. Theorem 1: NP-completeness from PARTITION

**PARTITION** (Garey–Johnson SP12). Given positive integers `a_1, …, a_n` with
`Σ_i a_i = 2B`, is there `S ⊆ [n]` with `Σ_{i∈S} a_i = B`?

### 3.1 The construction

Given a PARTITION instance `(a_1, …, a_n)` with `Σ a_i = 2B`, build the instance
`G(a)` of `ARMY-ALLOCATION`:

**Battlefield.** One row of `5n` hexes, indexed `0, …, 5n − 1`. No obstacles. For
`j = 1, …, n`, block `j` occupies hexes `5(j−1) … 5j−1`, of which

```
p_j := 5(j−1)        player deployment hex of slot j
e_j := 5(j−1) + 1    hex of enemy stack E_j
                     the remaining three hexes of the block are empty.
```

**Player army.** A single creature type `C` with

```
att(C) = α,  def(C) = α,  dmg_min(C) = dmg_max(C) = 1,  hp(C) = 5,  spd(C) = 2,
```

(`def(C) = α` is not load-bearing, but an earlier draft left it "arbitrary" while asserting
that no player creature dies; with `att` of every enemy type also set to `α` below, every
retaliation deals exactly 1 damage and the assertion is implied rather than assumed.)

and stock exactly `B` creatures. Slots: `k = n`, with deployment hexes `p_1, …, p_n`.

**Defence.** For each `j`, `E_j` is one creature of a type with

```
att = α,  def = α,  hp = a_j,  dmg_min = dmg_max = 1,  spd = 1,  value = a_j,
```

placed at `e_j`. Policy `π` as in §2.

**Question parameters.** `R = 1`, `W = B`.

The construction is computable in time polynomial in the *binary* encoding of `a`: the
battlefield has `5n` hexes and the numbers `a_j` appear only as hit points and values.

### 3.2 Geometry lemma

**Lemma 3.1.** In `G(a)`, a player stack deployed at `p_j` can attack `E_j` and no other
enemy stack, in round 1.

*Proof.* `dist(p_j, e_j) = 1`, so `E_j` is adjacent and attackable without moving. For
`j' ≠ j`, `dist(p_j, e_{j'}) = |5(j−1) − 5(j'−1) − 1| = |5(j − j') − 1| ≥ 4`, since
`|j − j'| ≥ 1`. By (†) a player stack reaches at most distance 3. ∎

**Lemma 3.2.** In round 1 of `G(a)`, if slot `j` holds `c_j ≥ 1` creatures, the maximum
damage the player can inflict on `E_j` is `c_j`. Consequently `E_j` dead at the end of
round 1 implies `c_j ≥ a_j`; and conversely, if `c_j ≥ a_j` and the stack of slot `j`
issues `WALK_AND_ATTACK` against `E_j` without waiting, `E_j` dies.

*Proof.* By Lemma 3.1, `E_j` can be struck only by the stack in slot `j`. That stack acts
once in round 1 (`MODEL.md` §5), and under (‡) it is never attacked, so it never
retaliates and delivers no damage outside its own action. By (★) with `d = 1` its strike
deals at most `c_j`, and exactly `c_j` unless it waited and met a defending `E_j`, in which
case at most that (§2.1, `(‡c)`) — at most, not strictly less: the engine clamps damage at 1
(`DamageCalculator.cpp:576`), so a one-creature, one-damage stack still delivers exactly 1
against a defending target, and only the inequality is used here. `E_j` is a single creature with `firstHPleft = hp = a_j`,
so by the kill rule (`MODEL.md` §3) it dies only once the damage it has absorbed reaches
`a_j`; since that damage is at most `c_j`, death implies `c_j ≥ a_j`. Conversely a
non-waiting strike lands at the striker's `NORMAL`-phase activation, meets the un-raised
defence by `(‡c)(i)`, delivers exactly `c_j ≥ a_j` and kills. By `(‡a)` no enemy action
can prevent any player stack from acting. ∎

### 3.3 Correctness

**Lemma 3.3 (yes ⟹ yes).** If the PARTITION instance is a yes-instance, then `G(a)` is a
yes-instance.

*Proof.* Let `S ⊆ [n]` with `Σ_{j∈S} a_j = B`. Allocate `c_j := a_j` for `j ∈ S` and
`c_j := 0` otherwise. The total allocated is `Σ_{j∈S} a_j = B`, exactly the stock, so the
allocation is feasible. Let every nonempty stack attack its neighbouring enemy. By
Lemma 3.2 every `E_j` with `j ∈ S` dies, so the destroyed value is
`Σ_{j∈S} a_j = B = W`. ∎

**Lemma 3.4 (no ⟹ no, contrapositive).** If `G(a)` is a yes-instance, then the PARTITION
instance is a yes-instance.

*Proof.* Fix a feasible allocation `(c_1, …, c_n)`, `Σ_j c_j ≤ B`, and a play destroying
value at least `W = B`. Let

```
S := { j ∈ [n] : E_j is dead at the end of round 1 }.
```

The only enemy creatures in the instance are the `E_j`, and `E_j` has value `a_j`, so the
destroyed value is exactly `Σ_{j∈S} a_j ≥ B`. By Lemma 3.2, `j ∈ S` implies `c_j ≥ a_j`.
Hence

```
B ≤ Σ_{j∈S} a_j ≤ Σ_{j∈S} c_j ≤ Σ_{j=1}^{n} c_j ≤ B,
```

so every inequality is an equality; in particular `Σ_{j∈S} a_j = B`. Thus `S` is a
PARTITION solution. ∎

**Lemma 3.5 (membership).** `ARMY-ALLOCATION` ∈ NP.

*Proof.* Fix the encoding first: the battlefield is part of the input as an explicit
hex grid, i.e. its dimensions `n, m` are given in unary (equivalently, the grid cells
are listed), and `R` is given in unary. This matches the game being modelled — a board
that exists hex by hex — and makes `O(nm)` genuinely polynomial in the input length;
without it, a sparse binary encoding of `n, m` would break the argument below. A
certificate is then the allocation (at most `k` pairs (type, count), each of size
polynomial in the input) together with the player's action sequence for `R` rounds: for
each stack-round pair, an optional `WAIT` bit and one terminal action, so at most `2·k·R`
action tokens — the factor 2 because a stack that waits still takes its terminal action
later in the same round (`MODEL.md` §5); an earlier draft wrote `k·R`, which undercounts
exactly those plays. Given the certificate the whole battle is simulated
deterministically: the fixed policy `(‡)` is computable in constant time, and every rule of
`MODEL.md` §§2–6 is an arithmetic operation or a BFS on the hex graph
(`MODEL.md` Proposition 7.2). Comparing destroyed value to `W` completes the check. ∎

**Proof of Theorem 1.** Membership by Lemma 3.5; hardness by Lemmas 3.3 and 3.4 together
with the polynomiality of the construction. The instances produced satisfy all the
restrictions claimed in the statement. ∎

### 3.4 Why this is only *weak* hardness

In `G(a)` the numbers `a_j` are encoded as hit points, in binary. If they were written in
unary the problem would be solvable in time `O(nB)` by the standard subset-sum dynamic
program, so Theorem 1 does not establish strong NP-hardness. We state this explicitly
because a reader of a "game is hard" paper is entitled to know which of the two it is.
Theorem 2 supplies the strong version.

The binary encoding is the appropriate one for this game: the shipped game routinely
carries stack sizes in the tens of thousands and creature hit points up to several hundred,
and the generalised game imposes no bound at all.

---

## 4. Theorem 2: strong NP-hardness from 3-PARTITION

**3-PARTITION** (Garey–Johnson SP15, strongly NP-complete). Given `3m` positive integers
`a_1, …, a_{3m}` and a bound `T` with `Σ_i a_i = mT` and `T/4 < a_i < T/2` for all `i`, is
there a partition of `[3m]` into `m` triples each summing to exactly `T`? The problem
remains NP-complete when all `a_i` are bounded by a polynomial in `m`, i.e. when they are
written in unary.

### 4.1 The construction

Given a 3-PARTITION instance, build `G₃(a, T)`:

**Battlefield.** Three rows, `8m + 2` columns, in the offset coordinates of `MODEL.md` §2.
For `g = 1, …, m` put `X_g := 8(g−1) + 1` and place

```
e_g   := (X_g,     1)     hex of enemy stack E_g
q_g^1 := (X_g − 1, 1)     LEFT         neighbour of e_g
q_g^2 := (X_g,     0)     TOP-RIGHT    neighbour of e_g
q_g^3 := (X_g,     2)     BOTTOM-RIGHT neighbour of e_g
```

All other hexes are empty. Row 1 is odd, so by `MODEL.md` §2 the six neighbours of
`(X_g, 1)` are `(X_g ± 1, 1)`, `(X_g − 1, 0)`, `(X_g, 0)`, `(X_g − 1, 2)`, `(X_g, 2)`; the
three hexes above are among them, so **all three deployment hexes are directly adjacent to
`E_g`**.

> **Why three rows.** An earlier version of this construction used a single row, as
> Theorem 1 does. That is impossible: in one row a hex has only two neighbours, so a third
> stack cannot reach `E_g` without walking through a hex occupied by an ally — and
> occupied hexes are not enterable (`MODEL.md` §2, `CBattleInfoCallback.cpp:1355-1360`).
> The bug was found by the geometry self-check in `../scripts/brute_force.py`, which
> verifies Lemma 4.1 on the built instance with *all* slots occupied. See
> `../VERIFICATION.md`, iteration 0.

**Player army.** `3m` creature types `C_1, …, C_{3m}`, where

```
att(C_i) = α,  def(C_i) = α,  dmg_min(C_i) = dmg_max(C_i) = a_i,  hp(C_i) = 5,
spd(C_i) = 2,
```

(`def(C_i) = α` is not decoration. Without it the player's defence is unspecified, and for a
large `α` the enemy's single base blow would be multiplied enough to kill a five-hit-point
singleton, so the blanket statement that no player creature dies would not follow. The
reduction survives either way — every player stack delivers its only strike before any
retaliation can land — but the constructed type has to be complete, and a referee found this
missing after an earlier round recorded it as fixed.)

and the stock of `C_i` is **exactly one creature**. Slots: `k = 3m`, with deployment hexes
`q_1^1, q_1^2, q_1^3, …, q_m^1, q_m^2, q_m^3`.

**Defence.** `E_g` is a single creature with `att = α`, `def = α`, `hp = T`,
`dmg_min = dmg_max = 1`, `spd = 1`, `value = 1`, at hex `e_g`.

**Question parameters.** `R = 1`, `W = m`.

Since all `a_i ≤ poly(m)` may be assumed, the construction is polynomial even under unary
encoding of the `a_i`.

### 4.2 Geometry lemma

**Lemma 4.1.** A player stack deployed at any `q_g^r` (`r ∈ {1,2,3}`) can attack `E_g` and
no other enemy stack, in round 1.

*Proof.* Each `q_g^r` is adjacent to `e_g`, so `E_g` is attackable without moving —
in particular no ally can block the approach. For `g' ≠ g`, the columns of group `g` lie in
`{X_g − 1, X_g}` and `e_{g'}` sits in column `X_{g'}`, with `|X_g − X_{g'}| ≥ 8`. Since the
`MODEL.md` §2 distance is at least `|Δ(x + ⌊y/2⌋)| − 1 ≥ 8 − 1 − 1 = 6` between such
columns, and by (†) a player stack reaches at most distance 3, no `q_g^r` reaches
`e_{g'}`. ∎

This lemma is machine-checked on every constructed instance, in the worst case for the
player (all `3m` slots occupied), by `check_geometry_3partition` in
`../scripts/brute_force.py`.

**Lemma 4.2.** In `G₃`, each slot holds at most one creature, and the total damage
inflicted on `E_g` during round 1 is at most `Σ_{i ∈ S_g} a_i`, where `S_g` is the set of
types allocated to the three slots of group `g`. Moreover `E_g` dies in round 1 if and only
if that total reaches `T`.

*Proof.* A slot is homogeneous (`MODEL.md` §9) so it holds creatures of a single type; each
type has stock one, so a slot holds at most one creature. A stack of one creature of type
`C_i` deals at most `a_i` per strike by (★) — exactly `a_i` unless it waited and met a
defending enemy, §2.1 `(‡c)` — and each stack strikes at most once in round 1; under (‡) it
is never attacked, so it never delivers retaliation damage either. By
Lemma 4.1 only the three slots of group `g` can strike `E_g`. Damage accumulates on the
health pool of `E_g` (`MODEL.md` §3), which is a single creature of `T` hit points, so it
dies exactly when the accumulated damage reaches `T`; since that damage is at most
`Σ_{i ∈ S_g} a_i`, death implies `Σ_{i ∈ S_g} a_i ≥ T`, and conversely three non-waiting
strikes summing to `T` meet the un-raised defence (`(‡c)(i)`) and kill. No enemy ever
initiates (`‡a`) and no player creature dies in round 1 (§2), so all three strikes are
available. ∎

### 4.3 Correctness

**Lemma 4.3 (yes ⟹ yes).** If the 3-PARTITION instance is a yes-instance then `G₃` is.

*Proof.* Let `{G_1, …, G_m}` be triples each summing to `T`. Allocate the three types of
`G_g` to the three slots `q_g^1, q_g^2, q_g^3`. Each stack strikes `E_g`; the accumulated
damage is `Σ_{i ∈ G_g} a_i = T`, so `E_g` dies by Lemma 4.2. All `m` enemy creatures die,
value `m = W`. ∎

**Lemma 4.4 (yes ⟸ requires a 3-partition).** If `G₃` is a yes-instance then the
3-PARTITION instance is.

*Proof.* A destroyed value of `W = m` requires all `m` enemy creatures to die, since each
has value 1 and there are `m` of them. Let `S_g` be the set of types allocated to group
`g`'s slots; the `S_g` are pairwise disjoint (each type has stock one) and `|S_g| ≤ 3`. By
Lemma 4.2, `Σ_{i∈S_g} a_i ≥ T` for every `g`. Summing,

```
mT ≤ Σ_{g=1}^{m} Σ_{i∈S_g} a_i ≤ Σ_{i=1}^{3m} a_i = mT,
```

so every inequality is tight: `Σ_{i∈S_g} a_i = T` for all `g`, and the `S_g` cover all
`3m` types. Finally `T/4 < a_i < T/2` forces `|S_g| = 3`: two elements sum to less than
`T`, four to more than `T`. Hence `{S_1, …, S_m}` is a 3-partition. ∎

**Proof of Theorem 2.** Lemmas 4.3 and 4.4, with the construction polynomial under unary
encoding of the `a_i`. Since 3-PARTITION is strongly NP-complete, `ARMY-ALLOCATION` is
strongly NP-hard, and therefore admits no pseudo-polynomial algorithm unless P = NP. ∎

---

## 5. Which mechanics carry the nonlinearity

It is worth being precise about this, because the natural objection to a result of this
kind is that the hardness was smuggled in by the choice of objective.

**5.1 Kill thresholds are not a modelling choice.** The objective counts creatures killed.
One might instead count *hit points removed*; **on this family** the objective would then
be `Σ_j min(a_j, c_j)`, which is concave and separable and is maximised greedily — the
problem becomes trivial, so Theorem 1 does rest on counting kills. That is a fact about
the matching reach structure, not about the objective in general: on the featureless
family of `candidate-C-featureless.md` the hit-point objective remains **strongly
NP-hard** (its §6, machine-checked in `../scripts/verify_hp_objective.py`), a point owed
to the round-4 external review — an earlier draft of this section claimed the hit-point
objective trivializes the whole problem, which is false.

Counting kills is still the right primary objective, and not because it makes a proof
work. In HoMM3 a stack that
survives with one hit point is undiminished: by `MODEL.md` Definition 3.3 its damage output
depends on `count`, which still includes the wounded top creature
(`CUnitState.cpp:282-285`), and by `MODEL.md` §6 it still retaliates and still acts. Hit
points removed from a stack you do not finish buy the player *nothing at all* in that
round. The step function is the game's own accounting, not ours.

**5.2 Superadditivity of the finishing blow.** Combining (K) and (C) with the retaliation
rule gives a strict inequality that is the tactical heart of the game. Let `v(D)` be the
value to the player of dealing `D` damage to an enemy stack of pool `P` and per-round
output `R`. Then over the remaining rounds

```
v(D) = 0                    for D < P        (no kill, full retaliation, full output)
v(D) = value(stack) + R·(rounds remaining) + (retaliation avoided)   for D ≥ P
```

so `v(D₁) + v(D₂) < v(D₁ + D₂)` whenever `D₁, D₂ < P ≤ D₁ + D₂`. Superadditive value under
a shared budget is exactly the structure of KNAPSACK, and it is why "focus fire until a
stack dies, never spread damage" is the first thing a HoMM3 player learns. Our reductions
are, in a sense, a formalisation of that folklore.

**5.3 What the constructions do *not* use.** No spells, no heroes, no morale or luck, no
obstacles, no double-wide creatures, no flying, no shooting, no WAIT, no special abilities,
and a single round. Theorem 1 additionally needs only a one-row battlefield; Theorem 2
needs three rows, for the reason given in §4.1. The hardness survives an aggressive
restriction of the game. That is the strongest form of such a result: it localises the
difficulty in `kills(·)` and the slot-sizing decision, rather than attributing it vaguely
to "the game".

Retaliation is *excluded by the policy* (‡) rather than unused: as §2 records, letting the
defence attack does not destroy the reductions, but it changes the arithmetic and has to be
accounted for. This is worth a sentence in the paper, because it is a place where the
obvious informal argument is wrong.

**5.4 What the constructions *do* need.** Both need the slot's deployment hex to determine
which enemy it can engage. This is a real mechanic — the engine maps slot index to starting
hex (`config/gameConfig.json:635-642`) — but two things must be said plainly.

*First*, the results are about the *joint* decision "how many creatures, in which slot", not
about stack sizing in isolation on a featureless board. That objection is answered, in the
strongest available way, by `candidate-C-featureless.md`: on a board where every slot
reaches every enemy the problem is still strongly NP-hard, and remains so with the
allocation given.

*Second*, and this is a restriction of the model rather than a gap in the proofs: **the
deployment hexes are an input of the generalized problem, not a function of the slot count
the way the shipped game computes it.** The engine's `attackerUnitsLoose` /
`attackerUnitsTight` tables (`config/gameConfig.json:635-642`) place stacks in one or two
fixed columns. `MODEL.md` §9 now states this explicitly: the object studied is a
*generalized battle scenario with prescribed deployment cells*. Theorem 1 and Theorem 2 use
that freedom mildly (a corridor, and three petals per enemy); Theorem 3 uses it heavily.
Proving any version under native formations is left open (§6).

**5.5 A matching upper bound: Theorem 1 is tight.**

> **Proposition.** For the family of instances of Theorem 1 (single creature type,
> `R = 1`, **one creature per enemy stack**, damage under `(★)`, corridor deployment in
> which slot `j` reaches exactly one enemy `E_j`, hold policy `‡`), `ARMY-ALLOCATION` is
> solvable in `O(k·B)` time and `O(B)` space, where `B` is the stock of the single type.

*Proof.* After deployment the play is forced: slot `j` either finishes `E_j` or achieves
nothing (§2, `(★)` and `(†)`; this needs **one creature per enemy stack** — against a
multi-creature stack a non-finishing blow still kills whole creatures and still scores, the
per-slot value is a staircase, and the 0-1 framing fails: round 10 exhibited a
matching-reach corridor with six-creature stacks where the threshold rule returns 0 and the
true optimum is 3). Slot `j` finishes `E_j` iff `c_j · d ≥ t_j`, i.e.
`c_j ≥ b_j := ⌈t_j / d⌉`, and any surplus above `b_j` is wasted. So the optimum is: choose
`S ⊆ [k]` maximising `Σ_{j∈S} v_j` subject to `Σ_{j∈S} b_j ≤ B` — a 0-1 knapsack over `k`
items, solved by the textbook dynamic program over (slot prefix, budget) in `O(k·B)`. ∎

Two consequences, stated carefully. First, *within the corridor family of Theorem 1* the
result is tight: that restriction is weakly NP-complete, admits a pseudo-polynomial
algorithm, and (unless P = NP) cannot be strongly NP-hard there. Second, this disposes of
the apparent contradiction "Theorem 1 gives a DP, Theorem 2 forbids one": the two
statements restrict `ARMY-ALLOCATION` (MODEL.md §9) in different, incomparable ways — two
independent readers tripped over this, so the paper must say it explicitly.

> **What this proposition does *not* license — and what an earlier draft got wrong.** This
> draft used to read the Theorem 1 / Theorem 2 contrast as evidence for a boundary along
> *roster diversity* ("few types easy, many types hard") and recorded that reading as an
> open conjecture. **The conjecture is now refuted.** `candidate-D-singletype.md`
> (Theorem 3) gives a strongly NP-hard family with a **single** creature type, and even
> with the allocation fixed to one creature per slot. What the `O(kB)` dynamic program
> above actually exploits is not a poor roster but a **trivial reach structure**: in the
> corridor family slot `j` engages exactly one enemy and each enemy is engaged by exactly
> one slot, so the reach graph is a perfect matching and the allocation separates into `k`
> independent threshold decisions. Once the reach hypergraph is nontrivial, one type
> suffices for strong hardness. The paper therefore presents Theorem 2 and Theorem 3 as
> **two independent sources of strong hardness** — heterogeneous damage under a trivial
> reach structure, and target selection under a rich one — and claims no dichotomy in
> either direction.

The DP is machine-checked against exhaustive subset enumeration on 2000 random instances
(`../scripts/dp_single_type.py`).

---

## 6. Open problems and known weaknesses

> **Status note.** Two items that this section used to list as open have since been
> settled, both negatively for the "it might get easier" reading:
>
> * **Positionless variant** ("is it still hard if every slot reaches every enemy?") —
>   **answered yes** by `candidate-C-featureless.md`, Theorem 4 and Corollary 4.1. The
>   allocation does decouple, and the hardness simply migrates into the choice of targets.
> * **Single type with general geometry** — **answered yes** by
>   `candidate-D-singletype.md`, Theorem 3 and Corollary 3.1, which also refutes the
>   roster-diversity conjecture formerly stated in §5.5.
>
> What remains open is listed below.

1. **Fixed `k`.** In the shipped game `k = 7`. Both constructions need `k` to grow. For
   fixed `k` the allocation has polynomially many "shapes" but the counts are still
   unbounded integers; we conjecture the problem is in P for fixed `k` and `R = 1`, and
   the proof would be a nice contrast result to include.
2. **Native deployment formations.** All four theorems take the map from slot index to
   deployment hex as *input* (§5.4, `MODEL.md` §9). The shipped game derives it from fixed
   formation tables. Recovering any of the results under native formations is open.
3. **Adversarial defence.** Replacing the scripted `π` by an optimising opponent moves the
   problem out of NP and towards candidate B (`candidate-B-recon.md`).
4. **Approximation.** Theorem 1 gives no inapproximability. The natural question — is the
   destroyed-value objective APX-hard? — is open; the KNAPSACK structure of §5.2 suggests
   a PTAS may exist for `R = 1`, which would itself be a publishable positive result.
5. **Round bound.** All theorems use `R = 1`. Larger `R` should only help hardness, but we
   have not written the argument, and it is not automatic: with more rounds the player can
   re-target, and monotonicity of the objective in `R` needs an argument.

---

## 7. Verification status

Both constructions have been implemented and checked by exhaustive search against the
reference implementation of the mechanics in `../scripts/`. See `../VERIFICATION.md` for
the protocol, the instance families, and the results. No claim in §§3–4 is asserted here
that has not survived that check.
