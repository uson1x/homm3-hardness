# Theorem 3: in-battle targeting is strongly NP-hard with a single creature type

**Canonical merged version.** This document is the single authoritative write-up of the
single-type theorem. It supersedes both of the two independent proofs that preceded it —
this file's own earlier draft and `sol-attempt/PROOF.md` — and follows the merge recipe
recorded in §10: **sol's creature statistics** (enemy defence 27, damage multiplier 0.35,
player hit points 4), **this file's resource lemma** in the general `0 < μ < 1` form,
**this file's geometry** (invariants, forced alternating triple, four adapters, and the
embedding lemma now written out in full), and **both** machine checks, each run with the
pure-movement branch enabled and disabled.

Companion to `../MODEL.md`, which fixes the rules and the citations into the VCMI source,
and to `candidate-A.md`, whose Theorems 1 and 2 this note extends and whose §5.5 conjecture
it refutes. Machine checking: `../scripts/verify_x3c.py` (this file's parameterisation),
`../scripts/crosscheck_sol.py` (the canonical parameterisation), supporting mechanics tests
in `../scripts/test_obstacles.py`.

> **Numbering.** In the paper (`paper/main.md`) the theorems are numbered in the
> pedagogical order Theorem 1 (PARTITION, weak) → Theorem 2 (3-PARTITION allocation) →
> **Theorem 3 (this document)** → Theorem 4 (featureless board,
> `candidate-C-featureless.md`). Earlier drafts called this result "Theorem D"; the letter
> is retired. Local lemma numbers below are local to this document.

---

## 1. Statement

Recall `ARMY-ALLOCATION` from `MODEL.md` §9.

> **Theorem 3.** `ARMY-ALLOCATION` is **strongly** NP-hard, already for instances with
> `R = 1`, a **single creature type** in the player's army, one creature per enemy stack,
> all enemy creatures of one type and value 1, flat damage, no abilities, static impassable
> hexes as the only terrain feature, and the garrison policy `(‡)` of §2.1. With
> `candidate-A.md` Lemma 3.5 (membership in NP) it is strongly NP-complete on this family.

> **Corollary 3.1 (fixed allocation).** The same instances remain strongly NP-hard when the
> allocation is *given* rather than chosen: fix one creature in every slot. Deciding whether
> a fixed, fully deployed single-type army destroys enemy value `W` in one round —
> `BATTLE-PLAY`, as in `candidate-C-featureless.md` Corollary 4.1 — is strongly NP-hard.

**What the corollary is for, and the claim it forbids.** In every yes-instance the winning
allocation is *unique and is the all-ones vector* (Lemma 5.2; machine-confirmed on every
yes-instance in §6). The player therefore has no interesting sizing decision to make: the
budget forces `3q` creatures into `3q` slots, one each. It follows that this theorem must
**not** be advertised as "single-type stack sizing is strongly hard". The honest reading is
Corollary 3.1's:

> the hardness lives in **target selection on the reach hypergraph**, and it survives with
> the roster reduced to one type and the allocation removed from the problem entirely.

That is still exactly what is needed to kill the roster-diversity conjecture of
`candidate-A.md` §5.5 — see §7 — and it is what the paper claims.

**Why this matters here.** `candidate-A.md` proves two things that look like a dichotomy:
Theorem 1 makes the *single-type* problem weakly NP-complete, and §5.5 shows that on the
family Theorem 1 produces there is a matching `O(kB)` dynamic program, so on that family
strong hardness is impossible unless P = NP. Theorem 2 recovers strong hardness but only
with `3m` distinct creature types. It was tempting to read this as "hardness scales with
roster diversity", and §5.5 recorded the temptation as an explicit open conjecture.

Theorem 3 says the conjecture is false. One type suffices for strong hardness. What the
`O(kB)` dynamic program of §5.5 actually needs is not a poor roster but a **trivial reach
structure**: in the corridor family of Theorem 1 slot `j` can engage exactly one enemy, so
the allocation decomposes into independent per-slot decisions and becomes a knapsack. Once
a slot can engage several enemies and several slots can engage the same one, the problem is
hard with a single type and nothing at all to choose but targets. The axis is the reach
hypergraph, not the roster.

Theorem 3 also uses a mechanic neither earlier theorem touches: the **lower clamp on
damage**, `dmg = max(1, ⌊…⌋)` (`DamageCalculator.cpp:576-577`). §3 explains why that clamp
is the whole engine of the proof.

The reduction is from **Planar Exact Cover by 3-Sets**, and it needs static impassable
hexes, which `candidate-A.md` deliberately avoided. That is the price; §8.2 states it plainly.

---

## 2. The instance

**Source problem.** `PLANAR-X3C`: a universe `X` with `|X| = 3q`, a collection `C` of
3-element subsets of `X`, such that the bipartite incidence graph
`G(X, C) = (X ∪ C, {(e, S) : e ∈ S})` is planar. Question: is there `C' ⊆ C` with
`|C'| = q` whose members are pairwise disjoint and cover `X`?

> **Provenance, verified against the source (2026-08-03).** `PLANAR-X3C` is NP-complete by
> Dyer and Frieze, *Planar 3DM is NP-complete*, Journal of Algorithms 7(2):174–184, 1986
> ([doi:10.1016/0196-6774(86)90002-7](https://doi.org/10.1016/0196-6774(86)90002-7)),
> **Lemma 2.2: "Planar X3C is NP-complete"** — stated and proved directly (from Planar
> 1-3SAT, their Lemma 2.1), not via 3DM. Their planarity convention is exactly ours: an
> associated bipartite graph with "a vertex for each element … and each triple", an edge
> for membership, and "we will say that the instance is planar if G is planar" (p. 175,
> read from a scan of the published paper). An earlier version of this note derived planar
> X3C from planar 3DM by the identity map; that detour is sound but unnecessary and has
> been dropped. Two bonuses from the source, both usable: their X3C instances have **every
> element in two or three sets** (p. 178), so the hardness survives that degree
> restriction — our step 1 element paths then have length ≤ 3 — and their Theorem 2.3
> (Planar 3DM) is what the identity argument would have rested on, so nothing is lost.
> The grid-drawing citation is handled in §4.4, step 3.

Given `(X, C)`, build the `ARMY-ALLOCATION` instance `G_3(X, C)`.

**Player army.** One creature type `P`:

```
att(P) = 1,  def(P) = 1,  dmg_min(P) = dmg_max(P) = 1,  hp(P) = 4,  spd(P) = σ,
value(P) = 0,
```

with `σ` the number of hexes of the board (§4), and **stock exactly `3q`**. There are
`k = 3q` slots, one per element `e ∈ X`, with deployment hexes `p_e`.

**Defence.** For each `S ∈ C` one stack `E_S` consisting of **one** creature of type `Q`:

```
att(Q) = 1,  def(Q) = 27,  dmg_min(Q) = dmg_max(Q) = 1,  hp(Q) = 3,  spd(Q) = 1,
value(Q) = 1,
```

placed at hex `z_S`. The enemy policy is `(‡)` of §2.1.

**Question parameters.** `R = 1`, `W = q`.

Every numeric parameter is a constant (1, 3, 4, 27) except `σ`, the stock `3q`, and
`W = q`, all bounded by a polynomial in `|X| + |C|`. So the instance is polynomial even
under **unary** encoding of every number, which is what makes the hardness *strong*.

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
action to the round's `WAIT` phase, which runs after all `NORMAL`-phase activations in
*increasing* speed order (`MODEL.md` §5, `CBattleInfoCallback.cpp:495-519`). `DEFEND`
ends the turn without moving and without attacking (`BattleAction.cpp:41`, dispatched at
`BattleActionProcessor.cpp:693`); it grants `+20 %` defence, an integer bonus with a
floor of `+1` for stacks whose 20 % rounds to zero, lasting until the stack next
receives a turn (`BattleActionProcessor.cpp:168-196`, `BonusDuration::STACK_GETS_TURN`,
removed at `BattleInfo.cpp:676-688`). `(‡)` reads nothing of the state beyond which of
its own two activations this is, is computable in constant time, and so is a legal `π`.
The full definition, its history (review rounds 5–6) and the one-round lemma live in
`candidate-A.md` §2.1; this section restates what this proof uses.

Three consequences, used throughout and in `candidate-A.md` and
`candidate-C-featureless.md` as well:

* **(‡a) No enemy ever initiates an attack**, so no player stack ever delivers retaliation
  damage. Neither `WAIT` nor `DEFEND` moves or strikes. This is the property the
  reductions need, and the reason the policy family was chosen: the first version of
  `candidate-A.md` used an attacking garrison and was wrong for exactly this reason
  (`../VERIFICATION.md`, iteration 1).
* **(‡b) A waiting or defending enemy still retaliates when struck.** Neither action
  consumes the retaliation charge (`MODEL.md` §6). Retaliation is accounted for in
  Lemma 5.1.
* **(‡c) One-round lemma** (`candidate-A.md` §2.1). In round 1: *(i)* the blow of every
  player stack that did not wait lands at its `NORMAL`-phase activation, before any
  enemy's postponed `DEFEND`, and so meets the un-raised defence — regardless of
  relative speeds; *(ii)* the blow of every player stack, waiting or not, deals **at
  most** its nominal damage, since raising `def(Q)` can only lower `f_def`
  (`MODEL.md` §4). A waiting player stack is scheduled in the `WAIT` phase by
  *increasing* speed and can meet a slower enemy's bonus, so for such blows only
  *(ii)* holds; and for `R ≥ 2` the bonus outlives the round boundary — both out of
  scope here, since `R = 1`.

Wherever a statement below quantifies over an *arbitrary* play, it is therefore phrased as
"the damage delivered is at most the nominal damage `D(c)`", never as an equality; the
equality is used only for the constructed witness play of Lemma 5.4, which contains no
`WAIT`. Numerically, in this construction a defending `E_S` has defence
`27 + ⌊27·20/100⌋ = 32`, so `Δ = 1 − 32 = −31`, `0.025·31 = 0.775` is past the cap `0.7`,
and the multiplier drops from `μ = 0.35` to `0.3`. Both lie in `(0, 1)`, which is the only
hypothesis Lemma 3.1 makes — see §3.3.

---

## 3. The resource lemma

By `MODEL.md` §4, with `Δ = att(P) − def(Q) = 1 − 27 = −26 < 0`, the defence advantage is
26 points and `0.025 · 26 = 0.65`, which is **below** the cap `0.7`, so the cap constant
never enters:

```
f_att = 1,        f_def = 1 − 0.025 · 26 = 0.35 =: μ,
```

so a player stack of `c` creatures striking any `E_S` deals

```
D(c) = max( 1 , ⌊ c · 1 · 1 · μ ⌋ ) = max(1, ⌊μc⌋).                            (★)
```

**Lemma 3.1 (Resource lemma).** *Let `0 < μ < 1` and `D(c) = max(1, ⌊μc⌋)`. Let
`c_1, …, c_r ≥ 1` be stack sizes and let stack `i` deliver at most `D(c_i)` damage to one
common target. If the total damage delivered is at least 3, then `Σ_i c_i ≥ 3`, with
equality if and only if `r = 3` and `c_1 = c_2 = c_3 = 1`.*

*Proof.* For `c = 1`, `D(1) = max(1, ⌊μ⌋) = 1 = c`. For `c ≥ 2`, `⌊μc⌋ ≤ μc < c` and
`1 < c`, hence `D(c) < c`. So `D(c) ≤ c` always, with equality exactly at `c = 1`.
Therefore `3 ≤ Σ_i (damage of stack i) ≤ Σ_i D(c_i) ≤ Σ_i c_i`. If `Σ_i c_i = 3` then every
inequality is tight, so `D(c_i) = c_i` for every `i`, so every `c_i = 1`, so `r = 3`. ∎

**3.1 What is really going on.** The lemma is a statement about the **damage floor**. The
engine clamps every strike from below at 1 (`DamageCalculator.cpp:576-577`,
`MODEL.md` §4). A single creature therefore delivers a full point of damage no matter how
badly outclassed it is, while any stack of `c ≥ 2` such creatures delivers strictly fewer
than `c` points. Damage per creature is thus **maximised by splitting into stacks of one**,
which is the exact opposite of the "merge everything" intuition, and it is a real (if
inelegant) HoMM3 tactic. Since a slot is homogeneous and can hold any number of creatures,
the player's allocation decision is precisely: how finely to split, and where.

The rest of the construction turns "splitting is at least as good, and here strictly
better" into "you must split into exactly three, and the three must sit on the three slots
of one 3-set".

**3.2 The concrete numbers.** With `μ = 0.35`, `(★)` gives

```
c    1  2  3  4  5  6  7  8  9  10  11  12
D(c) 1  1  1  1  1  2  2  2  3   3   3   4
```

so a *single* stack needs 9 creatures to deal 3 damage, and *two* stacks need 7
(`6 + 1`), against 3 for three stacks of one. That is a far bigger margin than the proof
needs. Lemma 3.1 is deliberately stated under the weakest hypothesis that still works,
`μ < 1`, rather than for `μ = 0.35`: the conclusion is the same and the hypothesis is immune
to the arithmetic worries of §3.3.

**3.3 Two arithmetic hazards, both dodged.**

*(a) Floating point.* The engine-versus-model cross-check (`../engine-check/REPORT.md`)
found that VCMI's hand-written JSON parser accumulates fractional digits as `0.1·d`
(`lib/json/JsonParser.cpp:536-551`), so the configured defence cap `0.7` is loaded as
`0.7000000000000001`, one ULP high. Any construction that *reaches* the cap therefore lives
in two slightly different arithmetics: at `def(Q) = 41`, which the earlier draft of this
document used, the model computes `D(10) = 3` and the engine `D(10) = 2`. The canonical
constants keep the *undefended* branch clear of the question — `0.65 < 0.7` means an
undefended blow never reads the cap constant, and the damage table above is identical in
both worlds. This is sol's contribution to the merge and it is why his parameterisation was
adopted. The *defended* branch (item (b) below) does cross the cap — `0.025·31 = 0.775` —
and there the boundary can bite; it is absorbed by Lemma 3.1's generality over
`μ ∈ (0, 1)`, not avoided.

*(b) The defending target.* By `(‡c)` a defending `E_S` has multiplier `0.3` rather than
`0.35`. Since Lemma 3.1 is stated for *all* `μ ∈ (0, 1)`, the lemma, and with it the whole
budget argument of §5, holds verbatim under either value; and a waiting player stack, which
is the only stack that can meet a defending enemy, delivers at most `D(c)` either way.
`candidate-A.md`'s constructions dodge both hazards by never invoking the defence factor at
all (`Δ = 0`); this one invokes it and survives, which is a stronger statement.

For the same reason the choice `def(Q) = 27` is not delicate. Any `def(Q) > att(P)` gives
`μ < 1` and the lemma applies; `27` is chosen only so that `0.025 · 26 = 0.65` sits safely
inside the uncapped range with room on both sides.

---

## 4. The board

**Notation.** A hex has six neighbours forming a cycle
`TOP_LEFT, TOP_RIGHT, RIGHT, BOTTOM_RIGHT, BOTTOM_LEFT, LEFT` (`MODEL.md` §2). Call
`{TOP_LEFT, RIGHT, BOTTOM_LEFT}` and `{TOP_RIGHT, BOTTOM_RIGHT, LEFT}` the **alternating
triples**.

The board is specified by four invariants. Everything downstream — §5 in full — uses only
these, never the details of the layout.

> **(I1)** Every enemy hex `z_S` has exactly three free neighbours, and they are pairwise
> non-adjacent. Write them `d_S^e` for `e ∈ S`, one per element of `S`.
>
> **(I2)** The free hexes other than the `z_S` decompose into exactly `3q` connected
> components, one per element; call the component of `e` its **region** `R_e`.
>
> **(I3)** `R_e` contains the deployment hex `p_e` and exactly the dockings `d_S^e` for the
> `S ∈ C` with `e ∈ S`, and no other hex adjacent to any enemy; each `d_S^e` is adjacent to
> `z_S` and to no other enemy hex. Moreover `p_e` has exactly one free neighbour.
>
> **(I4)** `σ ≥ |R_e|` for every `e`.

**Lemma 4.1 (Reach).** *Under (I1)–(I4), at the start of the battle the stack deployed in
slot `e` can strike exactly the enemies `E_S` with `S ∋ e`, and for each such `S` its only
legal approach hex is `d_S^e`.*

*Proof.* Every hex outside `R_e` that is adjacent to `R_e` is either impassable or holds a
living enemy, and neither is enterable (`MODEL.md` §2,
`CBattleInfoCallback.cpp:1355-1360`): by (I2) the regions are the connected components of
the free hexes once the enemy hexes are removed, so the only free non-region neighbours of
`R_e` are enemy hexes. The BFS of `MODEL.md` §5 from `p_e` therefore cannot leave `R_e`.
Each region holds exactly one player stack by (I2)+(I3), so no ally blocks the walk, and by
(I4) the whole of `R_e` is within movement range. `WALK_AND_ATTACK` needs a free hex
adjacent to the target; by (I3) the only hexes of `R_e` adjacent to an enemy are the
`d_S^e`, and `d_S^e` is adjacent only to `E_S`. ∎

**Lemma 4.2 (Alternating triples).** *The only pairwise non-adjacent 3-subsets of a hex's
six neighbours are the two alternating triples.*

*Proof.* Consecutive neighbours on the ring are adjacent to each other, in both row
parities; a 3-subset of a 6-cycle with no two consecutive members is an alternating triple.
∎ (Machine-checked for both parities in `test_obstacles.py`.)

So (I1) is not a design choice but a constraint: an enemy that three stacks must reach
simultaneously, while their regions stay separated, *must* present an alternating triple.
This is the one place where the hex geometry does real work, and it is why the construction
would not transfer unchanged to a square grid.

### 4.1 The gadgets

**Enemy gadget** for `S ∈ C`, anchored at `(X, Y)` with `Y` **even**:

```
z_S      = (X,   Y)        the enemy stack
d^1      = (X,   Y−1)      TOP_LEFT
d^2      = (X+1, Y)        RIGHT          the alternating triple
d^3      = (X,   Y+1)      BOTTOM_LEFT
impassable: (X+1, Y−1), (X+1, Y+1), (X−1, Y)      the other three neighbours
```

Drawn on the offset grid (even rows sit half a column to the right — the figure below has
`Y` even, so rows `Y±1` sit half a column left), with `#` impassable:

```
   row Y−1        d¹ #
   row Y        #  z  d²
   row Y+1        d³ #
```

The three dockings sit at 120° from one another. Each is adjacent to `z_S` and to nothing
else in the gadget, so a stack that walks in along one arm cannot slip round to another.

**Element gadget** for `e`: a connected region of free hexes with a two-hex stub at its end,
`p_e` on the outer hex (step 5 of Lemma 4.4 spells out why two hexes: the outer one then has
exactly one free neighbour). The stub gives the second half of (I3): a stack standing on a
hex with a single free neighbour is never on a path between two other hexes, so it can block
nothing.

**Corridors** connect `d_S^e` to `R_e`. They are hex paths, laid so that no hex of one
region is adjacent to a hex of another region or to an enemy hex other than at its own
docking.

**Lemma 4.3 (Adapters).** *An orthogonal drawing delivers the three edges of a set-vertex
along three of the four axis directions, and which three is not ours to choose; the three
dockings, by Lemma 4.2, are fixed. The gap is bridged by a constant-size box. For each of
the four possible triples of incoming directions there is a `9 × 9` pattern in which three
pairwise non-touching paths run from the three used boundary midpoints to the three
dockings, each path meeting `z_S` only at its final hex, and the unused boundary midpoint
is not used at all.*

*Proof.* Exhibited, one pattern per case, in `ADAPTERS` in `../scripts/verify_x3c.py`, and
checked there mechanically: each arm is a path, starts at its port, ends at a distinct
member of the alternating triple, touches the enemy only at its last hex, no two arms share
or touch a hex, and the unused port is untouched. The three arms are matched to the three
dockings in cyclic order, which is what makes the routing planar inside the box;
concretely, when the LEFT direction is used, its arm dips one row off the centre line
before reaching `TOP_LEFT` or `BOTTOM_LEFT`, and the arm that would otherwise want `RIGHT`
swings around the box. ∎

The box is `9 × 9` with the enemy at its centre; in local coordinates the enemy sits at
`(4, 4)` with row 4 **even**, and the four boundary midpoints ("ports") are `(4,0)` top,
`(8,4)` right, `(4,8)` bottom, `(0,4)` left. The parity of the local frame matters and is
discharged in Lemma 4.4, step 5.

### 4.2 Lemma 4.4: the embedding, in full

This is the step that a referee should read with a pencil, and it is the step the earlier
drafts of both proofs left as a sketch. It is written out here.

**Lemma 4.4 (Embedding).** *Let `(X, C)` be a `PLANAR-X3C` instance with `N = |X| + |C|`.
In time polynomial in `N` one can compute either*

* *a hex board of polynomial size (`O(N²) × O(N²)` hexes suffices, from the `O(N²)`
  drawing area of step 3), a set of impassable hexes, enemy hexes `z_S`
  (`S ∈ C`) and deployment hexes `p_e` (`e ∈ X`) satisfying (I1)–(I4), or*
* *a fixed no-instance `G_no` of `ARMY-ALLOCATION` (say: a `1 × 1` board, one slot, one
  creature of stock one, no enemies, `W = 1`), emitted only when the given instance is
  malformed or fails one of the polynomial-time no-certificates listed in step 0 —
  `|X|` not divisible by 3, an element lying in no set, or a failed planarity test.*

> **"Only when", not "exactly when".** An earlier version of this statement said `G_no` is
> emitted *exactly* when the source is a no-instance. That would be a decision procedure for
> `PLANAR-X3C`, which is precisely what the reduction is not allowed to be. The correct
> statement is one-directional: every input sent to `G_no` is certifiably a no-instance, but
> most no-instances are **not** sent there — they get an ordinary board whose game answer is
> no, which is exactly what a many-one reduction should do. The verifier builds 14 such
> boards for genuine no-instances (`../scripts/verify_x3c.py`, 17 yes / 14 no), so this is
> observable, not merely asserted.

*The second branch is what makes the map a **total** many-one reduction: a Karp reduction
must output a target instance on every source encoding, so detected no-conditions map to
`G_no` rather than to a bare verdict — a round-4 review correction to the earlier
statement, which output "no" as a verdict.*

The proof is in six steps. Steps 1–2 are graph surgery, step 3 quotes the drawing
literature, steps 4–6 are the hex-level construction, where all the adjacency bookkeeping
lives.

#### Step 0: degenerate inputs

Delete repeated members of `C`: a duplicate copy of a 3-set is never needed by an exact
cover (any cover using one copy uses no other), so the answer is unchanged, and afterwards
`G(X, C)` is a simple graph. If `|C| < q`, or if some `e ∈ X` lies in no member of `C`
(an *isolated element*), no exact cover exists and we output the fixed no-instance `G_no`.
Otherwise every set-vertex of `G` has degree exactly 3 and every element vertex has degree
`d_e ≥ 1`.

Compute a combinatorial planar embedding of `G` — a rotation system, i.e. the cyclic order
of the incident edges around each vertex, together with a choice of outer face — in linear
time (Hopcroft–Tarjan planarity testing with embedding, or Boyer–Myrvold, which returns the
embedding directly). If `G` is not planar the encoding is not a `PLANAR-X3C` instance; two
clean conventions exist — define `PLANAR-X3C` instances as carrying a valid planar
embedding, or define the language on all X3C encodings with nonplanar encodings outside the
restricted language — and under either we map the offending encoding to the fixed
no-instance `G_no`, which keeps the reduction total (under the second convention a
nonplanar encoding is a no-instance of the restricted language by definition, so `G_no` is
the correct image). The machine check treats that case by refusing to emit a board (§6).

#### Step 1: degree reduction that preserves the rotation

Replace every element vertex `e` of degree `d_e = d` by a path

```
v_e^1 — v_e^2 — … — v_e^d          (the element path of e)
```

of `d` new vertices, and attach the `i`-th incident edge of `e` to `v_e^i`, where the
incident edges are indexed in the cyclic order given by the embedding, starting at an
arbitrary one. Call the result `G'`.

*Claim: `G'` is planar, `Δ(G') ≤ 3`, and a planar embedding of `G'` extending the given
embedding of `G` outside a small disc around each `e` is computable in linear time.*

Degrees: a set-vertex is untouched and has degree 3; an interior path vertex has two path
neighbours and one incidence edge, hence degree 3; a path endpoint has degree 2 (or 1 if
`d = 1`).

Embedding: fix a closed disc `Δ_e` around `e` meeting no other vertex and meeting the
incident edges in `d` initial segments only. The boundary circle `∂Δ_e` meets those segments
at points `b_1, …, b_d`, and by the definition of the rotation system they occur in this
cyclic order along `∂Δ_e`. Cut `∂Δ_e` open at a point of the arc between `b_d` and `b_1` and
straighten the disc to a rectangle whose *top* side carries `b_1, …, b_d` in left-to-right
order. Draw the path `v_e^1 … v_e^d` as a horizontal segment across the middle of the
rectangle, with `v_e^i` directly below `b_i`, and join each `v_e^i` to `b_i` by a vertical
segment. The `d` vertical segments are pairwise disjoint and meet the horizontal one only
at their own endpoints, so the picture inside the rectangle is plane; outside `Δ_e` nothing
changed, and the cyclic order in which edges cross `∂Δ_e` is exactly what it was. Hence the
drawing of `G'` is plane, and it induces a rotation system computable in `O(d)` time per
vertex. This is the point the review asked to be proved rather than asserted: the *cyclic*
order of the incidence edges around `e` becomes the *linear* order along the path, and the
cut is made in a face corner, so no crossing is created.

Sizes: `|V(G')| = Σ_e d_e + |C| = 3|C| + |C| = 4|C|`, and
`|E(G')| = 3|C| + Σ_e (d_e − 1) = 6|C| − |X|`. Both are `O(N)`.

#### Step 2: connected components

`G'` may be disconnected — `G` need not be connected, and after step 0 it still need not
be. Let `G'_1, …, G'_t` be its connected components, with `n_1, …, n_t` vertices,
`Σ_i n_i = 4|C|`. Every component contains at least one set-vertex, because every element
path vertex carries an incidence edge.

Run steps 3–6 on each component separately, obtaining boards `B_1, …, B_t` of sizes
`W_i × H_i` with `W_i, H_i` polynomial in `n_i` — `O(n_i²)` from the drawing area bound of
step 3, times the constant scale factor `λ` of step 4; step 3 does **not** give `O(n_i)`
sides, see the correction there. Then **pack**: place `B_1, …, B_t` left to right, in a
board of width `Σ_i (W_i + 2) + 2` and height `4 + max_i H_i` (the `t − 1` internal
two-wide strips contribute `2(t−1)` and the two-thick border contributes 4 on each axis;
the `O(N²)` bound is unaffected), separated by vertical strips of
impassable hexes two hexes wide, and surrounded by an impassable border two hexes thick. A
hex of `B_i` and a hex of `B_j` (`i ≠ j`) then differ by at least 2 in the column
coordinate, and two hexes at `L∞` distance ≥ 2 are never adjacent (every hex neighbour
differs by at most 1 in each coordinate, `MODEL.md` §2). So no invariant can be violated
across blocks, and each `R_e` stays inside its own block. The packed board has sides
`Σ_i (W_i + 2) = O(Σ_i n_i²) = O(N²)` and `2 + max_i H_i = O(N²)` — polynomial, which is
all the reduction needs.

Rows must stay even where the gadgets need them even; the vertical offset of every block is
therefore chosen even, which the two-hex border allows.

> **Implementation note (third substitution).** `planar_embed.py` packs one level earlier
> than this step prescribes: the component *drawings* are placed side by side with two
> empty grid columns between them and scaled once, so features of distinct components end
> at `L∞` distance ≥ `2λ − 2ρ = 32 ≥ 2` by the separation inequality of step 4, and the
> default-impassable hexes between them form exactly the strips above. Disclosed in the
> paper's Appendix D.6; (SEP′) measures every cross-component feature pair directly.

#### Step 3: an orthogonal grid drawing

We need, for a connected plane graph `H` with `Δ(H) ≤ 4` on `n` vertices, a drawing with:

> **(D1)** every vertex at a distinct point of `ℤ²`;
> **(D2)** every edge a rectilinear path in the grid between its endpoints, leaving each
> endpoint along one of the four axis directions, and using each (vertex, direction) pair
> at most once;
> **(D3)** two edge paths meet only at a shared endpoint, and no edge path passes through a
> vertex;
> **(D4)** all coordinates bounded by a polynomial in `n`;
> **(D5)** computable in time polynomial in `n`.

We need nothing else — not bend-minimality, not area optimality, not preservation of the
step-1 embedding (the reduction's correctness never refers to it again). Two standard
results supply (D1)–(D5); either suffices.

* **Valiant's grid embedding.** Every planar graph of maximum degree 4 with `n` vertices can
  be embedded in a grid of area `O(n²)` with vertices at grid points and edges as
  internally disjoint rectilinear paths. L. G. Valiant, *Universality considerations in VLSI
  circuits*, IEEE Transactions on Computers C-30(2):135–140, 1981. This is the citation
  normally used for exactly this situation, and it carries no connectivity hypothesis.
* **Orthogonal drawings with few bends.** Tamassia and Tollis, *Planar grid embedding in
  linear time*, IEEE Transactions on Circuits and Systems 36(9):1230–1234, 1989; and Biedl
  and Kant, *A better heuristic for orthogonal graph drawings*, Computational Geometry
  9(3):159–180, 1998, which gives an `n × n` drawing with at most `2n + 2` bends in linear
  time for **connected** planar graphs of maximum degree 4. Step 2 has already reduced us
  to the connected case, which is why that hypothesis costs nothing here; the review's
  question "which theorem covers connected but non-biconnected degree-4 plane graphs" is
  answered by Biedl–Kant, and, independently of it, by Valiant.

> **Citation status (updated 2026-08-03).** The operative citation is now
> **Tamassia–Tollis 1989** alone, via the exact statement in the *Handbook of Graph
> Drawing and Visualization*, ch. 7 (Duncan–Goodrich, hosted by Tamassia), Theorem 7.3:
> *"Let G be a 4-plane graph. If G is biconnected, there exists an orthogonal grid drawing
> of G using O(n²) area with at most 2n + 4 bends and where only two edges have more than
> two bends. If G is connected, the number of bends is 2.4n + 2 and no edge has more than
> four bends."* — in linear time, credited explicitly to [TT89]. The **connected** case is
> the one used here (step 2 reduces to connected components; `Δ(G') ≤ 3 ≤ 4`), and an
> orthogonal grid drawing of a plane graph gives (D1)–(D5) directly: distinct grid points,
> rectilinear non-crossing edge paths, polynomial area, polynomial time; (D2)'s
> one-direction-per-edge-end is forced by degree ≤ 4 orthogonality. Caveat, stated
> honestly: the primary IEEE text is paywalled and was verified through this authoritative
> secondary statement, not read in the original. Valiant and Biedl–Kant are demoted to
> non-load-bearing alternatives (round 4 found the Biedl–Kant abstract also covers
> nonplanar graphs and doubted the exact statement attributed to Valiant).
>
> **Update 2026-08-17.** The abstract of the IEEE original was obtained as recorded in a
> bibliographic index (the OpenAlex record of the journal page, reconstructed from the
> record's inverted word index — not the publisher's own text) and states verbatim: an
> `O(n)`-time algorithm producing planar grid embeddings with "(1) the total number of
> bends is at most 2.4n+2; (2) the number of bends along each edge is at most 4; (3) the
> length of every edge is O(n); (4) the area of embedding is O(n²)". Every number the
> construction relies on thus matches an independent record of the primary abstract. The
> abstract does **not** state the connectivity hypothesis — that the `2.4n + 2` bound is
> for connected graphs still rests on the Handbook alone. Also still unread: the paywalled
> proof body and the biconnected `2n + 4` refinement — the latter is not used here.

Apply the chosen algorithm to the component, obtaining a drawing `Γ` of polynomial size.
The cited theorem gives `O(n²)` **area**, which does not by itself bound either side by
`O(n)`; an earlier version of this step asserted a `g × g` grid with `g = O(n)`, which does
not follow. We do not need it. Enclose `Γ` in its bounding box and write `g` for the larger
side, so `g = O(n²)` in the worst case. Every claim below uses only that `g` is polynomial in
`n`, so a board of `O(g) × O(g) = O(n²) × O(n²)` hexes is still polynomial and the unary speed
`σ` is still polynomial. Strong NP-hardness is unaffected.

#### Step 4: scaling, and the separation inequality

Let

```
λ := 20   (the scale factor, even)          ρ := 4   (the gadget-box radius)
```

and map the drawing into hex coordinates by

```
Φ(i, j) := (λ·(i − i_min) + μ , λ·(j − j_min) + μ),     μ := 6.
```

Here `(i_min, j_min)` is the lower-left corner of `Γ`'s bounding box, so the image coordinates
start at `μ` and the construction is translation-invariant. **The offset `μ` must exceed the
gadget radius `ρ = 4`, and an earlier version used `μ = 2`, which is a genuine failure of the
construction rather than a cosmetic detail:** a legal normalized drawing with a vertex at
`(0,0)` maps to `(2,2)`, and the `9 × 9` box centred there extends to `(−2, −2)`, off the
board. With `μ = 6` every gadget box lies at coordinates `≥ 2`, and `μ` is even so the parity
argument below is untouched (`λ` is even, so `λ·(j − j_min) + μ` is even exactly when `μ` is).

Every image row `λ·(j − j_min) + μ` is **even**, because `λ` and `μ` are both even. Fill in
each drawn edge: a unit
segment of `Γ` from `(i,j)` to `(i±1,j)` or `(i,j±1)` becomes the `λ+1` hexes on the
corresponding axis-aligned run between the images of its endpoints. This is legitimate
because **the 4-neighbour square grid is a subgraph of hex adjacency in both row parities**:
`(x,y)` is adjacent to `(x±1,y)` always, and to `(x,y±1)` always — from an even row the
lower neighbours are `(x,y+1)` and `(x+1,y+1)`, from an odd row `(x−1,y+1)` and `(x,y+1)`,
and `(x,y+1)` occurs in both (`MODEL.md` §2; machine-checked for both parities in
`test_obstacles.py`).

Write `img(F)` for the set of hexes covered by a drawn feature `F` (a vertex point or a
filled edge path).

**Separation.** Regard `Γ` as a subset of the plane: the union of its vertex points and its
edge paths, each path a union of closed unit segments with integer endpoints. Two features
of `Γ` that share no point are at Euclidean-`L∞` distance at least 1, since all their
segments lie on integer grid lines and have integer endpoints; distinct vertex points are
likewise at distance at least 1. Because `Φ` scales distances by exactly `λ`,

```
F ∩ F' = ∅   in Γ    ⟹    L∞-dist( img(F), img(F') ) ≥ λ = 20.               (SEP)
```

Now replace, in step 5, a `(2ρ+1) × (2ρ+1)` box around each vertex image by a gadget, and
truncate every corridor at the boundary of the boxes at its two ends. Every hex of a gadget
box is within `L∞` distance `ρ` of its vertex image. Hence for two *non-incident* features
— two boxes of distinct vertices, or a box and the corridor of an edge not incident to that
vertex, or two corridors of edges sharing no endpoint —

```
L∞-dist ≥ λ − 2ρ = 20 − 8 = 12 ≥ 2,                                          (SEP′)
```

and two hexes at `L∞` distance at least 2 are never adjacent. **This is the inequality the
earlier draft got wrong**: with `λ = 9` and `ρ = 4` the same computation gives
`9 − 8 = 1`, and two boundary cells of unrelated boxes can indeed end up hex-adjacent.
`λ = 20` is not tight — `λ = 10` already gives `10 − 8 = 2` — but it is even, comfortable,
and leaves the straight run computed next.

Two corridors *incident to the same box* leave it through different ports. Outside the box
each runs straight along its own axis for at least `λ − ρ = 16` hexes before the first
possible bend (a bend of `Γ` occurs at a grid point, whose image is at distance ≥ `λ` from
the vertex image). Two straight runs leaving one centre along perpendicular axes are at
`L∞` distance `t` at parameter `t`, and along opposite axes at distance `2t`; since they are
truncated at `t = ρ = 4`, the closest they come outside the box is `L∞` distance 4 ≥ 2, so
they never touch. Two corridors incident to the same box and running to the *same* port
cannot occur, by (D2).

#### Step 5: the gadget boxes

*Set-vertex `S`.* Its image `Φ(v_S)` sits on an even row. Replace the `9 × 9` box around it
by the Lemma 4.3 adapter for the triple of axis directions along which `Γ` delivers the
three incident edges. Its centre becomes `z_S`; the three arms are free and are assigned to
the three elements of `S` according to which port each element's corridor arrives at; every
other hex of the box, including the unused port, is impassable.

*Parity.* Lemma 4.3's pattern is stated in a local frame whose row 4 is even. The
translation taking the local frame to the board is `(x, y) ↦ (X − 4 + x, Y − 4 + y)` with
`Y = λ·(j − j_min) + μ` even (both `λ` and `μ` are even), so the row shift `Y − 4` is even.
Hex adjacency in offset coordinates
depends on the row parity and is invariant under column translation (`MODEL.md` §2), so an
even row shift and any column shift carry the pattern over verbatim, adjacency for
adjacency. This is why `λ` was chosen even.

*Element-path vertex `v_e^i`.* Its degree in `G'` is at most 3, so at least one of the four
axis directions is unused at it. Let `U` be the set of used directions. The free hexes of
its box are the union of the axis segments from the centre out to the used ports, together
with the centre: a "plus" with `|U| ≤ 3` arms. It is connected, contained in the box, and
meets the box boundary exactly at the used ports. Adjacencies *inside* the plus are
irrelevant — every hex of it belongs to the single region `R_e` — which is exactly why the
set-vertex needs a hand-built adapter and the element vertex does not.

*The deployment stub `p_e`* (the point the review asked to be spelled out). Take the first
vertex `v_e^1` of `e`'s element path and one axis direction `u` unused at it; such a `u`
exists because `deg(v_e^1) ≤ 2`. Declare free the two hexes at distance 1 and 2 from the
centre along `u`, and set `p_e` to be the one at distance 2. Then:

* `p_e` is connected to the plus through the hex at distance 1, so it lies in `R_e`;
* the hex at distance 1 is not adjacent to any hex of another region, since everything
  outside the box is at distance ≥ 12 by (SEP′) and the rest of the box is `R_e` itself;
* `p_e` has **exactly one** free neighbour, which is the second half of (I3). Every free hex
  of the box other than the two stub hexes lies on one of the four axes through the centre,
  at distance 1 to 4 from it. Take `u = RIGHT` for concreteness (the other three directions
  are symmetric under the reflections that preserve row parity, and the vertical case is
  checked below): `p_e = (X+2, Y)` with `Y` even, whose six neighbours are `(X+1, Y)`,
  `(X+3, Y)`, `(X+2, Y±1)` and `(X+3, Y±1)`. Of these, `(X+1, Y)` is the stub's other hex
  and is free; `(X+3, Y)` lies on the `u`-axis beyond `p_e` and is impassable, since the
  stub is two hexes long and `u` carries no corridor; and the remaining four lie in rows
  `Y ± 1`, where the free hexes of the box are at most the two vertical-axis cells
  `(X, Y ± 1)`, each at `L∞` distance 2 from every one of them. For a vertical `u`, say
  `p_e = (X, Y+2)`, the neighbours are `(X ± 1, Y+2)`, `(X, Y+1)`, `(X+1, Y+1)`,
  `(X, Y+3)` and `(X+1, Y+3)`; rows `Y+1` and `Y+2` contain no free hex except the two
  stub hexes `(X, Y+1)` and `p_e` itself, since the horizontal arms lie on row `Y` and the
  direction `u` carries no arm; and `(X, Y+3)`, `(X+1, Y+3)` lie beyond the two-hex stub
  and are impassable.

Nothing else on the board is within distance 12 of the stub, so it creates no adjacency
anywhere else.

#### Step 6: closing the board

Declare impassable every hex not made free in steps 4–5. Set `σ` to the number of hexes of
the (packed) board. This is legal: creature statistics are part of the input in the
generalised game (`MODEL.md` §1).

**Verification of the invariants.**

*(I1).* By step 5 the free neighbours of `z_S` are exactly the three arm ends, i.e. the
alternating triple `{TOP_LEFT, RIGHT, BOTTOM_LEFT}` of the adapter, pairwise non-adjacent by
Lemma 4.2 and by the direct check in `verify_x3c.py`. No hex outside the box is adjacent to
`z_S`, by (SEP′).

*(I2).* Fix `e`. The set of free hexes assigned to `e` is: the plus of every `v_e^i`, the
corridors of the `d_e − 1` path edges of `e`, the corridors of the `d_e` incidence edges at
`e`, the adapter arms ending at the dockings `d_S^e`, and the stub. The path-edge corridors
join consecutive pluses, so the pluses form one connected set; each incidence corridor joins
one plus to one adapter arm; the stub hangs off the first plus. Hence `R_e` is connected.
Distinct `R_e, R_{e'}` never touch: their features are non-incident in `Γ` (elements are
non-adjacent in `G'`, so no edge of `Γ` joins them, and their vertex boxes are distinct),
so (SEP′) applies; the only place where hexes of different elements come close is *inside*
an adapter box, where Lemma 4.3 has checked that the three arms are pairwise non-touching.
Every free non-enemy hex belongs to exactly one element, so the number of components is
exactly `|X| = 3q`.

*(I3).* `R_e` contains `p_e` by construction. Its hexes adjacent to an enemy are exactly the
arm ends `d_S^e` for `S ∋ e`: inside `S`'s box only the last hex of each arm touches `z_S`
(Lemma 4.3), and every hex outside `S`'s box is at distance ≥ 12 from `z_S` by (SEP′), so it
touches no enemy at all. Each `d_S^e` touches `z_S` and, by (SEP′) again, no other enemy.
The stub gives the last clause, as shown in step 5.

*(I4).* `σ` is the hex count of the board, which is at least `|R_e|`. ∎

**What is and is not machine-checked here.** Lemma 4.2 (the forced alternating triple),
Lemma 4.3 (the four adapters), and the square-grid-inside-hex-adjacency fact used in step 4
are machine-checked. The invariants (I1)–(I4) are machine-checked *on every board the
verifier builds*, and there are two board sources. The compact router (placement by
hill-climbing, corridors by BFS with clearance) feeds the big game-level suites; through it
the lemma's *conclusion* has been exercised on 31 (default) and 55 (`--full`) machine-built
boards, and the router reports failure rather than emitting a board that violates the
invariants. Since round 8 the algorithm of Lemma 4.4 is also implemented step by step —
`embed_lemma.py` is steps 0–6 with the literal constants `λ = 20`, `ρ = 4`, on top of the
planarity and drawing machinery of `planar_embed.py` — with three subroutine substitutions,
disclosed in the paper's Appendix D.6: the planarity test is
Demoucron–Malgrange–Pertuiset rather than the linear-time algorithms step 0 cites, the
drawing is a from-scratch st-ordered visibility construction for degree ≤ 3 rather than
[TT89] as quoted in step 3, and step 2's packing of finished boards is realized at the
drawing level (components' drawings side by side, two empty grid columns between them, so
`2λ` hexes after scaling — covered by the same separation inequality and measured
directly by (SEP′) on every cross-component feature pair). All three are legitimate
because the proof consumes only (D1)–(D5), polynomial time and the separation inequality,
and `validate_drawing` machine-checks the drawing properties on
every build. `verify_embedding.py` runs every corpus family through the algorithm: every
board built passes (I1)–(I4) and the feature-based (SEP′) separation check, every skip carries a
certificate re-verified against the instance (non-planarity is the DMP test's own verdict,
cross-checked by a planted non-planar control), and on the smallest boards the full game
search agrees with X3C end-to-end under the historical and the published constants. What
remains a hand proof is the universal claim — that the algorithm succeeds on *every*
planar instance. §6 states this again where it matters.

### 4.3 Speed

`σ` equals the hex count, which is legal and convenient: it makes (I4) trivial and removes
any need to equalise corridor lengths, which was the reviewer's main worry about this route.
The coupling of speed with initiative (`MODEL.md` §5) is harmless here: `σ > 1 = spd(Q)`, so
every player stack precedes every enemy stack even within the `NORMAL` phase — although
`(‡c)(i)` no longer needs it, since under `(‡)` every enemy's terminal `DEFEND` sits in
the `WAIT` phase regardless of speeds (§2.1).

---

## 5. Correctness

Throughout, fix a feasible allocation `c : X → ℤ_{≥0}` with `Σ_e c_e ≤ 3q` and an arbitrary
play of round 1 by the player against `(‡)`.

**Lemma 5.1 (No interference from the defence).** *No player creature dies during round 1,
and every player stack gets its action.*

*Proof.* Under `(‡)` the defence never initiates (`‡a`). An enemy retaliates only when
struck, at most once per round (`MODEL.md` §6, and `(‡b)`), and its strike deals
`max(1, ⌊1 · 1 · f⌋) = 1` damage since `att(Q) = def(P) = 1` gives `Δ = 0` and `f = 1`. A
player stack of `c ≥ 1` creatures of 4 hit points absorbs 1 damage without losing a
creature, and by `MODEL.md` Definition 3.3 its effective count is unchanged. Each player
stack strikes at most once, so it receives at most one retaliation. Every living stack acts
once per round (`MODEL.md` §5), whichever phase it acts in. ∎

**Lemma 5.2 (Budget).** *Let the play kill `t` enemies. Then `t ≤ q`. If `t = q` then
`Σ_e c_e = 3q`; every slot holds exactly one creature; every deployed stack strikes, and
strikes an enemy that dies; and each dead enemy is struck by exactly three distinct
one-creature stacks.*

*Proof.* Each enemy is a single creature of 3 hit points, so it dies exactly when 3 damage
has accumulated on it (`MODEL.md` §3), and that damage comes only from the stacks that
struck it. A stack **strikes** at most once per round -- a stack that has performed
`WALK_AND_ATTACK` has ended its turn, and `WAIT` defers a stack's turn without granting it a
second strike (`MODEL.md` §5) -- so the sets of strikers of distinct enemies are disjoint.
(The weaker phrasing "a stack acts once per round" is false under `WAIT`, which is why the
argument is run on strikes throughout.) Let `K` be the set of dead enemies, `|K| = t`, and for `S ∈ K` let `A_S` be its
strikers. By `(‡c)` the blow of a stack of `c` creatures delivers at most `D(c)` damage, so
Lemma 3.1 applied to `(c_a)_{a ∈ A_S}` gives `Σ_{a ∈ A_S} c_a ≥ 3`. Summing over the
disjoint `A_S`,

```
3t ≤ Σ_{S ∈ K} Σ_{a ∈ A_S} c_a ≤ Σ_e c_e ≤ 3q,                                 (†)
```

whence `t ≤ q`. Suppose `t = q`, so every inequality in `(†)` is tight.

The middle inequality is tight, so **every allocated creature sits in a stack that struck a
member of `K`**: the sum `Σ_e c_e` counts every allocated creature once, the double sum
counts exactly those in the striker stacks of `K`, and the two agree.

The first inequality is tight together with `Σ_{a ∈ A_S} c_a ≥ 3` for each `S`, so
`Σ_{a ∈ A_S} c_a = 3` for every `S ∈ K`; the equality case of Lemma 3.1 then gives
`|A_S| = 3` and `c_a = 1` for each of the three.

Hence the `3q` creatures allocated sit in exactly `3q` stacks of one creature. A stack
occupies one slot and there are exactly `3q = k` slots, so **every slot holds exactly one
creature** and every one of them struck a member of `K`. ∎

> **A sentence the earlier draft got wrong.** It argued that "a slot left empty or a stack
> that passed would contribute to `Σ_e c_e` and not to the left-hand side". An empty slot
> contributes nothing to `Σ_e c_e` either, so that is not the argument. The correct
> argument is the counting one above: tightness forces `3q` distinct singleton striker
> stacks, and there are exactly `3q` slots to hold them.

Note that Lemma 5.2 uses no geometry whatsoever.

**Lemma 5.3 (Confinement).** *In the situation of Lemma 5.2, when the stack of slot `e`
takes its action, every enemy `E_S` with `S ∋ e` is still alive. Consequently, by the
argument of Lemma 4.1, that stack can strike only enemies `E_S` with `S ∋ e`.*

*Proof.* Induction on the realized order of **terminal actions** — the single move,
attack, or defend each stack performs. That order is fixed by `MODEL.md` §5 — phase, then
speed, then side, then slot — with a stack that issues `WAIT` taking its terminal action at
its later position in the `WAIT` phase; the argument uses only that each stack takes
exactly one terminal action in the round, at one position in that order.

Suppose the claim holds for every stack that acted before slot `e`. Then every strike so far
was delivered from a docking of the striker's own region: by (I3) the only hexes of `R_a`
adjacent to an enemy are `a`'s own dockings, and by the inductive hypothesis every earlier
striker was still confined to its region when it moved, because all enemies bounding that
region were alive at that moment.

Let `E_S` be any enemy already dead, and suppose `e ∈ S`. By Lemma 5.2 every stack in play
holds one creature and so delivers at most `D(1) = 1` damage; since `E_S` has 3 hit points
and is struck by exactly three stacks over the round, each of those three blows delivers
exactly 1 and `E_S` dies on the third, so all three strikers have already acted. Each struck
from a hex adjacent to `z_S`, and two stacks cannot occupy one hex, so those three hexes are
the three free neighbours of `z_S`, i.e. `d_S^{e'}` for the three `e' ∈ S`, one each. By the
previous paragraph the stack that struck from `d_S^{e'}` is the stack of slot `e'`. In
particular the stack of slot `e` is among them, so it has already acted — contradicting that
it is acting now. Hence no `E_S` with `S ∋ e` is dead, the boundary of `R_e` is intact, and
Lemma 4.1 applies unchanged. ∎

> **Why this lemma is needed at all.** A dead unit stops blocking its hex
> (`homm3_model.py:271`, transcribing `CBattleInfoCallback.cpp:1355-1360`; pinned down in
> `test_obstacles.py::test_enemy_hex_blocks_passage_until_it_dies`). So the regions are
> *not* permanently separated: every kill opens a door between three of them. Lemma 5.3 is
> the statement that the door only ever opens for stacks that have already spent their
> action. Without it the reduction would leak and the "no ⟹ no" direction would fail. This
> is the least obvious step in the proof and the one a referee should attack first. The
> doorway is real and not hypothetical: killing an enemy by hand on a chained three-triple
> board and re-querying reach shows the reach set widen, for exactly the elements of the
> dead triple (`crosscheck_sol.py`, doorway probe).
>
> The induction also covers plays in which a stack moves without attacking, defends, or
> waits — but the three cases are not the same, and an earlier draft blurred them (a
> round-4 review finding). A stack that moves without attacking or defends has *spent* its
> terminal action. A stack that waits has **not**: it has postponed its terminal action to
> the `WAIT` phase (`MODEL.md` §5), and the induction simply reaches it there — the
> induction is over terminal actions, not over issued commands, which is why waiting
> changes the order of the induction and nothing else. The argument never assumes that an
> acting stack strikes, and `(‡c)` covers the only other effect of waiting, the possible
> damage reduction against a defended target.

**Lemma 5.4 (yes ⟹ yes).** *If `(X, C)` has an exact cover then `G_3(X, C)` is a
yes-instance.*

*Proof.* Let `C' = {S_1, …, S_q}` be an exact cover. Allocate one creature to every slot;
the total is `3q`, exactly the stock. Each element `e` lies in exactly one `S ∈ C'`; let the
stack of slot `e` issue `WALK_AND_ATTACK` to `d_S^e` against `E_S`. No stack waits or
defends, so by `(‡c)` every blow deals its nominal `D(1) = 1`.

Every one of these moves is legal, whatever order the engine imposes. Only the three slots
of `S` ever target `E_S`, so when slot `e` acts `E_S` has taken at most two strikes and is
still alive; `d_S^e` is free, since no other stack can enter `R_e` (Lemma 4.1) and the other
two strikers of `E_S` stand on the other two dockings. So Lemma 4.1 applies and the strike
lands. Each `S ∈ C'` accumulates 3 damage and dies, and the destroyed value is `q = W`. ∎

**Lemma 5.5 (yes ⟹ exact cover).** *If `G_3(X, C)` is a yes-instance then `(X, C)` has an
exact cover.*

*Proof.* Take an allocation and a play destroying value at least `q`. Every enemy has value
1, so the number `t` of dead enemies is at least `q`; by Lemma 5.2, `t ≤ q`. Hence `t = q`
and the second half of Lemma 5.2 applies. Let `K` be the set of dead enemies. By Lemma 5.2
each `S ∈ K` is struck by exactly three one-creature stacks, and by Lemma 5.3 each striker
of `E_S` is the stack of a slot `e` with `e ∈ S`; since the three strikers are distinct and
`|S| = 3`, they are exactly the slots of `S`. A slot strikes once, so distinct members of
`K` use disjoint slot sets; `|K| = q` and each uses 3 slots, so together they use all `3q`
slots. Hence `K` is a family of `q` pairwise disjoint 3-sets covering `X`: an exact
cover. ∎

**Proof of Theorem 3.** Lemmas 5.4 and 5.5 give the equivalence; Lemma 4.4 gives a total
polynomial-time construction (degenerate and nonplanar encodings map to the fixed
no-instance `G_no`); §2 notes every number
is polynomially bounded, so the reduction is a polynomial reduction even under unary
encoding, and `PLANAR-X3C` is NP-complete. Membership in NP is `candidate-A.md` Lemma 3.5
verbatim (the board is given hex by hex and `R = 1`). ∎

### 5.1 Proof of Corollary 3.1 (fixed allocation)

Fix the allocation `c_e = 1` for every `e ∈ X`, so the instance ceases to have an allocation
decision at all and the only choice left is the play.

*Yes direction.* Lemma 5.4 already uses precisely this allocation.

*No direction.* With `c ≡ 1`, `Σ_e c_e = 3q` and every stack delivers at most `D(1) = 1`
damage per blow. An enemy has 3 hit points, so each kill consumes strikes from at least
three distinct stacks, and the striker sets of distinct dead enemies are disjoint (a stack
strikes at most once per round; see Lemma 5.2). Killing `t` enemies therefore consumes at least `3t` of the `3q` stacks, so
`t ≤ q`, and at `t = q` every dead enemy is struck by exactly three distinct one-creature
stacks and every stack strikes a dead enemy — the conclusion of Lemma 5.2, obtained here
without the resource lemma's equality case, which is only needed to rule out unequal stack
sizes. Lemmas 5.3 and 5.5 then apply verbatim. ∎

The corollary is the version of the theorem to quote, for the reason given in §1: with the
allocation pinned, no one can misread the result as a statement about stack sizing. Note
also what the corollary costs: nothing. The reduction was never using the freedom to size
stacks; it was using the freedom to choose targets under a reach structure that a planar
incidence graph can encode.

---

## 6. Verification status

Two machine checks, under two different parameterisations of the same construction. Nothing
in `homm3_model.py` was modified for either: obstacles were already supported
(`Battlefield.obstacles`, honoured by `Battle.reachable:278`), so both run on the existing
simulator. `verify_mechanics.py` reports all checks passing (90 as of 2026-08-16; the
count grows as mechanics tests are added — trust the script's own output, not this file).

**A. `../scripts/verify_x3c.py`** — the construction with `def(Q) = 41`, `hp(P) = 5`
(`μ = 0.3`, on the defence cap, so the ULP discrepancy of §3.3(a) is live).

1. **Resource lemma**, exhaustively over stack multisets of up to 6 stacks and sizes up to
   40, under *both* defence-cap constants (Python's `0.7` and VCMI's loaded
   `0.7000000000000001`). Confirms `D(c) = max(1, ⌊μc⌋)`, that the cheapest 3 damage costs
   3 creatures, and that `(1,1,1)` is the unique cheapest witness.
2. **The four adapters** of Lemma 4.3, checked as described there.
3. **A negative control**, so that the suite is not passing vacuously. Set
   `def(Q) = att(P)`, which destroys Lemma 3.1: now `Δ = 0`, no defence factor applies,
   `D(c) = c`, and three creatures in a *single* slot kill an enemy on their own. Killing
   `q` enemies then needs only `q` distinct 3-sets, not `q` disjoint ones. The check
   confirms that a fixed **no**-instance of X3C does turn into a **yes**-instance of the
   game under that change — i.e. the search would notice if the resource lemma stopped
   holding.
4. **Board invariants (I1)–(I4)** on every constructed board, plus the direct check that
   each deployed stack's attackable set equals the sets containing its element and that each
   has exactly one approach hex per target.
5. **The reduction**, on X3C instances with `q ∈ {1,2,3,4}`, planted-cover and random
   families, yes and no: the game answer is computed by enumerating **all** allocations
   (every count vector summing to at most the stock — nothing is pruned away by the
   construction's own logic) and, for each, searching all plays, branching over targets and
   over every legal approach hex in the manner of `empirics/scripts/solve.py::_play`. The
   search additionally records *which* allocations win; in every yes-instance the winner is
   unique and is the all-ones allocation predicted by Lemma 5.2 and quoted by
   Corollary 3.1.

   Results, rerun for this version:

   | command | instances built | X3C yes / no | skipped | verdict |
   |---|---|---|---|---|
   | `verify_x3c.py` | 31 | 17 / 14 | 0 | ALL PASS |
   | `verify_x3c.py --vacate` | 31 | 17 / 14 | 0 | ALL PASS |
   | `verify_x3c.py --full --vacate` | 55 | 30 / 25 | 4 | ALL PASS |
   | `crosscheck_sol.py` | 25 | 14 / 11 | 0 | ALL PASS |
   | `crosscheck_sol.py --full` | 37 | 23 / 14 | 3 | ALL PASS |

   The default suite gives **identical answers with the pure-movement branch on and off**,
   which is the point of the `--vacate` flag.

   > **Why the `--full` counts used to move between runs, and no longer do.** The router
   > retried under a per-instance wall-clock budget (`build_board(..., budget=25.0)`), so on
   > a loaded machine it laid out fewer of the harder instances and reported more skips —
   > worse, a truncated retry loop consumed a different amount of the shared rng stream, so
   > every *subsequent* board shifted too, which is why even the yes/no split wobbled.
   > Round 8 flagged the drifting counts; frozen-clock probes then showed the deadline was
   > the *only* source of variance (with the clock frozen, two separate processes build
   > bit-identical boards — same fingerprints). The deadline is removed, retries are capped
   > by attempt count alone, and the counts in the table above now reproduce exactly on any
   > machine. What the suite asserts was never affected: every board built passes the
   > invariant check, every instance built agrees with X3C, and the unique winning
   > allocation is canonical on every yes-instance. Skips are honest failures of a heuristic
   > layout routine; the embedding verifier's per-family classification shows every skipped
   > family is a degenerate no-instance with an uncovered element (three of them are also
   > non-planar — non-planarity exists in the corpora but is not what drives the skips). At
   > `q = 4` the allocation enumeration alone is `C(24,12) ≈ 2.7·10⁶` vectors per instance,
   > which is where the time goes.

   The only prune inside the play search is an admissible upper bound on the value still
   obtainable: the damage still to come is at most the sum of `D(count)` over the stacks
   that have not acted, and an enemy needs 3 accumulated damage to die. It is a statement
   about damage arithmetic only and ignores reachability entirely, so it cannot mask an
   error in Lemma 4.1 or Lemma 5.3, which are the delicate steps.

**Pure movement, and the `--vacate` flag.** Neither search branches over `MOVE`-only
actions. A pure move deals no damage and affects the rest of the round only through which
hex the stack occupies, so the action "this stack vanishes" **dominates** every pure move
and admitting it gives a sound upper bound. `VACATE_BRANCH` in `verify_x3c.py` adds exactly
that branch and is now reachable from the command line as `--vacate`; the flag's state is
printed in the run header and in the summary line, so a log identifies which world it came
from. Before this version the flag existed but no documented command turned it on, and the
write-up claimed a vacate-enabled run that could not be reproduced. It can be now, and the
answer is unchanged on all 31 default instances.

**B. `../scripts/crosscheck_sol.py`** — the **canonical** parameterisation of §2
(`def(Q) = 27`, `hp(P) = 4`, `μ = 0.35`) driven through the same board generator and the
same exhaustive play search. It additionally re-derives the damage function from
`MODEL.md` §4 by hand and compares it against `compute_damage` for `c = 1 … 199`; runs the
resource-lemma sweep under these constants; probes that the budget bound is load-bearing;
probes that the doorway of Lemma 5.3 really opens; and admits pure movement on sol's own
hand-built boards. Counts in the table above; all agreeing, all winners canonical. This is
the check that covers the **canonical** constants of §2, so it is the one to quote for the
theorem as stated.

**C. `../scripts/test_obstacles.py`** (158 checks) pins the simulator behaviour the proof
leans on: alternating triples are the only pairwise non-adjacent triples (Lemma 4.2), the
square grid is a hex subgraph (Lemma 4.4, step 4), obstacle walls separate regions even at
unbounded speed, a living enemy seals a corridor and a dead one does not (the premise of
Lemma 5.3), and a stack on a dead end blocks nothing (the second half of (I3)).

The one thing the machine checks do **not** do is verify Lemma 4.4 in general:
`verify_embedding.py` runs the lemma's own algorithm on every corpus family and checks
(I1)–(I4) — plus the full game answer on the smallest boards — but the claim that the
algorithm succeeds on *every* planar instance remains a hand proof (§4.2).

---

## 7. What this changes

**7.1 The roster-diversity conjecture is dead.** `candidate-A.md` §5.5 records it as an open
conjecture; it is now refuted and that section has been updated to say so. The correct
statement of the contrast is not "few types easy, many types hard" but:

* the `O(kB)` dynamic program of `candidate-A.md` §5.5 is a statement about a **reach
  structure**, namely that each slot engages exactly one enemy and each enemy is engaged by
  exactly one slot — the reach graph is a perfect matching. Then the allocation separates
  into `k` independent threshold decisions and the problem is a knapsack;
* as soon as the reach hypergraph is nontrivial, one creature type is enough for strong
  hardness, and the allocation can even be fixed (Theorem 3, Corollary 3.1);
* `candidate-A.md` Theorem 2 is then not the "strong" endpoint of a diversity axis but a
  second, independent source of hardness: many types with a *trivial* reach structure
  (three preassigned slots per enemy) is also strongly hard.

We now have hard families at **both** extremes of the roster axis, so no boundary along that
axis can separate the easy cases from the hard ones. That is a refutation of the conjecture,
not a replacement for it: we make no claim that the reach hypergraph is *the* dividing
parameter, only that it, and not the roster, distinguishes the examples we have. The paper
presents the two theorems as isolating two different sources of the same difficulty, drops
the conjecture rather than restating it, and never uses the word "dichotomy" for a result.

**7.2 The featureless question is answered elsewhere, not here.** `candidate-A.md` §6.1 asks
whether the problem is still hard on a *featureless* board where every slot reaches every
enemy. Theorem 3 does not answer that: it goes the other way, making the reach structure as
rich as planar incidence allows and paying for it with obstacles. That question is settled
by `candidate-C-featureless.md` (Theorem 4), which keeps the many-type roster. Worth
recording as the natural sequel: *featureless board, single type, enemies of differing hit
points*. There the decision is a multiset of stack sizes summing to at most the stock,
partitioned into groups whose `D`-sums cover the enemies' hit points — a covering problem
with the damage floor supplying the granularity. Neither theorem says anything about it, and
it is the version a referee is most likely to ask for.

**7.3 A third mechanic joins the list.** `candidate-A.md` §1 names two: kill thresholds (K)
and count-based output (C). Theorem 3 adds

* **(F) The damage floor.** Every strike deals at least 1 (`DamageCalculator.cpp:576-577`).
  Against a target whose defence exceeds the attacker's attack, `f_att = 1` and `f_def < 1`,
  so `c` creatures in one stack deal `⌊μc⌋ < c` while the same `c` creatures in `c` stacks
  of one deal `c`. Splitting is then strictly better, and the granularity it buys is exactly
  what a covering problem needs.

Note the sign flip: against a *weaker* target, where the attack factor exceeds 1, merging is
**weakly** better and sometimes strictly better, since `⌊c·f_att⌋ ≥ c·⌊f_att⌋` — but the
inequality can be an equality, so "merging is strictly better" is false as a general claim
and was wrong in the earlier draft. What survives, and is all that is used, is that the
game's own arithmetic makes the optimal granularity depend on the matchup, which is why the
player cannot decide it slot by slot. (K) does the work of turning damage into value; (F) is
what makes a single-type army capable of expressing a covering problem at all.

---

## 8. What the reduction leans on that the shipped game does not give for free

Listed here rather than buried, because a referee will find them.

1. **Deployment hexes are an input.** `MODEL.md` §9 defines `ARMY-ALLOCATION` with the map
   from slot index to starting hex given in the input. In the shipped game that map comes
   from fixed formation tables (`attackerUnitsLoose` / `attackerUnitsTight`,
   `config/gameConfig.json:635-642`), which place stacks in one or two columns, not at
   arbitrary hexes. This construction needs one deployment hex inside every element region,
   so it uses the generalised freedom in an essential way — more so than either theorem of
   `candidate-A.md`. The honest statement, which `MODEL.md` §9 now makes explicitly, is that
   **the object studied is a generalized battle scenario with prescribed deployment cells**,
   not merely the shipped game with the board and roster bounds lifted. Recovering the
   result under native formations is left open (§9).
2. **Obstacles are load-bearing.** `candidate-A.md` §5.3 could boast that its constructions
   used no obstacles at all; Theorem 3 cannot. Static impassable hexes are a shipped
   mechanic (`MODEL.md` §2, `CBattleInfoCallback.cpp:1328-1391`), so obstacles add nothing
   foreign to the game's own rules — though, as point 1 says, the arena is the generalized
   model, not the shipped game — but the "aggressive restriction" selling point is
   weaker here.
3. **Speed is set to the board size.** Legal, and it removes the corridor-length
   bookkeeping, but a referee may find it inelegant. A version with bounded speed would need
   equalised corridor lengths, which is exactly the complication §4.3 buys its way out of.
4. **The objective is "value destroyed within `R = 1`".** Inherited from `MODEL.md` §9 and
   not improved on here.

---

## 9. Weaknesses and open ends

1. ~~**Two literature dependencies are unverified in this project**~~ — **resolved
   2026-08-03**: Dyer–Frieze read in full against the source (§2); Tamassia–Tollis
   verified via the Handbook's exact Theorem 7.3 statement (§4.2, step 3), primary IEEE
   text itself still unopened (paywall) — the one residue of this item. (The theorem hangs
   off the first and Lemma 4.4 off the second, which is why this was listed first.)
2. **Lemma 4.4 is a hand proof.** It is now written out rather than sketched, including the
   scaling repair, the rotation-preserving degree reduction, the disconnected case and the
   deployment stub — but it is checked by hand, and only its *conclusion* is machine-checked,
   on router-built boards.
3. **The machine check reaches `q ≤ 4`.** The exhaustive play search is the bottleneck. The
   step that would most benefit from larger instances is Lemma 5.3, since leakage needs a
   dead enemy and several rounds of structure to show itself.
4. **Native deployment formations** (§8.1), **bounded speed** (§8.3), **an obstacle-free
   single-type construction**, **fixed `k`** (`candidate-A.md` §6.2 conjectures the problem
   is in P for fixed `k`; this theorem needs `k = 3q` to grow and says nothing about it), and
   **the natural whole-battle objective** are all explicitly deferred. None is needed for
   the present submission.

---

## 10. The two independent proofs, and the merge

An isolated instance of gpt-5.6-sol proved the same theorem independently and in parallel
(`sol-attempt/PROOF.md`, `verify.py`, `ATTEMPTS.md`); this file's author was asked to try to
break it and could not. The two write-ups agree on every substantive point, which is the
strongest evidence either of them could have. This section records the audit and what the
merge took from each. `sol-attempt/` is kept as the historical record; **this file is the
one to read.** Cross-check code: `../scripts/crosscheck_sol.py`.

### 10.1 A correction to the framing

The brief under which the cross-review was run said sol's construction is *without
obstacles*. That is not what his document says: restriction 6 reads "the only terrain
feature used is a polynomial-size set of static impassable hexes", his Lemma 1 says "make
every unused battlefield cell an obstacle", and his `verify.py` builds boards as
`obstacles = frozenset(range(width*height)) - open_cells`. His `ATTEMPTS.md` §3 records
rejecting an obstacle-free open-board variant as unproven. The two constructions do not
differ on this axis at all. What is true, and worth keeping, is that neither of us had to
modify `homm3_model.py`.

### 10.2 What was attacked, and what held

* **The arithmetic.** Defence 27 against attack 1 is 26 defence points, and
  `0.025 · 26 = 0.65` is genuinely below the cap `0.7`, so the multiplier is `0.35` and an
  *undefended* blow never reads the cap. (A *defended* target under `(‡)` is another
  matter: `def 32` gives `0.025 · 31 = 0.775`, which crosses the cap and is clamped —
  absorbed by the resource lemma's `μ ∈ (0, 1)` generality, and pinned against the engine
  by the harness's ULP cases; see the paper §4.2.) The damage function re-derived from `MODEL.md` §4 by hand
  agrees with `compute_damage` for `c = 1 … 199`. His table `1,1,1,1,1,2,2,2,3,3,3,4` is
  right, and his minima `9, 7, 3` are right.
* **The ULP question, and he wins it.** Recomputing his whole damage table under the
  engine's mis-parsed cap `0.7000000000000001` and under Python's `0.7` gives **identical**
  results, because he never reaches the cap. The `def(Q) = 41` variant does reach it and its
  table differs at `D(10)` (3 against 2). Both are safe — Lemma 3.1 needs only `μ < 1` — but
  his choice removes the issue instead of surviving it. **The merge uses his constants.**
* **The resource lemma.** His Lemma 2 assumes `δ(2) = δ(3) = 1`; Lemma 3.1 above assumes
  only `δ(c) < c` for `c ≥ 2`, which holds for every `μ < 1` and implies his — including
  under the defending-enemy multiplier `0.3` of `(‡c)`, which his form would have had to
  re-derive. **The merge uses the general form.**
* **The stock-tightness induction (his Lemma 4).** The same argument as Lemma 5.3 above,
  checked line by line. Two places are terser than they should be but neither is wrong:
  (a) he never states that exactly `q` enemies die, only bounds the first `q` — it does
  follow, since a `(q+1)`-th kill would need three more creatures that equality has already
  spent; (b) his "three attackers come from precisely its three incident element components"
  relies on there being one stack per component, not on `e_t` having exactly three free
  neighbours. Both repairs are one sentence and both are incorporated above.
* **Is the induction guarding against anything?** Killing an enemy by hand on a chained
  three-triple board and re-querying reach shows that reach really does widen, for exactly
  the elements of the dead triple and no others. The doorway is real, the induction is
  necessary, and its scope is right. Neither original write-up demonstrated this; §5 now
  says it, because a referee will ask why the lemma is there.
* **His constants on machine-built boards.** His creature statistics driven through this
  file's instance generator, which builds planar boards automatically and reaches `q = 4`
  instead of his two hand-drawn `q = 2` boards: **37 instances (23 yes, 14 no), all agreeing
  with X3C**, and in every yes-instance the unique winning allocation is the canonical
  all-ones. (Deterministic since the router's wall-clock deadline was removed — see §10.2:
  these counts reproduce exactly, the 3 skipped boards are printed, never silently dropped.)
  His parameters survive everything this construction survives.

### 10.3 The gap that was in both verifications, now closed

Neither his search nor this one branches over **pure movement** — both branch only over
passing and over (target, approach hex). Both proofs argue it away, but the argument uses
the very lemma under test, so the machine checks were mildly circular. The `VACATE_BRANCH`
relaxation of §6 closes it: a vanishing stack dominates every pure move, and the answers do
not move. It is now reachable as `verify_x3c.py --vacate` and captured in a log.

This mattered slightly more for his construction than for this one: his deployment hexes sit
in the *middle* of their corridors (`verify.py`: `sorted(path)[len(path)//2]`), so a
stationary stack does block its corridor and a pure move would unblock it. Here they sit on
dead ends and `check_geometry` asserts it, so the question cannot arise. That is a small
structural advantage of this layout, not a defect in his proof.

### 10.4 What each write-up contributed

**From sol:** the `0.35` parameterisation (§3.3a); the Dyer–Frieze citation with a DOI and
the two-line derivation of the X3C form from PLANAR 3DM (§2).

**From this file:** the general `μ < 1` resource lemma; the whole of §4, in particular the
forced alternating triple (Lemma 4.2), the four adapters (Lemma 4.3) — his Lemma 1 disposes
of that step in one sentence, "the embedding's cyclic order lets the three incident corridors
enter these ports without crossing", which is exactly the step that is not obvious — and
Lemma 4.4 in full; the machine check at scale with a negative control; and the disclosure
convention for unverified citations.

**Packaging note.** `sol-attempt/PROOF.md` refers to `docs/MODEL.md` and `docs/candidate-A.md`,
which do not exist under those paths (they are `homm3/MODEL.md` and
`homm3/proofs/candidate-A.md`), and `sol-attempt/verify.py` puts `sol-attempt/scripts` on
`sys.path` rather than `homm3/scripts`, so it dies with `ModuleNotFoundError` from the
repository root and reproduces only once `PYTHONPATH` points at `homm3/scripts`. Those files
are kept unchanged as the historical record of an independent proof; the paths in **this**
document are the correct ones.

---

**Status:** proved + checked, independently confirmed. Literature dependencies resolved
2026-08-03: **Dyer–Frieze read in full against the published paper** (Lemma 2.2 states
Planar X3C NP-complete with our exact planarity convention — see §2); **Tamassia–Tollis
1989 verified via the exact Theorem 7.3 statement in the Handbook of Graph Drawing**
(connected 4-plane case suffices — see §4.2 step 3), with the honest caveat that the
paywalled IEEE original itself was not opened. Earlier DBLP-only checks confirmed
bibliography, not statements, and had pointed at the wrong Tamassia paper; both issues are
now corrected in place.

The reduction (§§2–3, §5) is complete and machine-checked end to end under two
parameterisations, including the delicate no-leakage induction (Lemma 5.3), with the
pure-movement relaxation enabled and disabled and identical answers. The resource lemma is
robust to the engine's ULP discrepancy and to the defence bonus that the formalised hold
policy introduces. The geometry is complete: the invariants (I1)–(I4), the forced
alternating triple, and the four adapters are machine-checked, and the general embedding
(Lemma 4.4) is written out in full rather than sketched.

**Remaining work** (round 8 note: an earlier version of item (a) said the citation *content*
was still unchecked, contradicting the status paragraph above — that sentence predated the
2026-08-03 verification and is corrected here): (a) the Tamassia–Tollis 1989 statement is
quoted via the Handbook's Theorem 7.3; on 2026-08-17 the abstract of the IEEE original was
additionally obtained as recorded in a bibliographic index (OpenAlex, reconstructed from
the record's inverted word index) and states verbatim the numbers used here — `O(n)` time,
total bends at most `2.4n + 2`, at most `4` bends per edge, edge length `O(n)`, area
`O(n²)` — so the residual gap has narrowed to the unread proof body, the biconnected
`2n + 4` refinement (not used here), and the connectivity hypothesis of the `2.4n + 2`
case, which the abstract does not state and which therefore still rests on the Handbook;
Dyer–Frieze was read in full and the Handbook quotation was checked verbatim; (b) Lemma 4.4's two construction
gaps found in round 7 are now repaired in the text (the bounding-box offset `μ = 6 > ρ`, and
the grid bound weakened to the polynomial the citation actually supplies), and after round 8
the deterministic construction is implemented as well (`planar_embed.py` + `embed_lemma.py`,
with three disclosed subroutine substitutions — DMP planarity, st-visibility drawing,
drawing-level packing; see
§4.2 — validated on the whole corpus by `verify_embedding.py`) — this closes what the
round-8 codex voice named the largest remaining gap between the proof and the artifact;
only the universal claim of the lemma remains hand-proved.
