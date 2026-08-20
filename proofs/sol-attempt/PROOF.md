# Strong NP-hardness of single-type army allocation

> **SUPERSEDED — historical record.** This is one of two proofs of the same theorem, written
> independently and in parallel by an isolated agent. It was cross-reviewed, found correct,
> and merged with the other into the canonical write-up
> `../candidate-D-singletype.md`, which is **the version to read and to cite**. The merge took
> this document's creature statistics (defence 27, multiplier 0.35, player hit points 4) and
> its Dyer–Frieze citation; it took the other document's general `μ < 1` resource lemma, its
> geometry, and its embedding lemma, which is written out in full there rather than quoted in
> a sentence as in Lemma 1 below. This file is kept **unchanged** as evidence that two
> independent derivations agreed.
>
> **Corrections to the paths and the reproduction command**, which are wrong in the text
> below and are the reason this note exists:
>
> | written here | actually |
> |---|---|
> | `docs/MODEL.md` | `homm3/MODEL.md` |
> | `docs/candidate-A.md` | `homm3/proofs/candidate-A.md` |
> | `scripts/homm3_model.py` | `homm3/scripts/homm3_model.py` |
> | `scripts/solve.py` | `homm3/empirics/scripts/solve.py` |
>
> `verify.py` puts `sol-attempt/scripts` on `sys.path`, which does not exist, so from the
> repository root it fails with `ModuleNotFoundError: No module named 'homm3_model'`. It
> reproduces (ALL CHECKS PASSED, a few seconds) with
>
> ```
> PYTHONPATH=homm3/scripts python3 homm3/proofs/sol-attempt/verify.py
> ```
>
> Two further gaps, both one sentence and both repaired in the canonical version: this proof
> never states that exactly `q` enemies die (only bounds the first `q` — it does follow, since
> a `(q+1)`-th kill would need three creatures the equality has already spent), and "three
> attackers come from precisely its three incident element components" relies on there being
> one stack per component rather than on the three-free-neighbour property of Lemma 1.

## Theorem

Consider `ARMY-ALLOCATION` as defined in `docs/MODEL.md`, Section 9, with the
deterministic combat rules implemented by `scripts/homm3_model.py`.

**Theorem (i).** `ARMY-ALLOCATION` is strongly NP-hard even under all of the
following simultaneous restrictions:

1. the round bound is `R = 1`;
2. the player's army contains a single creature type;
3. every enemy stack contains one creature, all enemy creatures have the same
   type and value one;
4. the enemy policy is to hold position;
5. damage is flat, all creatures are melee and have no special abilities; and
6. the only terrain feature used is a polynomial-size set of static impassable
   hexes.

Thus the roster-diversity conjecture in `docs/candidate-A.md`, Section 5.5, is
false.  The construction uses growing speed and a growing obstacle board, but
every number in it is polynomially bounded.  In particular, it remains a
polynomial reduction if all numerical parameters are written in unary.

## Source problem

We reduce from **PLANAR 3-DIMENSIONAL MATCHING** (PLANAR 3DM).  An instance has
three disjoint sets `X`, `Y`, and `Z`, each of cardinality `q`, and a family
`T` of triples in `X × Y × Z`.  Its incidence graph has one vertex for every
element and every triple and an edge `u--t` exactly when `u` occurs in `t`.
The incidence graph is planar.  The question is whether `T` contains `q`
pairwise disjoint triples.  Such triples necessarily cover the universe

```
U := X union Y union Z,                 |U| = 3q.
```

Dyer and Frieze proved PLANAR 3DM NP-complete [1].  This is also the exact
planar-X3C form needed below: every triple vertex has degree three, and a
matching of size `q` is an exact cover of `U`.

## A corridor realization lemma

We first isolate the only geometric fact used by the reduction.

**Lemma 1 (incidence corridors).**  From a planar incidence graph
`G = (U union T, E)` one can construct in polynomial time a rectangular hex
battlefield, static obstacles, cells `p_u` for `u in U`, and cells `e_t` for
`t in T` with the following properties.  Regard every `e_t` as blocked, as it
will be while occupied by its living enemy.

1. The non-obstacle cells other than the `e_t` have one connected component
   `K_u` for each `u in U`, and `p_u` belongs to `K_u`.
2. `K_u` contains a cell adjacent to `e_t` if and only if `u in t`.
3. For each triple `t = {u,v,w}`, the three cells of `K_u`, `K_v`, and `K_w`
   adjacent to `e_t` are distinct and pairwise nonadjacent.
4. The board area and the diameter of every `K_u` are polynomial in `|G|`.

**Proof.**  Compute a planar embedding and a polynomial-area grid drawing of
`G`.  This is a standard constructive planar-drawing result; one may, for
example, first split a high-degree element vertex into a small plane tree and
then use an orthogonal grid drawing.  This preserves one connected region per
element and introduces only linearly many drawing vertices.  Scale the drawing
by a fixed constant.  Replace each drawn edge by a one-cell-wide hex corridor,
join the corridors at each element vertex, and make every unused battlefield
cell an obstacle.  The scaling leaves at least one obstacle-cell layer between
unrelated corridors, including under the diagonal adjacencies of the offset
hex grid.

At a triple vertex install a constant-size local trident.  Its centre is
`e_t`; its three arms end at three alternating neighbours of `e_t`.  Alternating
neighbours of a hex are pairwise nonadjacent.  The embedding's cyclic order
lets the three incident corridors enter these ports without crossing.  Delete
the centre of every trident.  What remains is precisely a thickened subdivision
of `G - T`, whose components are the element vertices and their incident open
edge stubs.  These are the `K_u`.  All operations use constant-size local
replacements on a polynomial-area grid drawing, proving all four claims. ∎

Let `S` be at least two and at least the maximum number of cells in any
component `K_u`.  Then a stack at `p_u` can reach every cell of `K_u` in one
move.  While every enemy is alive, it can attack exactly the enemies `e_t`
with `u in t`.  We deliberately do **not** require equal corridor lengths.
Section “No direction” proves that opening a killed enemy's centre creates no
useful leakage.

## The combat resource lemma

Use the following two creature types.  All omitted ability flags are false.

| statistic | player type `P` | enemy type `E` |
|---|---:|---:|
| attack | 1 | 1 |
| defence | 1 | 27 |
| flat damage | 1 | 1 |
| hit points | 4 | 3 |
| speed | `S` | 1 |
| value | 0 | 1 |

For a `P` stack containing `c` creatures attacking one `E`, the defence
advantage is 26.  It is below the defence cap, so the intended real-arithmetic
multiplier is

```
1 - 0.025 * 26 = 0.35.
```

Accordingly the mathematical formula is

```
delta(c) = max(1, floor(0.35 c)).
```

The proof does not rely on any exact-integer boundary.  It uses only

```
delta(c) <= c for every c >= 1,
delta(1) = delta(2) = delta(3) = 1.                (1)
```

The raw products relevant to the second line are `0.35`, `0.70`, and `1.05`;
none is an integer.  More importantly, these statements were checked against
the executable `compute_damage`, not inferred only from the displayed decimal.
Its output for `c = 1,...,12` was

```
1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4.
```

Thus this construction avoids both the defence cap and the sketch's
`10 * 0.3` boundary.

**Lemma 2 (three-for-three).**  Suppose some positive-size `P` stacks make one
attack each against an enemy with three hit points.  If their initial creature
counts have sum at most three, they kill the enemy if and only if there are
exactly three stacks and each contains one creature.  More generally, every
kill consumes attacks by stacks whose creature counts sum to at least three.

**Proof.**  By (1), damage is at most creature count, so three damage requires
total count at least three.  If total count equals three, the positive stack
sizes form one of `(3)`, `(1,2)`, `(2,1)`, or `(1,1,1)`.  By (1), these deal,
respectively, one, two, two, and three total damage. ∎

For reference, exhaustive enumeration with the executable formula gives
minimum creature costs 9, 7, and 3 when exactly one, two, or three attacking
stacks are permitted.  Only the equality statement in Lemma 2 is used.

## The reduction

Given `(X,Y,Z,T)`, apply Lemma 1.  Make one player deployment slot at every
`p_u`, hence `k = 3q`.  The available army consists of exactly `3q` creatures
of the single type `P`; the allocation may put any nonnegative number in each
slot, subject to that stock bound.

For every triple `t in T`, place one one-creature stack of type `E` at `e_t`.
The enemy policy always holds.  Set

```
R = 1,                  W = q.
```

All `P` stacks act before all `E` stacks because `S >= 2`.  An enemy may
retaliate against the first attacker, but its retaliation deals one damage.
A one-creature `P` stack has four hit points, so it survives.  Retaliation is
therefore harmless; in particular it occurs after that stack has delivered its
only attack and cannot change any other player's damage.

The construction is polynomial.  Its combat numbers other than `S`, `3q`, and
`q` are constants, while `S` is at most the polynomial board area.  The list of
obstacles is itself explicit and polynomial.  Hence the construction also has
polynomial size under unary encoding of every numerical parameter.

## Correctness

### Yes direction

**Lemma 3.**  If the PLANAR 3DM instance has a perfect matching, the constructed
`ARMY-ALLOCATION` instance has value at least `q` in one round.

**Proof.**  Put one `P` creature in every element slot.  For each selected
triple `t = {u,v,w}`, have the stacks at `p_u`, `p_v`, and `p_w` attack `e_t`.
The matching covers every element once, so this specifies exactly one action
for every player stack.  The three incidence corridors end at distinct,
pairwise nonadjacent approach cells.  A stack that has already attacked cannot
block either of the other two approaches.  Each attack deals one damage, so
the third attack kills `e_t`.  This destroys the `q` selected enemies and earns
value `q`. ∎

### No direction

The subtlety is that a dead enemy no longer occupies its centre cell.  The
three incident element components then become connected.  The following
argument shows why this apparent doorway cannot be exploited.

**Lemma 4 (no useful leakage).**  If a one-round play kills at least `q`
enemies, then the first `q` killed enemies correspond to `q` pairwise disjoint
triples.

**Proof.**  Associate with each of the first `q` killed enemies all player
attacks delivered to it up to its death.  A player stack attacks at most once
in the round, so these groups of attacks are disjoint.  The hold policy means a
player stack has suffered no damage before its own attack; its effective count
at that attack is exactly the count allocated to its slot.

Lemma 2 gives a total allocated count of at least three in each group.  Hence

```
3q <= (counts in those q groups)
   <= (total count allocated)
   <= (available stock) = 3q.                         (2)
```

Every inequality is equality.  Consequently every killed enemy receives
exactly three attacks, each from a distinct one-creature stack.  There is no
allocated stack left for a wasted attack, pure movement, defence, or an
unkilled target.

Order these enemies by their time of death.  Before the first enemy dies, all
enemy centre cells are occupied.  Lemma 1 therefore says its three attackers
come from precisely its three incident element components.  Since the enemy
needs three one-creature attackers and has exactly three incident elements,
all three of those element stacks have now acted.

Proceed inductively.  Consider an unacted stack in component `K_u`.  If `u`
were incident to an already killed triple, then the preceding paragraph,
applied when that triple died, says that this very stack had already acted.
Thus no already killed triple is incident to `u`.  Any route by which the
stack could leave `K_u` must first cross the centre of a triple incident to
`u`; all such centres are still occupied.  It follows that the stack can
attack only a still-living triple that actually contains `u`.

Therefore the three stacks that kill the next enemy are exactly its three
incident element stacks.  None of those elements occurred in an earlier
killed triple, because its unique stack would already have acted.  The killed
triples are pairwise disjoint by induction. ∎

**Lemma 5.**  If the constructed `ARMY-ALLOCATION` instance has value at least
`q`, the PLANAR 3DM instance has a perfect matching.

**Proof.**  Enemy value is one, so value at least `q` means at least `q` enemy
creatures die.  By Lemma 4, the first `q` corresponding triples are pairwise
disjoint.  They contain `3q` distinct elements, exactly the cardinality of
`U`, and hence form a perfect three-dimensional matching. ∎

Lemmas 3 and 5 prove equivalence.  Since PLANAR 3DM is NP-complete and the
reduction remains polynomial with unary numbers, `ARMY-ALLOCATION` is strongly
NP-hard with one player creature type and `R = 1`. ∎

## Machine check

`verify.py` performs the required finite checks directly with
`scripts/homm3_model.py`.

* It numerically audits the damage formula and exhausts all compositions in
  the resource lemma's equality range.
* It unit-tests static obstacle blocking.
* It builds a planar yes-instance with an unselected distractor triple and a
  planar no-instance whose three triples pairwise intersect.
* It verifies exact incidence reach both with loose probes and with every slot
  occupied.
* For each instance it enumerates all 924 allocations of at most six identical
  creatures among six slots.  For every allocation it recursively branches
  over passing, every attackable target, and every legal approach hex, using
  the same structure as `scripts/solve.py::_play`.

The yes-instance has optimum two at threshold two; the no-instance has optimum
one.  The complete captured output is in `VERIFY-LOG.txt`.  This finite check
does not replace Lemma 1 or the unbounded correctness proof; it checks the
mechanical transcription and the small cases most likely to expose targeting,
approach, blocking, retaliation, or rounding mistakes.

## References

[1] M. E. Dyer and A. M. Frieze, “Planar 3DM is NP-complete,” *Journal of
Algorithms* 7(2), 174–184 (1986),
[doi:10.1016/0196-6774(86)90002-7](https://doi.org/10.1016/0196-6774(86)90002-7).

For the standard polynomial grid-drawing step in Lemma 1, see R. Tamassia,
“On embedding a graph in the grid with the minimum number of bends,” *SIAM
Journal on Computing* 16(3), 421–444 (1987).

STATUS: proved+checked
