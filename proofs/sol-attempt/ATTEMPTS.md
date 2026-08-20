# Attempts, rejected variants, and resolved obstructions

This file records the routes considered while proving `PROOF.md`.  “Rejected”
means that the argument was not used, not necessarily that the underlying idea
is impossible.

## 1. The proposed `0.3` damage factor

The route sketch proposed

```
d(c) = max(1, floor(0.3 c)).
```

Its combinatorial idea is sound, but `c = 10` lies exactly on the integer
boundary `10 * 0.3 = 3`.  The executable model follows floating-point engine
arithmetic, and the repository already warns that this boundary can move by one
under the parsed `0.7` defence cap.  A proof that quotes “one stack needs ten”
would therefore be needlessly brittle.

The final proof uses attack 1 against defence 27, below the cap, for an intended
multiplier of `0.35`.  The only exact values used are

```
d(1) = d(2) = d(3) = 1 and d(c) <= c.
```

The relevant raw products are `0.35`, `0.70`, and `1.05`, away from integer
boundaries.  `verify.py` checks them with `compute_damage`.  It also reports the
stronger empirical minima 9, 7, and 3 creatures for one, two, and three stacks,
but the proof deliberately does not depend on the first two numbers.

## 2. Arbitrary X3C without a planar incidence graph

An early abstraction was “make slot `u` reach exactly the targets containing
`u`.”  Static corridors can realize this relation directly only when its
incidence graph is planar; otherwise corridor crossings would need a crossover
gadget.  No sound crossover gadget was found or needed.

The final reduction starts from Dyer and Frieze's PLANAR 3DM.  It is already an
exact-cover problem on triples, and its planar incidence graph admits the
required obstacle corridors.

## 3. Open-board distance encoding

I considered replacing obstacles by distances on an open board.  This would
require the incidence relation of the hard exact-cover family to be a
hex-distance threshold graph between element slots and target stacks.  General
planar-3DM incidence graphs do not come with such a representation, and no
known NP-hard geometric exact-cover restriction was established here.  Claiming
this route would merely hide the geometry lemma, so it was rejected.  The
proved theorem uses the static obstacles already present in the formal model.

## 4. Corridor crossings and unintended hex adjacency

Noncrossing Euclidean curves are not by themselves enough.  In the offset hex
grid, cells on two visually distinct routes can still be diagonally adjacent,
which joins the routes for BFS.  Lemma 1 therefore scales a polynomial grid
drawing before rasterization and leaves an obstacle-cell layer between
unrelated corridors.

At a target, three arbitrary neighboring approach cells are also unsafe:
consecutive neighbors of a hex are adjacent to each other.  The final local
gadget uses the three alternating neighbors.  They are pairwise nonadjacent,
so an attacker parked at one port cannot block or enter another element's
corridor while the enemy lives.  Both explicit verification boards use this
layout, and `verify.py` asserts that each incidence has exactly one approach
hex.

## 5. A dead target opens a doorway

This was the most serious apparent obstruction.  An enemy hex is occupied only
while the stack is alive.  After the third hit kills it, the centre becomes a
free cell and connects its three incidence corridors.  Thus the pristine reach
graph is not invariant during the round.

Two repairs were considered.

1. Equalize every incidence path to the movement limit, so entering the dead
   centre would cost one step too many.  This works in spirit but burdens the
   embedding with a padding lemma and invites shortcut errors at corridor
   bends.
2. Use the stock equality.  Killing `q` three-HP targets with stock `3q`
   forces every kill to use exactly three singleton stacks.  The first killed
   target therefore consumes all three stacks in the components it opens.
   Inductively, every opened component contains only stacks that have already
   acted, so no live action can exploit it.

The proof uses the second repair.  It is independent of corridor length and is
valid even if speed is large enough to traverse the whole opened network.  The
verification boards intentionally use such oversized speed rather than relying
on equalized paths.

## 6. Dynamic blocking

One occupied player slot per element component causes no cross-component
blocking.  In a yes play, the three attackers of a selected triple use its
three alternating ports.  Once an attacker moves to its port, it is neither on
nor adjacent to either other port.  Selected triples form a matching, so no
element component is needed by two selected targets.

The verifier checks initial reach twice: once with a single probe stack and
once with all six element slots occupied.  Its play search then recomputes BFS
after every move and branches over every approach hex, so later movement and
blocking are not approximated away.

## 7. Retaliation and the hold policy

The hold policy stops enemy normal actions, but it does not stop retaliation.
The first singleton attacker against a target receives one damage after its
blow.  Giving the player type four hit points makes it survive without changing
effective count.  In any event, that stack has already made its only attack in
the one-round construction.  The third blow kills the defender before it can
retaliate.  The final proof accounts for this explicitly; it does not silently
treat “hold” as “no retaliation.”

## 8. Obstacle implementation discrepancy

The task description anticipated that `scripts/homm3_model.py` might lack
obstacles.  In this sandbox it already has an `obstacles` field on
`Battlefield`, and `Battle.reachable` adds those cells to the BFS blocked set.
No copy or extension was necessary.  `verify.py` nevertheless contains a
one-row wall unit test before using obstacles in either reduction instance.

## 9. Scope of the finite check

The two machine instances have `q = 2`.  The yes-instance contains an
overlapping distractor triple; the no-instance has three pairwise-intersecting
triples and every element occurs.  For each, all 924 allocations are evaluated
and all target/approach choices implemented by the executable one-round solver
are searched.

The finite check is not offered as a proof of the polynomial corridor-embedding
lemma or of arbitrary-size correctness.  Those are proved in `PROOF.md`.  Its
role is to catch mistakes in damage floors, reachability, obstacles, approach
selection, movement blocking, and retaliation.
