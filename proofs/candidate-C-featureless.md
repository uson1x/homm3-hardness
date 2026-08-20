# Theorem 4: target selection stays strongly NP-hard on a featureless battlefield

Draft. Companion to `../MODEL.md`, which fixes the rules and the citations into the VCMI
source, and to `candidate-A.md`, whose Theorem 2 this document supersedes on the point a
referee is most likely to press. Machine checking: `../scripts/verify_featureless.py`.

> **Numbering.** In the paper (`paper/main.md`) the theorems run Theorem 1 (PARTITION,
> weak) → Theorem 2 (3-PARTITION allocation) → Theorem 3 (single type on a planar reach
> structure, `candidate-D-singletype.md`) → **Theorem 4 (this document)**, with
> Corollary 4.1 the fixed-allocation form. Earlier drafts of this file called the theorem
> "Theorem 3"; it has been renumbered so that the repository and the paper agree.

---

## 1. What this fixes

`candidate-A.md` §5.4 admits the weak point of Theorem 2 openly:

> Both need the slot's deployment hex to determine which enemy it can engage. […] it
> means the results are about the *joint* decision "how many creatures, in which slot",
> not about stack sizing in isolation on a featureless board.

and its §6 recorded the resulting open problem — "is the problem still hard if every slot
can reach every enemy?" — as "the most likely referee question and the most valuable next
result". This document answers it, and `candidate-A.md` §6 now carries a status note saying
so rather than listing it as open.

In `G₃` (candidate-A §4.1) the battlefield does most of the combinatorial work: each
enemy `E_g` sits in a private "flower" whose three petals are the only deployment hexes
that can reach it, so the partition into triples is *imposed by adjacency* and the player
merely fills the seats. The natural objection is that such a board is a gadget, not a
game position, and that on an ordinary open field — where every stack can walk to every
enemy — the allocation and the targeting decouple and the problem might collapse.

It does not collapse.

> **Theorem 4.** `ARMY-ALLOCATION` is **strongly** NP-hard already for instances with
>
> * `R = 1`,
> * no obstacles and no abilities of any kind,
> * every creature type of stock exactly one, one creature per enemy stack,
> * a rectangular open battlefield of six rows and `4m + 2` columns, and
> * **complete reachability**: in the starting position, with every slot occupied,
>   every player stack can attack every enemy stack.

> **Corollary 4.1 (the harder half).** The same instances are hard even when the
> allocation is *given*. Deciding whether a *fixed, fully deployed* army can destroy
> enemy value `W` in one round, on an obstacle-free board with complete reachability, is
> strongly NP-hard. Call this problem `BATTLE-PLAY`; `ARMY-ALLOCATION` contains it.

Corollary 4.1 is the honest headline, and §7 explains why: once the board is featureless
the allocation becomes irrelevant (any injection of types into slots is as good as any
other), and the entire difficulty moves into the choice of targets. Theorem 4 and
candidate-A Theorem 2 therefore *bracket* the question rather than one subsuming the
other — one is hard because geometry forces the grouping, the other because nothing does.

---

## 2. Notation, and what carries over

We reuse the conventions of `candidate-A.md` §2 unchanged:

* a constant `α ∈ ℤ_{>0}`; every player type has attack `α`, every enemy type defence `α`
  and attack `α`, so `Δ = 0` in `MODEL.md` §4 and `f_att = f_def = 1`. Hence a stack of
  `c` creatures with flat per-creature damage `d` deals

  ```
  dmg = max(1, ⌊c · d⌋) = c · d          for c ≥ 1, d ≥ 1.                        (★)
  ```

* all creatures are melee non-shooters, so no melee penalty applies;
* the scripted defence is `(‡)` exactly as formalised in `candidate-A.md` §2.1: *if the
  stack has not waited this round, it issues `WAIT`; on its postponed activation, it
  issues `DEFEND` at its current hex.* In particular no enemy initiates an attack, a
  waiting or defending enemy still retaliates when struck, and by the one-round lemma
  `(‡c)` the `+20 %` defence bonus applies to no blow unless the striking player stack
  itself waited — in which case the blow delivers at most its nominal damage.

`(‡)` is as load-bearing here as it was there, and for the same reason — see §5.4. The
alternative repair of candidate-A §2, giving the player types `NO_RETALIATION` and
letting the defence attack, works here too and is machine-checked alongside `(‡)`.

What does *not* carry over is `MODEL.md`'s reachability bound `(†)`: there, player speed
was `2`, which was exactly what confined a slot to its own enemy. Here speed is large,
and confinement is what we are removing.

---

## 3. The construction

Let `(a_1, …, a_{3m}; T)` be a 3-PARTITION instance: `Σ_i a_i = mT` and
`T/4 < a_i < T/2` for every `i`. Build the `ARMY-ALLOCATION` instance `G_F(a, T)`.

**Battlefield.** `h = 6` rows and `w = 4m + 2` columns, in the offset coordinates of
`MODEL.md` §2. **No obstacles.** Write `(x, y)` for the hex in column `x`, row `y`.

**Defence.** For `g = 1, …, m` put `X_g := 4g − 2` and place `E_g`, a single creature, at

```
e_g := (X_g, 3),
```

of a type with `att = def = α`, `dmg_min = dmg_max = 1`, `hp = T`, `spd = 1`, `value = 1`.
Since `X_1 = 2` and `X_m = 4m − 2 ≤ w − 3`, every `e_g` has all six neighbours on the
board, and consecutive enemies are four columns apart.

**Player army.** `3m` creature types `C_1, …, C_{3m}` with

```
att(C_i) = α,  def(C_i) = α,  dmg_min(C_i) = dmg_max(C_i) = a_i,
hp(C_i) = 5,   spd(C_i) = s := w + h = 4m + 8,
```

and stock of `C_i` **exactly one creature**. There are `k = 3m` slots, deployed along the
top row:

```
p_j := (j − 1, 0),        j = 1, …, 3m.
```

(`3m − 1 ≤ w − 1`, so the row is long enough. A contiguous run of starting hexes is what
the engine itself does: `config/gameConfig.json:635-642` maps slot count and slot index to
deployment hexes.)

**Question parameters.** `R = 1`, `W = m`.

All `a_i` may be assumed bounded by a polynomial in `m`, so the construction is polynomial
even with the `a_i` written in unary; the board has `6(4m+2) = O(m)` hexes, so listing it
explicitly (as `MODEL.md` §9 and candidate-A Lemma 3.5 require for NP-membership) is also
polynomial.

Three named hexes per enemy will do all the geometric work:

```
q_g^1 := (X_g − 1, 2)          q_g^2 := (X_g, 2)          q_g^3 := (X_g + 1, 3)
```

Row 3 is odd, so by `MODEL.md` §2 the six neighbours of `(X, 3)` are

```
(X − 1, 3), (X + 1, 3), (X − 1, 2), (X, 2), (X − 1, 4), (X, 4).                  (N)
```

`q_g^1, q_g^2, q_g^3` are among them, so each is adjacent to `e_g`.

---

## 4. Geometry

The point of this section is that the board imposes *nothing* except a seat count.

Call a play **attack-only** if every player stack, on its turn, either passes or issues
`WALK_AND_ATTACK`; that is, it uses no `MOVE`-only action, no `WAIT` and no `DEFEND`. The
witness play constructed in §6 is attack-only, and that is the only place geometry is used.

**Lemma 4.1 (confinement along attack-only plays).** In any **attack-only** play of round 1
of `G_F`, every occupied hex lies in row 0, or is an enemy hex, or is adjacent to an enemy
hex. In particular **rows 1 and 5 are free throughout such a play**.

*Proof.* Enemy stacks occupy `e_g` in row 3 and never move: under `(‡)` they issue `WAIT`
and then `DEFEND` in place, neither of which changes their hex, and in the
`NO_RETALIATION` variant they strike an already-adjacent player stack,
for which `WALK_AND_ATTACK` selects the attacker's own hex as the approach hex (it is at
distance 0 and adjacent to the target). A player stack starts on `p_j` in row 0. In an
attack-only play the only action that changes a player stack's hex is `WALK_AND_ATTACK`,
whose destination is by definition adjacent to the struck target (`MODEL.md` §5,
`BattleActionProcessor.cpp:216-352`), hence adjacent to some `e_g`, hence in rows 2, 3 or 4
by `(N)`. A stack acts at most once in a round, so no other hex is ever entered. Rows 1 and
5 contain no `e_g` and, by `(N)`, no neighbour of any `e_g`. ∎

> **Why the restriction to attack-only plays, and why it costs nothing.** `H3-det` retains
> pure movement, `WAIT` and `DEFEND` (`MODEL.md` §5, §7), so in the *full* model an earlier
> player stack can simply walk into row 1 and the universal form of this lemma — "in any
> play" — is **false**. An earlier draft stated it universally; that was a wording error,
> and it is the one a referee would find first. It does not touch Theorem 4, for a reason
> worth stating up front: **Lemmas 4.1–4.4 are used only in the yes-direction**, where we
> exhibit a play and may choose it to be attack-only, and **the no-direction (Lemma 6.2) is
> geometry-free** — it bounds the damage available to the player without any reference to
> the board, so no amount of extra freedom of movement can help. The reference simulator
> implements exactly the attack-only fragment (`../scripts/homm3_model.py`, `turn_order`:
> no MOVE-only action, no WAIT), and the machine check compensates for the gap by also
> allowing a passing stack to **vanish from the board**, which frees strictly more hexes
> than any MOVE could — see §8.

**Lemma 4.2 (access).** Fix `g` and `r ∈ {1,2,3}`. In any state reached by an attack-only
play of round 1 in which `q_g^r` is free, a player stack still standing on its deployment
hex `p_j` can move to `q_g^r` and strike `E_g`.

*Proof.* By Lemma 4.1 every hex of row 1 is free. Row 0 is even, so the two lower
neighbours of `p_j = (j−1, 0)` are `(j−1, 1)` and `(j, 1)`, both in row 1: the stack can
leave row 0 in one step, and can then walk along row 1 freely.

Row 2 is even, so the two upper neighbours of `(x, 2)` are `(x, 1)` and `(x+1, 1)`. Hence:

* `q_g^1 = (X_g − 1, 2)` is entered from `(X_g − 1, 1)` — one step down from row 1;
* `q_g^2 = (X_g, 2)` is entered from `(X_g, 1)` — likewise;
* `q_g^3 = (X_g + 1, 3)` is entered from `(X_g + 1, 2)`, which by `(N)` is a neighbour of
  `(X_g+1, 3)`; and `(X_g + 1, 2)` is *always* free, because the only row-2 neighbours of
  `e_{g'}` are `(X_{g'} − 1, 2)` and `(X_{g'}, 2)`, and `|X_{g'} − X_g| ≥ 4` for `g' ≠ g`,
  so `X_g + 1 ∉ {X_{g'} − 1, X_{g'}}` for any `g'`. It is entered from `(X_g + 1, 1)`.

Each route is: one step out of row 0, at most `w − 1` steps along row 1, then at most two
steps down. Its length is at most `w + 2 < s`, and every hex on it is free. By
`MODEL.md` §5 a melee stack may move to any hex within BFS distance `spd` over free hexes
and strike an adjacent enemy from there. ∎

**Lemma 4.3 (complete reachability — the featureless property).** In the starting position
of `G_F`, with all `3m` slots occupied, every player stack can attack every enemy stack.

*Proof.* At the start the occupied hexes are exactly row 0 and the `e_g`, so every `q_g^1`
is free; apply Lemma 4.2. ∎

**Lemma 4.4 (realisability).** Let `φ : [3m] → [m]` satisfy `|φ^{-1}(g)| = 3` for every
`g`. Then there is an **attack-only** play of round 1 of `G_F`, with all `3m` slots
occupied, in which every stack `j` strikes `E_{φ(j)}`.

*Proof.* Every player type has the same speed `s`, and `s > 1 = spd(E_g)`, so by
`MODEL.md` §5 the player stacks occupy a consecutive prefix of the `NORMAL` phase, in
increasing order of slot index (initiative descending, ties broken by side then slot);
under `(‡)` every enemy's `NORMAL`-phase activation is a `WAIT`, which neither moves nor
strikes, and its terminal `DEFEND` comes only in the `WAIT` phase, after every player
action of this play (`candidate-A.md` §2.1). Let
`j_g^1 < j_g^2 < j_g^3` be the three slots with `φ(j) = g`. Instruct stack `j_g^r` to move
to `q_g^r` and strike `E_g`.

When `j_g^r` acts, `q_g^r` is free: the only stacks that ever enter `q_g^{1,2,3}` are the
three of group `g`, and they take distinct hexes. So Lemma 4.2 applies. `E_g` is alive
when `j_g^r` acts. This needs an argument, because a stack cannot strike a dead enemy and
the play would then fail to realise `φ`: `E_g` has `hp = T`, the blows assigned to it are
`a_i` for the three `i` with `φ(i) = g`, and the 3-PARTITION promise gives `a_i < T/2` for
every `i`. Any two of them therefore sum to strictly less than `T`, so `E_g` survives its
first two blows and the third striker finds it alive. This holds for **every** `φ` with
`|φ^{-1}(g)| = 3`, not only for those a 3-partition produces, which is what the lemma claims
and what §8 machine-checks. ∎

> **A sentence the earlier draft got wrong.** It argued that if `E_g` had already died then
> "the blow is not needed and the assignment is realised with a strict surplus". That is not
> an argument: if `E_g` is dead, stack `j_g^r` does not strike `E_{φ(j)}` at all, so the play
> does not realise `φ` in the sense the lemma asserts. The draft then fell back on the fact
> that in the only use made of the lemma the three blows sum to exactly `T` — true, but it
> proves a weaker lemma than the one stated. The `a_i < T/2` argument above is the right one
> and costs nothing, since it covers arbitrary `φ`.

**Remark 4.5 (the one real constraint).** The board does impose *something*: an enemy has
six neighbours, so at most six stacks can strike it in one round. That bound never binds
here (three per enemy). It is worth stating because it is the only geometric fact the
construction cannot make disappear, and it is why "featureless" means *complete
reachability plus local seat capacity*, not "positions do not exist".

Lemmas 4.3 and 4.5 are machine-checked exhaustively; Lemma 4.4 is machine-checked for
*every* `φ` on the instances tested, not just the ones a 3-partition produces. See §8.

---

## 5. Damage accounting

**Lemma 5.1 (no player creature dies).** In round 1 of `G_F`, every deployed player stack
has `count = 1` from start to finish.

*Proof.* A player stack of one creature has `hp = 5`. The only damage it can take in
round 1 is retaliation: it strikes `E_g`, `E_g` survives, and `E_g` retaliates for
`max(1, ⌊1 · 1⌋) = 1` by `(★)`. A stack strikes at most once per round, and under `(‡)`
no enemy initiates an attack, so at most 1 damage lands on it. By `MODEL.md` §3,
`firstHPleft` drops from 5 to 4 and `count` is unchanged. (In the `NO_RETALIATION`
variant an enemy may also attack once, for another 1 damage; `2 < 5` still leaves
`count = 1`.) ∎

**Lemma 5.2 (accounting).** Fix any allocation and any play of round 1. For `g ∈ [m]`
let `S_g ⊆ [3m]` be the set of types whose stack struck `E_g`. Then the `S_g` are
pairwise disjoint, and

```
nominal damage delivered to E_g  ≤  Σ_{i ∈ S_g} a_i ,
absorbed damage on E_g           =  min( T , nominal damage delivered ),
```

with the first inequality an equality whenever no striker of `E_g` waited.

*Proof.* Each type has stock one and a slot is homogeneous (`MODEL.md` §9), so a slot
holds at most one creature and each type appears in at most one slot; each stack acts at
most once per round, so it strikes at most one enemy, which gives disjointness. By
Lemma 5.1 the stack of type `C_i` has `count = 1` when it strikes, so by `(★)` its blow has
nominal value `1 · a_i = a_i`; by `candidate-A.md` §2.1 `(‡c)` a stack that waited and met a
defending `E_g` delivers **at most** `a_i`, and any other stack delivers exactly `a_i`.
(At most, not strictly less: the damage formula clamps at 1, so when `a_i = 1` the defence
bonus cannot reduce the blow below its nominal value. The argument only ever needs the
inequality, and stating it as strict would be false on exactly those instances.) Damage
accumulates in `E_g`'s single health pool (`MODEL.md` §3), which holds `T` points, and
damage beyond that pool is discarded (**the overkill rule**, `MODEL.md` §3,
`CUnitState.cpp:202-203`) — which is why the second line is an equality only for
*absorbed* damage, not for delivered damage. No other damage reaches `E_g`: retaliation by
`E_g` damages the *player*, and under `(‡)` no enemy attacks, so no player stack ever
delivers a retaliation. ∎

> The distinction matters and an earlier draft blurred it: writing "damage received by
> `E_g` `= Σ a_i`" is false as soon as the killing blow exceeds the remaining pool, which
> a play is perfectly free to arrange. Nothing downstream needs the equality; Lemma 5.3
> needs only the direction "absorbed reaches `T` ⟹ nominal was at least `T`". A pleasant
> by-product of the correctness chain is that it proves *retrospectively* that every
> successful play has zero overkill: in the tight case of Lemma 6.2 every `Σ_{i∈S_g} a_i`
> equals `T` exactly.

**Lemma 5.3 (kills).** `E_g` is dead at the end of round 1 **only if**
`Σ_{i ∈ S_g} a_i ≥ T`; and it **is** dead if its strikers do not wait and
`Σ_{i ∈ S_g} a_i ≥ T`.

*Proof.* `E_g` is a single creature with `firstHPleft = hp = T`, so by the kill rule of
`MODEL.md` §3 it dies exactly when the damage it has *absorbed* reaches `T`. By Lemma 5.2
absorbed damage never exceeds the nominal total `Σ_{i∈S_g} a_i`, giving the first half; and
if no striker waited, the nominal total is delivered in full, giving the second. ∎

**§5.4 Why the policy `(‡)` is still load-bearing.** One might expect `R = 1` plus
`spd(E_g) = 1 < s` to make the defence's policy irrelevant: the enemies act last, and the
round ends immediately after. It does not, and the machine check caught exactly this.
The destroyed value is read at the *end* of the round, so an enemy attack in the final
phase still matters: it provokes the player stack's **retaliation**, which delivers a
second blow of `a_i` to that enemy inside the same round. With the attacking policy
mistakenly in place, the search reported three kills on an instance whose arithmetic
admits one. This is the candidate-A iteration-1 bug (`../VERIFICATION.md` §3) reproduced
verbatim in the featureless setting. Both repairs of candidate-A §2 work here and both are
checked (§8).

---

## 6. Correctness

**Lemma 6.1 (yes ⟹ yes).** If `(a, T)` is a 3-PARTITION yes-instance then `G_F(a, T)` is
a yes-instance.

*Proof.* Let `{G_1, …, G_m}` be a partition of `[3m]` into triples with
`Σ_{i ∈ G_g} a_i = T`. Deploy `C_i` in slot `i` for every `i` — any injection will do —
and let `φ(i) := g` for `i ∈ G_g`. By Lemma 4.4 there is a play in which every stack
strikes its assigned enemy; by Lemma 5.2 each `E_g` receives `Σ_{i∈G_g} a_i = T`, and by
Lemma 5.3 all `m` enemies die. The destroyed value is `m · 1 = W`. ∎

**Lemma 6.2 (yes ⟸ yes).** If `G_F(a, T)` is a yes-instance then `(a, T)` is a
3-PARTITION yes-instance.

*Proof.* Enemy creatures have value 1 and there are `m` of them, so destroyed value
`≥ W = m` forces all `m` to die. By Lemma 5.3, `Σ_{i ∈ S_g} a_i ≥ T` for every `g`, and
by Lemma 5.2 the `S_g` are pairwise disjoint subsets of `[3m]`. Summing,

```
mT  ≤  Σ_{g=1}^{m} Σ_{i ∈ S_g} a_i  ≤  Σ_{i=1}^{3m} a_i  =  mT,
```

so every inequality is an equality: `Σ_{i∈S_g} a_i = T` for all `g`, and the `S_g` cover
`[3m]`. Finally `T/4 < a_i < T/2` forces `|S_g| = 3` — two elements sum to less than `T`,
four to more. Hence `{S_1, …, S_m}` is a 3-partition. ∎

Note what Lemma 6.2 does *not* use: no geometry at all. The board can only ever *restrict*
which `S_g` are achievable, so the upper-bound direction is geometry-free; all the
geometric work (Lemmas 4.1–4.4) is spent on the yes-direction, where we choose the play.

**Proof of Theorem 4.** Lemmas 6.1 and 6.2, with a construction computable in time
polynomial in the unary encoding of `(a, T)`. Since 3-PARTITION is strongly NP-complete
(Garey–Johnson SP15), `ARMY-ALLOCATION` is strongly NP-hard on this family, and the
family satisfies every restriction listed in the statement — Lemma 4.3 gives complete
reachability. Membership in NP is candidate-A Lemma 3.5 verbatim, so the problem is
strongly NP-complete on this family. ∎

**Proof of Corollary 4.1.** Fix the allocation to `C_i ↦ slot i`. Lemma 6.1 uses no other
allocation, and Lemma 6.2 never mentions the allocation. So the equivalence survives with
the allocation given as part of the input. ∎

**Corollary 6.3 (hit-point objective).** *On the same instances, replace the objective by
**total hit points removed** — absorbed damage, overkill discarded (`MODEL.md` §3,
`CUnitState.cpp:202-203`) — and the target by `W_hp = mT`. The problem remains strongly
NP-hard, with the allocation free or given.*

*Proof.* The total nominal player damage is `Σ_i a_i = mT`, and by Lemma 5.2 enemy `g`
absorbs `min(T, nominal delivered to g)`, with delivered at most nominal (a striker that
waited into a `DEFEND` bonus delivers at most its nominal `a_i`, and strictly less unless the
clamp at 1 holds it up, which needs only the inequality here). Total absorbed is therefore at most
`min(mT, Σ_g T) = mT`, with equality only if every stack strikes, every blow delivers its
full nominal `a_i`, and every enemy absorbs exactly `T` — i.e. `Σ_{i∈S_g} a_i = T` for
every `g` with the `S_g` disjoint and covering `[3m]`, and `T/4 < a_i < T/2` forces
`|S_g| = 3`: a 3-partition, exactly as in Lemma 6.2. Conversely the witness play of
Lemma 6.1 delivers exactly `T` to each enemy, absorbing `mT`. The argument never mentions
the allocation, so it survives with the allocation given. ∎

This corollary is owed to the round-4 external review; see §7.4(b) for the claim it
corrects. Machine check: `../scripts/verify_hp_objective.py` — on the same instance
families as §8 plus the four smallest legal cases, the hit-point relaxation
`max_f Σ_g min(T, Σ_{f(i)=g} a_i)` equals `mT` exactly on the 3-PARTITION yes-instances
(both directions, source decided independently), the 3-partition witness play run in the
reference simulator absorbs exactly `mT` on every yes-instance, and a negative control
confirms the relaxation stays strictly below `mT` on a fixed no-instance.

---

## 7. Where the hardness actually lives

This is the part a referee should read, and it is not flattering to the "allocation"
framing.

**7.1 The allocation has become free.** In `G_F` every type has stock one and every slot
reaches every enemy, so *every* injection of types into slots is equivalent: the multiset
of blows available to the player does not depend on which slot holds which type, and by
Lemma 4.4 every three-per-enemy targeting is realisable from any of them. The decision
that encodes the 3-partition is the **choice of targets**, not the allocation. That is
precisely why Corollary 4.1 holds, and why it is the stronger statement.

So candidate-A §6.1 is answered, but with a twist: the featureless problem is still
strongly NP-hard, and the reason is that a *different* decision took over. The pair
`Theorem 2 + Theorem 4` should be presented as a bracket:

| | what forces the grouping | what the player decides |
|---|---|---|
| candidate-A Thm 2 | board adjacency | how to fill the seats (allocation) |
| Theorem 4 here | nothing | whom to hit (play) |

Reporting only one of the two would misdescribe the source of the difficulty.

**7.2 On this board, but only on this board, a diverse roster is needed.** Both Theorem 2
and Theorem 4 give `3m` distinct types with distinct damage values. On a featureless board
the single-type case is in fact *easy* in the same weak sense:

> **Proposition 7.1.** Suppose the army is a single type of flat damage `d` with stock
> `B`, there are `k` slots and `m` enemy stacks, `R = 1`, the defence plays `(‡)`, and
> every slot reaches every enemy. Then the optimum is computable in `O(m · k · B)` time.
>
> *Sketch.* By (★) a slot holding `c` creatures delivers `c · d` to whichever enemy it
> targets, and by Lemma 5.3-style accounting enemy `g` dies iff the total count aimed at
> it is at least `b_g := ⌈pool_g / d⌉`. Any surplus is wasted, and one slot suffices per
> enemy. So the optimum is `max { Σ_{g∈S} v_g : Σ_{g∈S} b_g ≤ B, |S| ≤ k }` — a 0-1
> knapsack over `m` items **with a cardinality constraint**, solved by the textbook DP
> over (item prefix, budget, cardinality).
>
> **The cardinality dimension is not optional.** An earlier draft claimed `O(m · B)`, which
> silently dropped the constraint `|S| ≤ k`; general cardinality-constrained knapsack needs
> the extra count dimension, and `O(m·B)` is only correct when `k ≥ m`. (The separate
> `O(kB)` DP of candidate-A §5.5 *is* correct as stated: there each slot faces its own
> enemy, so there is no cardinality constraint to carry.)
>
> **Not machine-checked.** This is an algorithmic remark, not a hardness claim; it is
> stated to delimit Theorem 4, and the paper should either check it the way
> `../scripts/dp_single_type.py` checks candidate-A §5.5, or drop it.

So the honest scope is: **on a featureless board, hardness needs a diverse roster**; with
a single type the featureless case degenerates to knapsack. This does **not** support a
roster-diversity axis, and an earlier draft's claim that it does is withdrawn:
`candidate-D-singletype.md` (Theorem 3) shows that a single type suffices for strong
hardness as soon as the reach structure is nontrivial, even with the allocation fixed.
Proposition 7.1 and Theorem 3 together say something sharper than either alone — the
featureless single-type case is easy *because* complete reachability collapses the reach
hypergraph, not because the roster is poor.

**7.3 What the construction does not use.** No obstacles. No flying. No shooting or
ammunition. No spells, heroes, morale or luck. No double-wide creatures. The witness play
uses no `WAIT`, no `DEFEND` and no `MOVE`-only action — it is attack-only in the sense of
§4 — though all three remain available to the player and the no-direction quantifies over
them. No special abilities at all in the primary variant. One round. One creature per
enemy stack.
All `3m` player types are identical except for their damage value; all `m` enemy stacks
are identical. And, the point of the exercise, no wiring from slots to enemies.

**7.4 What it does need.** (a) `3m` distinct damage values — §7.2. (b) ~~The kill
threshold being a step function~~ — **withdrawn**. An earlier draft claimed here, as
candidate-A §5.1 did, that counting hit points removed instead would make the objective
separable and concave and the problem trivial. On *this* construction that is false:
Corollary 6.3 shows the hit-point objective is strongly NP-hard on exactly these
instances. The separable-concave collapse is a property of the matching reach structure of
Theorem 1, not of the objective. What the kill threshold buys this theorem is the natural
value-`1`-per-enemy objective with `W = m`; the hardness itself does not need it. (c) A defence
that does not attack, or `NO_RETALIATION` on the player types — §5.4. (d) The number of
slots `k = 3m` grows with the instance; candidate-A §6.2 remains open. (e) Creature speed
`s = 4m + 8` grows with the instance. Speed is an input in the generalised game, but the
`MODEL.md` §5 coupling "speed *is* initiative" means we cannot raise movement range
without also making the player fastest — which is what we want here, but which a
construction needing a different initiative order could not do.

**7.5 Relation to bin covering.** Stripped of the game, Theorem 4 is bin covering: `3m`
items, `m` bins, cover each bin to level `T`. That is not novel as combinatorics, and the
paper should not pretend otherwise. What is new is that the *game mechanics realise it
with no gadgetry at all* — an open rectangle, one round, and creature statistics that are
legal inputs. The interest is in how little of HoMM3 the hardness needs, not in the
combinatorial core. (Approximation is a different matter: offline bin covering has
approximation schemes, so a "PTAS for the featureless case" would not be a new result —
see `../RELATED-WORK.md`.)

---

## 8. Verification status

Protocol and code: `../scripts/verify_featureless.py`. Mechanics are taken only from
`../scripts/homm3_model.py`; no rule is restated in the verifier.

Six checks. **C1–C5** run for both defence variants (`hold` and `noretal`) on `m = 2`
(6 types, 6 slots, 2 enemies, board 10 × 6) and `m = 3` (9 types, 9 slots, 3 enemies, board
14 × 6) — 46 instance runs in total. **C6 does not**: it runs only at `m = 2`, only under
`hold`, on four instances with sampled allocations, because it is exhaustive and expensive.
An earlier draft said "six checks under both variants at `m = 2, 3`"; that was false and is
corrected here.

| | check | what it establishes |
|---|---|---|
| C1 | complete reachability with all `3m` slots occupied | Lemma 4.3, in the worst case for the player |
| C2 | no slot starts adjacent to an enemy; enemy neighbourhoods are disjoint and non-touching | rules out a degenerate board that still wires slots to enemies |
| C3 | *every* labelled three-per-enemy assignment `φ` is realisable, and the simulated destroyed value equals the arithmetic prediction | Lemma 4.4 in full generality, and Lemmas 5.1–5.3 |
| C4 | exhaustive relaxation over all `f : [3m] → [m] ∪ {skip}` | Lemma 6.2, independently of geometry |
| C5 | exhaustive over all `2^6` occupancy patterns of each enemy's neighbourhood, with every other region saturated | Remark 4.5: blocking is *only* seat capacity |
| C6 | exhaustive play search per allocation on the real crowded board, branching over targets **and** over approach hexes, with a passing stack additionally allowed to vanish | assumption-free cross-check |

C3 settles the yes-direction constructively — an actual play is run in the simulator and
its destroyed value read off — and C4 settles the no-direction. C5 is exhaustive rather
than sampled by a monotonicity argument: `Battle.reachable` is monotone in the blocked
set, so saturating everything outside `N(e_g)` is the worst case, and by Lemma 4.1 the
blockers can only ever live in the deployment row and the enemy neighbourhoods — a step
that inherits Lemma 4.1's restriction to attack-only plays, so C5 certifies attack-only
states. Pure movement is covered separately and only by C6's vanish relaxation.

C6 is the tier that would catch a mis-modelled rule, and it is the expensive one: an
exhaustive search over one allocation's play at `m = 2` costs ≈ 10⁵ nodes, so it is run
on the four smallest legal instances (at `T = 13` the window `T/4 < a_i < T/2` admits
exactly one yes and one no instance; likewise at `T = 16`) with the identity allocation
plus sampled ones. The "vanish" option makes C6 an upper bound that also covers the
MOVE-only action the reference simulator omits (§4, note after Lemma 4.1). The `Geometry`
cache that sits in front of the model's BFS is compared against uncached model calls on
10 800 queries before the tier runs.

**Results.**

```
python3 verify_featureless.py                     # C1-C5, 46 instance runs,  88 s
python3 verify_featureless.py --full --allocs 12  # adds C6,                 342 s
```

* 46 instance runs (16 instances at `m = 2`, 7 at `m = 3`, each under two defence
  variants): **no mismatches**. Every `game = YES` coincides with `3-PARTITION = YES`.
* C3 checked 20 assignments per `m = 2` instance and **1680 per `m = 3` instance** — all
  realisable, all with the predicted value.
* C5 performed 768 (`m = 2`) and 1728 (`m = 3`) saturation checks per instance, all
  exact: the legal approach hexes were the free neighbours of the target in every one.
* C4 returned `m` on every yes-instance and `m − 1` on every no-instance, so the bound is
  tight on the yes side and strictly below `W` on the no side.
* C6, on 4 instances × 13 allocations each, 4 · 10⁵ to 6 · 10⁵ nodes per instance:
  **the exhaustive search value equalled the C4 relaxation bound exactly in all four
  cases** (2 = 2 on the yes-instances, 1 = 1 on the no-instances). Since C4 ignores
  geometry entirely and C6 respects it fully, that is the sharpest statement available
  from a bounded check: on this family the board costs the player nothing.

**One real bug, found by the machine.** The first version of the verifier ran the
attacking defence policy under both variant labels. Under the `hold` label the player
stacks then retaliated and delivered a second blow to their own target, and the search
returned 3 kills where the arithmetic allows 1 — 23 mismatches across both board sizes.
This is the same failure mode as candidate-A iteration 1, and it is the reason §5.4 exists:
`R = 1` plus a slowest defence is *not* enough to make the policy irrelevant.

**What remains unchecked.** In descending order of importance.

1. **What the real engine has and has not confirmed.** The reductions are searched against
   the Python transcription in `../scripts/homm3_model.py`, not against VCMI. Since an
   earlier draft of this file was written, a harness linking the *actual* VCMI battle
   classes has been built and run (`../engine-check/REPORT.md`): 49 cases, 46 exact
   agreements, 3 explained discrepancies (counts as of 2026-08-16 — the harness grows;
   trust `compare.py`'s own output). Stated precisely, so that neither direction is
   overclaimed:
   * **engine-cross-checked:** the combat arithmetic (`DamageCalculator::calculateDmgRange`,
     including the attack and defence factors and the clamp at 1), the health-pool and
     effective-count mechanics (`CHealth`, `CUnitState::damage`, `getCount`), and the
     retaliation-charge mechanics (`CRetaliations`, `ableToRetaliate`) — including all 12
     cases drawn from the reduction constructions;
   * **not engine-checked:** complete battles, obstacle boards, reachability and approach
     selection, turn order over a whole round. No constructed instance of this theorem or
     of Theorem 3 has been played inside VCMI.
   * The three discrepancies are a one-ULP artefact of VCMI's JSON parser loading the
     defence cap `0.7` as `0.7000000000000001`, and they appear only when the defence
     factor is used at all. This theorem's constructions set `Δ = 0` and never invoke it;
     Theorem 3 does invoke it, so `../engine-check/REPORT.md`'s remark that "no reduction
     uses the defence branch" is out of date and Theorem 3's §3.3 handles the point
     directly.
2. **Only `m ∈ {2, 3}`.** Larger `m` needs a smarter search than exhaustive play
   enumeration.
3. **C6 covers four instances and 13 allocations each, not all 13 327.** A full sweep
   would take days at ≈ 25 s per allocation. The gap is covered mathematically by C4
   (which quantifies over all allocations) and by C5 (which quantifies over all blocking
   patterns), but not by one single brute force. An earlier attempt to fold the
   allocation into the search tree with a shared memo — sound, because assuming the
   not-yet-acted slots empty only frees hexes — blew up on the approach-hex component of
   the state and was abandoned; it is the obvious thing to retry if this tier needs to
   scale.
4. **MOVE-only, WAIT and DEFEND are still absent from the simulator.** C6's vanish
   relaxation dominates MOVE-only. `WAIT` and player-side `DEFEND` are not covered by any
   check; the argument that neither can help at `R = 1` is written out — a stack that waits
   or defends still acts at most once, Lemma 5.2 counts blows rather than order, and by
   `candidate-A.md` §2.1 `(‡c)` a waiting stack's blow is *at most* nominal — waiting is
   the only way, at `R = 1`, to meet an enemy whose postponed `DEFEND` has already
   landed — but it is not machine-checked here. (The phase mechanics themselves are
   unit-checked in `../scripts/verify_mechanics.py`, and `../scripts/brute_force.py`
   runs the defence's `(‡)` literally in its `waitdefend` variant.)
5. **Proposition 7.1 is not machine-checked** — flagged in place.

---

## 9. Open problems this leaves

1. **Single type on a featureless board with several creatures per enemy stack.**
   Proposition 7.1 assumes one slot suffices per enemy. Enemy stacks of many creatures,
   where partial kills score, may be harder. (This was formerly described as "the
   remaining route to the roster-diversity dichotomy of candidate-A §5.5". There is no such
   dichotomy: `candidate-D-singletype.md` refutes it. The question is still interesting,
   but it is now a question about *complete reachability*, not about rosters.)
2. **Fixed `k`.** Unchanged from candidate-A §6.2, and now sharper: with the board
   featureless and `k` fixed, the problem is a fixed-dimension covering problem and is
   very likely in P. Proving it would give the contrast result the paper wants.
3. **Natural victory objective.** Theorem 4 still uses the artificial `R = 1` deadline.
   The route suggested by the external review — every item creature a shooter with one
   shot, armies separated by an impassable barrier, so that surviving enemies can never be
   damaged after the first volley — would replace `R = 1` by "eventually eliminate the
   defence". It needs shooting and ammunition in the simulator, which `MODEL.md` §7 keeps
   in the model but `homm3_model.py` does not implement.
4. **Approximation.** See §7.5: the bin-covering core means positive approximation results
   would need to beat what is already known offline.

---

Rejected variants and the reasoning behind them: `attempts/featureless-dead-ends.md`.

---

Status: **proved + machine-checked (bounded).** Theorem 4 and Corollary 4.1 are proved on
paper and confirmed on 46 instance runs at `m = 2, 3` under two defence variants, with
zero mismatches against 3-PARTITION; the geometry lemmas 4.3–4.4 and Remark 4.5 are
machine-checked exhaustively (1680 labelled assignments and 1728 saturation patterns per
`m = 3` instance), and an unrestricted play search branching over both targets and
approach hexes met the geometry-free upper bound exactly on 4 instances × 13 allocations.
The verification found one real bug (§5.4, §8) before passing. Not established: any
`m > 3`; a single unrestricted brute force over all 13 327 allocations; WAIT; and — as
everywhere in this project — conformance of the Python mechanics to the shipped engine.
