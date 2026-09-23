# Формулировки из homm3/paper/main.md (клин-рум выписка, без доказательств)

## §1.2 Contributions (строки 97-126)

### 1.2 Contributions

1. **A formal model of HoMM3 combat cited line by line to the VCMI engine** (Section 2),
   with an executable transcription, and with the combat arithmetic and health mechanics
   cross-checked against the shipped engine classes.
2. **Theorem 1** (Section 3.1): allocation is NP-complete with a *single* creature type,
   `R = 1`, no obstacles and a one-row battlefield. Weak hardness, from PARTITION.
3. **Proposition 1.1** (Section 3.1): on that family, an `O(kB)` dynamic program solves the
   problem, so Theorem 1 is tight and strong hardness there is impossible unless P = NP.
4. **Theorem 2** (Section 3.2): allocation is *strongly* NP-hard, from 3-PARTITION, with
   every creature type of stock one.
5. **Theorem 3 and Corollary 3.1** (Section 3.3): the problem is strongly NP-hard with a
   **single creature type**, and remains so with the allocation fixed to one creature per
   slot. The reduction is from planar exact cover by 3-sets and uses the engine's lower
   clamp on damage as its arithmetic engine. This refutes the roster-diversity conjecture.
6. **Theorem 4 with Corollaries 4.1 and 4.2** (Section 3.4): strong NP-hardness survives on
   an obstacle-free rectangle with *complete reachability* — every stack can attack every
   enemy from the starting position — survives with the allocation given, isolating
   unrestricted target assignment as the hard decision, and survives with the objective
   changed from creatures killed to hit points removed.
7. **A machine-checking methodology** (Section 4) and an honest report of the errors it
   caught. One scope note belongs up front: the checks exercise the constructions on
   bounded instances; the embedding algorithm of Lemma D.4 is implemented step by step —
   with three named subroutine substitutions, disclosed in Appendix D.6 — and validated on
   the whole instance corpus (Section 4.4), but its correctness on *all* inputs — like
   every proof in this paper — rests on the hand proof, not on a proof assistant.
8. **An empirical study** (Section 5) comparing exactly computed optima against allocations
   proposed by three tiers of language models on 145 instances, each allocation completed
   by oracle-optimal play.


## §2.3 The problem (строки 278-310, до строки *Proof.* леммы 2.1)

### 2.3 The problem

> **`ARMY-ALLOCATION`.**
> **Input.** A battlefield `(n, m, obstacles)`; `k` slots with deployment hexes
> `p_1, …, p_k`; a multiset `A` of player creatures as (type, count) pairs; a fixed
> defence — enemy stacks with types, counts and hexes — which plays the fixed policy `(‡)`
> of Section 2.4; a round bound `R` in unary; a target `W ∈ ℤ_{>0}`. Every creature type
> carries a nonnegative integer *value* as part of its tuple (Section 2.2); the objective
> reads the values of enemy types only.
> **Question.** Is there an allocation of `A` to the `k` slots (each slot receiving at most
> one type, each type's total at most its stock) and a sequence of player actions such that
> after `R` rounds against `(‡)` the total value of enemy creatures killed is at least `W`?

`BATTLE-PLAY` is the same question with the allocation given as part of the input;
`ARMY-ALLOCATION` contains it.

Three points on the formulation. The enemy plays one concrete scripted policy, not an
adversarial one, which keeps the problem in NP and matches the informal "against a fixed
defence"; the adversarial version is a different problem. Baking `(‡)` into the problem
rather than taking an arbitrary "deterministic poly-time policy `π`" as input is deliberate:
an arbitrary encoded program with a promised running time is not a syntactically checkable
input restriction, a circuit encoding would repair that at no gain, and every theorem uses
`(‡)` anyway — hardness for the one fixed policy is the stronger statement. The objective
counts **whole creatures killed**, weighted by the per-type value. That is the game's own
accounting: a stack at one hit point fights at full strength, so hit points removed without
a kill buy the player nothing in that round. It is *not*, however, the sole source of
hardness — counting hit points removed collapses only the matching-reach family of
Theorem 1 to a separable concave sum; on the family of Theorem 4 the hit-point objective
remains strongly NP-hard (Corollary 4.2). And `R` is given in unary so that evaluating a
certificate is polynomial.

**Lemma 2.1 (membership).** `ARMY-ALLOCATION ∈ NP`.


## §2.4 The garrison policy (строки 319-372)

### 2.4 The garrison policy

All four theorems use the same scripted defence, and it has to be pinned down precisely,
because "hold position" does not determine an action: `H3-det` retains movement, `WAIT` and
`DEFEND`.

> **(‡)** If the stack has not waited this round, issue `WAIT`; on its postponed
> activation, issue `DEFEND` at its current hex.

Both are shipped actions. `WAIT` postpones the stack's terminal action into the round's
`WAIT` phase, which runs after all `NORMAL`-phase activations, in *increasing* speed
order (R9); `DEFEND` (R13) ends the turn without moving or attacking and grants `+20 %`
defence — an integer bonus with a floor of `+1` — until the stack next receives a turn.
Three consequences are used throughout:

* no enemy ever initiates an attack, so no player stack ever delivers retaliation damage;
* a waiting or defending enemy still retaliates when struck — neither action consumes the
  retaliation charge;
* **the one-round lemma**: in round 1, the blow of a player stack that did not wait lands
  at its `NORMAL`-phase activation, before any enemy's postponed `DEFEND`, and therefore
  meets the un-raised defence — *regardless of relative speeds*; and every blow, waiting
  or not, delivers at most its nominal damage, since raising the target's defence can
  only lower `f_def`. **Every statement quantifying over an arbitrary play is therefore
  phrased as "at most the nominal damage"**; equalities are asserted only for the
  constructed witness plays, which never wait.

The lemma's scope is exactly one round, and both ways it fails outside that scope are
worth stating, because an earlier justification ("no blow ever meets the bonus") claimed
too much and was refuted by external review. A player stack that itself waits is
scheduled in the `WAIT` phase by *increasing* speed, so a slower enemy's postponed
`DEFEND` can land first and the player's postponed blow then meets the bonus — for such
blows only the inequality survives. And for `R ≥ 2` the bonus persists past the round
boundary until the enemy's next activation, so a fast player striking early in round 2
meets the bonus left over from round 1. All four theorems set `R = 1`; a multi-round
extension must redo this analysis.

An earlier version of `(‡)` issued `DEFEND` at the stack's own turn. For the theorems the
two are interchangeable — every constructed player stack is strictly faster than every
enemy — but they part company on the empirical corpus of Section 5, whose natural
instances contain enemies *faster* than the player, and there the old policy made six
recorded optima unattainable (Section 5.1 gives the history and the machine checks that
close it). The present `(‡)` was adopted after being verified reduction by reduction by
external review; the mechanics it stands on — the `WAIT`-phase order, the bonus
arithmetic and duration, and the retaliation-charge neutrality of both actions — are
unit-checked against the cited engine lines, and the searches of Section 4 include a
variant in which the defence executes `(‡)` literally, phase by phase (Section 4.4).

That the policy is load-bearing is not obvious. The first version of Theorem 1 used an
attacking garrison and was wrong: an enemy that attacks provokes a *retaliation*, which
delivers a second blow to that same enemy inside the same round, and the reduction then
decides subset-sum with the wrong budget. Section 4.3 tells the story.

---


## Формулировка со строки 385

> **Theorem 1.** `ARMY-ALLOCATION` is NP-complete, already for instances with `R = 1`, a
> **single creature type** in the player's army, one creature per enemy stack, no obstacles,
> and a battlefield of one row.

## Формулировка со строки 410

> **Proposition 1.1.** On the family of Theorem 1 — single creature type, `R = 1`, policy
> `(‡)`, damage under `(★)`, **one creature per enemy stack**, and a *matching reach
> structure* in which slot `j` reaches exactly one enemy `E_j` and each enemy is reached by
> exactly one slot — `ARMY-ALLOCATION` is solvable in `O(k·B)` time and `O(B)` space, `B`
> being the stock.

## Формулировка со строки 441

> **Theorem 2.** `ARMY-ALLOCATION` is **strongly** NP-hard, already for `R = 1`, no
> obstacles, no abilities, and instances in which every creature type has stock exactly one.

## Формулировка со строки 472

> **Theorem 3.** `ARMY-ALLOCATION` is **strongly** NP-hard, already for `R = 1`, a **single
> creature type** in the player's army, one creature per enemy stack, all enemy creatures of
> one type and value 1, flat damage, no abilities, and static impassable hexes as the only
> terrain feature. With Lemma 2.1 it is strongly NP-complete on this family.

## Формулировка со строки 477

> **Corollary 3.1 (fixed allocation).** The same instances remain strongly NP-hard when the
> allocation is given: fix one creature in every slot. `BATTLE-PLAY` is strongly NP-hard on
> single-type instances.

## Формулировка со строки 506

> **Lemma 3.2 (resource lemma).** Let `0 < μ < 1` and `D(c) = max(1, ⌊μc⌋)`. If stacks of
> sizes `c_1, …, c_r ≥ 1` each deliver at most `D(c_i)` to one target and the total is at
> least 3, then `Σ c_i ≥ 3`, with equality iff `r = 3` and `c_1 = c_2 = c_3 = 1`.
>

## Формулировка со строки 625

> **Theorem 4.** `ARMY-ALLOCATION` is **strongly** NP-hard already for instances with
> `R = 1`; **no obstacles and no abilities of any kind**; every creature type of stock one,
> one creature per enemy stack; a rectangular open battlefield of six rows and `4m + 2`
> columns; and
> **complete reachability** — in the starting position, with every slot occupied, every
> player stack can attack every enemy stack.

## Формулировка со строки 632

> **Corollary 4.1.** The same instances are hard with the allocation *given*. `BATTLE-PLAY`
> is strongly NP-hard on obstacle-free boards with complete reachability.

## Формулировка со строки 635

> **Corollary 4.2 (hit-point objective).** On the same instances, replace the objective by
> **total hit points removed** — absorbed damage, with overkill discarded — and the target
> by `W_hp = mT`. The problem remains strongly NP-hard, with the allocation free or given.

Throughout, `(★)` denotes the specialization of the damage formula used by Theorems 1, 2
and 4: give every player type attack `α` and every enemy type defence `α`, so `Δ = 0`,
`f_att = f_def = 1`, and a stack of `c` creatures of flat per-creature damage `d` delivers
nominal damage `c·d`. Theorem 3 deliberately breaks this and uses the defence factor.
