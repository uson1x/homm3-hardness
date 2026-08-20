# Related Work

Draft of the Related Work section. English, for the paper. Companion to `LIT-REVIEW.md`
(Russian), which records the search protocol and the novelty verdicts behind the framing
chosen here.

Every paper described below was read in full, not from its abstract. Papers cited for
context only (classical hardness results, survey entries) are marked as such.

---

## 1. Complexity of turn-based tactics and battle subgames

### 1.1 Fire Emblem (Gao, 2019)

Gao [Gao19] gives the only prior complexity study of a commercial turn-based tactical
role-playing game. He fixes a simplified Fire Emblem model — grid of floor and wall tiles,
Manhattan distance, `Mov = 6` for every unit, damage `Atk − Def` with automatic counter
attack, deterministic scripted enemies of two kinds ("patient" and "impatient") — and
proves two results. *Simplified FE*, the question whether the player has a winning
strategy, is PSPACE-complete, by implementing Viglietta's open-close door and crossover
gadgets [Vig14] and reducing from TQBF. *Poly-round FE*, the same question with a round
budget given in unary, is NP-complete, by reduction from Rectilinear Monotone 3-Bounded
3-SAT, and remains so on cycle-free maps, without healing units, and with weapon
durability bounded by a constant. He notes the results transfer to Final Fantasy Tactics,
Tactics Ogre and Disgaea.

Two features of Gao's model matter for the comparison with our results. First, **every
numeric attribute is a constant bounded by 8**; HP, Atk, Def and Mov never scale with the
instance. His hardness is therefore purely combinatorial — it comes from routing units
through a map, from the geometry of enemy aggro ranges, and from the SAT structure encoded
in that geometry, never from arithmetic on large numbers. As a consequence his
NP-completeness is, trivially, strong NP-completeness. Second, **the player's army is
given**: there is no allocation decision anywhere in the model. The player chooses where
units move and what they attack, not how much force to commit.

Our results are complementary rather than comparable. Theorems 1 and 2 fix the geometry to
a corridor or three rows, use one round, and let the hardness come entirely from the
arithmetic of splitting a force; Theorem 4 removes the geometry altogether. Only Theorem 3
puts weight on the board, and it uses it to encode a planar incidence structure rather than
to route units through a map. Gao fixes the arithmetic and lets the hardness come entirely
from the geometry.

### 1.2 Attrition games on graphs (Furtak and Buro, 2010)

The closest prior result to ours, and the one that shapes our claims most, is Furtak and
Buro [FB10]. They study an *attrition game*: a directed graph whose nodes are units with
integer `⟨health, attack⟩`, an edge `x → y` meaning `x` may attack `y`, two players moving
simultaneously in discrete rounds, damage accumulating and units dying at health `≤ 0`.
The model is deliberately an abstraction of small-scale real-time-strategy combat with
movement removed. A systematic sweep of the AIIDE proceedings (2005–2025, workshops
included) and of CIG/CoG (2008–2025) — two independent passes over ~2900 titles, with
every flagged abstract read — found no other hardness result about combat or force
allocation at either venue in their entire history; [FB10] stands alone there.

Three of their results bear on ours.

* **Theorem 1 (tractable core).** For one unit against `n`, the optimal target ordering is
  obtained by sorting targets by decreasing `a_i / ⌈h_i / a_0⌉` and never switching target
  before a kill. This is the polynomial boundary of the problem, and it is worth stating
  in any paper about force allocation: with a single attacker and no budget split, focus
  fire is provably optimal and computable by sorting.
* **Theorem 3.** With `n` targets carrying kill rewards `r_i` and a white unit that will
  not survive, choosing the reward-maximal target ordering is NP-hard, by reduction from
  0-1 Knapsack. The knapsack capacity is the attacker's *remaining lifetime*: killing
  target `j` costs `⌈h_j / a_0⌉` rounds and pays `r_j`.
* **Theorem 7.** In *attrition games with attack partitioning* (APAG), where a unit may
  divide its attack power among all of its potential targets, deciding whether white has a
  pure winning strategy is NP-hard, by reduction from Subset Sum. In the construction a
  single white unit holds `σ` attack power, must spend `σ − n` of it on one large enemy,
  and wins exactly when the remaining `n` points can be split among enemies whose health
  values realise a subset summing to `n`.
* **Theorem 8.** Adding either a round cap or a survivor-count objective yields NP-hardness
  again from Subset Sum; the proof partitions a *set of attacking units* so that each part's
  total attack power exactly matches the health of one of two targets.

Theorem 7 is, in a different game skin, the combinatorial mechanism of our Theorem 1: a
homogeneous attacking resource split across enemies, each of which dies if and only if its
share reaches its health threshold. Theorem 8 is the shape of our Theorem 2, restricted to
two targets. **We do not claim the mechanism as new.** Our claims against [FB10] are
narrower and are stated in §4 below: the resource we split is a native, player-facing
action of a shipped game rather than a modelling device; the map from allocation to
reachable enemy is realized by board geometry rather than chosen as a
graph; and our hardness is strong, whereas every numeric hardness result in [FB10] is weak
(Subset Sum and Knapsack throughout, with the PSPACE-completeness of Corollary 6 requiring
polynomially bounded health).

We also note that [FB10] closes with exactly the question our Theorem 1 sits inside:
"what is the smallest `k` for which the `k` vs. `n` problem is NP-hard?"

### 1.3 Strategic defence games (de Haan and Wolf, 2018)

De Haan and Wolf [dHW18] prove that winner determination in *Greedy Spiders* on planar
graphs is PSPACE-complete, and abstract the construction into metatheorems covering any
round-based two-player game that implements "defence positions" and "destroyable paths".
By requiring one player to commit in advance to a polynomial-time strategy with a
polynomial-size description they obtain the first Σᵖ₂- and Πᵖ₂-hardness results for
computer games, and apply them to tower defence.

Despite the name, no numeric resource is allocated anywhere in that paper: the in-game
currency is used only to discretise time into rounds, and the reductions are from TQBF over
graph reachability. It is relevant to us as the natural home of the *adversarial* variant
of our problem (see §5), not to Theorems 1 and 2.

### 1.4 Tower defence and real-time strategy

Suttichaya [Sut17] proves that placing `k` turrets on a grid to maximise the shortest
start-to-exit path is NP-hard: turret *placement* as a geometric blocking problem, with no
force-allocation content. Beyond [FB10] we found no complexity result for any real-time
strategy title; the frequently assumed "StarCraft is NP-hard" result is [FB10], whose
motivating figure is a StarCraft II combat scene.

---

## 2. Complexity of card games, and where partition arguments already appear

Card games are the part of the games-complexity literature where allocation and partition
arguments are established, and two of these results are closer to us than anything in the
tactics literature.

**Hearthstone.** Hoffmann, Lynch and Winslow [HLW20] study single-turn puzzles from the
Boomsday Lab expansion under three generalisations (scaling hand, board and deck size).
Their Theorem 3.1 reduces 3-PARTITION to board-scaled *Lethal*: the player's board holds
`3n` minions with attack values `4a_1, …, 4a_{3n}`, the opponent holds `n` taunt minions
with `4S/n` health each, total attack equals total enemy health so no attack may overkill,
and the winning assignments of attackers to targets are exactly the solutions of the
3-PARTITION instance. Theorems 3.2 and 3.3 give weak NP-hardness from 2-PARTITION for the
hand- and deck-scaled versions, and the authors observe that multiplicative buff cards let
their 2-PARTITION reductions yield strong NP-hardness as well.

This is the closest published relative of our Theorem 2: heterogeneous attackers of unit
multiplicity, assigned to targets with exact health thresholds, hardness via 3-PARTITION,
in a shipped commercial game. **A referee will know this paper, and any claim that strong
NP-hardness is new in this genre would be wrong.** Our Theorem 2 differs in what is being
decided — the pre-battle allocation of an army to slots, with the slot geometry deciding
reachability — rather than in the combinatorial technique, which is the same.

**Netrunner.** Bosboom and Hoffmann [BH17] prove mate-in-1 for the Runner and mate-in-2 for
the Corp weakly NP-hard in generalised Netrunner, by reduction from 2-PARTITION: spending a
numeric resource across gates with exact thresholds.

**Flesh and Blood.** Romão, de Paula and Ueda [RPU25] model one aggressive turn of Flesh
and Blood as an integer linear program: each card is played for attack, pitched for
resources, or held for defence, and the FAB-AGGRO objective maximises total attack subject
to a pitch budget. They show FAB-AGGRO contains 0-1 Knapsack by mapping items to cards
(attack = profit, pitch cost = weight) and conclude NP-hardness, with FAB and FAB-MIDRANGE
following as generalisations. The paper states no decision problem and proves no membership
result, and the hardness is weak: the authors themselves point to dynamic programming as a
route to pseudo-polynomial algorithms.

The relevant distinction for us is what the knapsack ranges over. In [RPU25] it ranges over
*which cards to play* — item selection from a heterogeneous pool, the classical setting. In
our Theorem 1 there is a single creature type and every creature is on the field; nothing
is selected, and the only free variable is how the stock is divided among slots.

**Other card-game results, for context.** UNO is NP-hard even for a single player
[DDHUUU14]; perfect-information Hearthstone is PSPACE-hard [Zha23]; Magic: The Gathering is
Turing-complete [CBH19].

---

## 3. Composition, allocation, and the classical ancestry

Two lines of work outside games contain the mathematics our reductions rely on, and we cite
them rather than let a referee raise them.

**Allocation with thresholds.** With a single creature type, `R = 1`, and each slot facing
one enemy, our problem is exactly: choose `S ⊆ [k]` maximising `Σ_{j∈S} v_j` subject to
`Σ_{j∈S} a_j ≤ B` — 0-1 Knapsack [Kar72], and with `v_j = a_j` the max subset-sum problem
whose decision version is PARTITION [GJ79, SP12]. With unit-multiplicity heterogeneous
attackers and per-slot thresholds it is a form of BIN COVERING, shown strongly NP-hard by
Assmann, Johnson, Kleitman and Leung [AJKL84]. Neither observation is a criticism of the
theorems — they are what makes the reductions go through — but stating them plainly is the
honest way to present a hardness result whose source problems are fifty years old.

**Military force allocation.** The static Weapon-Target Assignment problem, assigning
weapons to targets to minimise expected surviving value, was shown NP-complete by Lloyd and
Witsenhausen [LW86]; see Ahuja et al. [AKJO07] for exact and heuristic algorithms. Its
hardness comes from a nonlinear product objective under probabilistic attrition, not from
kill thresholds, so it is an ancestor rather than a competitor.

**Colonel Blotto.** The game-theoretic literature on splitting a force across battlefields
[Har08, Rob06, ADHLMS16, BDDHS17] runs in the opposite direction: its headline results are
polynomial-time algorithms for equilibrium computation, including the indivisible-unit
discrete case [Har08]. Hardness appears there only when the resource stops being
homogeneous [DSST21]. No Blotto paper establishes NP-hardness for fixed per-battlefield
thresholds, which is the structure our kill rule imposes. The closest equilibrium-flavoured
statement of our mechanic is shared-effort games with a project threshold [PTW23], where
the single-agent best response is again a knapsack.

**Composition rather than allocation.** Ponomarenko and Sirotkin [PS20] prove that optimal
team choice in the auto-battler Dota Underlords is NP-complete via maximum-density-`k`-
subgraph and maximum edge-weighted clique. This is the exact complement of our framing:
there the difficulty is entirely in *which* units to field, and the arrangement is free;
in our Theorem 1 there is nothing to choose and the difficulty is entirely in the split.

---

## 4. Heroes of Might and Magic III

There is no prior complexity result for any title in the Heroes of Might and Magic, King's
Bounty, Disciples, Age of Wonders or Master of Magic series. We are aware of two academic
papers on HoMM3, neither of which studies complexity.

Diochnos [Dio10], at this venue, models the random secondary-skill offers of the level-up
process, gives an `O((1/ε²) ln(1/δ))` sampling algorithm for estimating the induced skill
distribution, validates it experimentally, and observes that the game's pseudo-random
generator produces few distinct sequences. Kowalski et al. [KMPPP18] generate balanced
HoMM3 maps from strategic terrain features. Neither concerns combat, army allocation, or
hardness.

**Positioning.** Against this background we state our contribution narrowly and without
claiming the underlying phenomenon as new.

1. **A formal model of HoMM3 combat, exhaustively regression-tested on bounded instances
   and engine-cross-checked**, derived line by line from the VCMI reimplementation, with a
   source citation for every rule. Prior game-complexity papers in this genre, including
   [Gao19] and [HLW20], describe their rules in prose. We treat the engine as the
   specification, make the transcription auditable, and — for the combat arithmetic and the
   health mechanics, though not for whole battles — compare it against the shipped engine
   classes themselves.
2. **Theorem 1: allocation is NP-complete with a single creature type.** The mechanism —
   splitting a homogeneous attacking resource across threshold-guarded targets — is that of
   [FB10, Thm. 7]. What is new is that in HoMM3 the split is not a modelling device but a
   literal game action performed before every battle, that the resource is a discrete count
   of creatures rather than a divisible scalar, and that the map from allocation to
   reachable enemy is realized by board geometry rather than chosen as
   part of the construction.
3. **Theorem 2: the general problem is strongly NP-hard.** This strengthens the weak
   hardness of [FB10] and [RPU25] for the allocation question specifically. It does not
   claim strong hardness as new in the genre: [HLW20] reduce from 3-PARTITION in
   Hearthstone, and every number in [Gao19] is a bounded constant.
4. **Two independent sources of strong hardness, and a positive result separating them.**
   Theorem 1 needs no choice of what to bring and yields weak hardness only — with one
   creature type, `R = 1` and a matching reach structure the problem admits an `O(kB)`
   dynamic program, so Theorem 1 is tight there. Theorem 2 obtains strong hardness from
   heterogeneous damage values under a *trivial* reach structure. Theorem 3 obtains it from
   target selection on a planar incidence reach structure with a *single* creature type,
   and Corollary 3.1 keeps it with the allocation fixed. Theorem 4 removes the board wiring
   altogether and keeps strong hardness on an open rectangle with complete reachability.
   The separation, not any single reduction, is the contribution: in every family we
   exhibit, what distinguishes the tractable case from the hard ones is the **reach
   hypergraph**, not roster diversity (a description of our examples, not a dichotomy —
   round 4 objected to the word "classification" here, correctly). An earlier version of
   this paragraph proposed a roster-diversity boundary as a hypothesis; Theorem 3 refutes
   it, and we state no such roster-diversity boundary.
5. **Verification methodology.** Every reduction was checked by bounded search against
   an executable transcription of the rules (scope itemized in the paper's §4), and the
   arithmetic was additionally compared
   against the shipped engine's own battle classes. The checks found five substantive
   errors — an unrealisable one-row geometry, a lemma invalidated by the retaliation rule,
   a verifier that ran the wrong defence policy under both variant labels, an optimum
   evaluator that branched over targets but not over approach hexes, and a contaminated
   prompt batch in the empirical study — all reported in full rather than silently
   corrected. We are not aware of another paper in this genre that machine-checks its
   reductions at all.

---

## 5. Open directions suggested by the neighbours

* **Adversarial defence.** Replacing our scripted policy by an optimising opponent moves
  the problem out of NP. The metatheorems of [dHW18] suggest the second level of the
  polynomial hierarchy as the likely landing place if one player is strategically
  restricted, rather than PSPACE.
* **Positionless allocation — settled.** [FB10] lets an attacker fan out over all targets;
  Theorems 1 and 2 force a slot to face one enemy. Whether hardness survives when every
  slot reaches every enemy was the referee question we most expected, and Theorem 4 answers
  it: it does, with the allocation decision becoming irrelevant and the difficulty moving
  wholesale into target selection.
* **Native deployment formations.** All four theorems take the slot-to-hex map as input,
  which is a genuine generalisation beyond lifting the board and roster bounds; the shipped
  game reads it from fixed formation tables. Recovering any of the results under native
  formations is open.
* **Fixed slot count.** The shipped game has `k = 7`. All constructions need `k` to grow;
  a matching polynomial algorithm for constant `k` would complete the picture.
* **Approximation.** [Laf18] pairs speedrunning hardness with an FPTAS and FPT results, and
  is a good model for what this genre rewards. The knapsack structure of our objective
  suggests a PTAS for `R = 1`.

---

## References

[ADHLMS16] Ahmadinejad, Dehghani, Hajiaghayi, Lucier, Mahini, Seddighin. From Duels to
Battlefields: Computing Equilibria of Blotto and Other Games. AAAI 2016.

[AJKL84] Assmann, Johnson, Kleitman, Leung. On a dual version of the one-dimensional bin
packing problem. *Journal of Algorithms* 5(4):502–525, 1984.

[AKJO07] Ahuja, Kumar, Jha, Orlin. Exact and Heuristic Algorithms for the Weapon-Target
Assignment Problem. *Operations Research* 55(6):1136–1146, 2007.

[BDDHS17] Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin. Faster and Simpler
Algorithm for Optimal Strategies of Blotto Game. AAAI 2017.

[BH17] Bosboom, Hoffmann. Netrunner Mate-in-1 or -2 is Weakly NP-Hard. arXiv:1710.05121,
2017.

[CBH19] Churchill, Biderman, Herrick. Magic: The Gathering is Turing Complete. FUN 2021,
LIPIcs 157, art. 9.

[DDHUUU14] Demaine, Demaine, Harvey, Uehara, Uno, Uno. UNO is hard, even for a single
player. *Theoretical Computer Science* 521:51–61, 2014.

[dHW18] de Haan, Wolf. Restricted Power — Computational Complexity Results for Strategic
Defense Games. FUN 2018, LIPIcs 100, art. 17, pp. 17:1–17:14.

[Dio10] Diochnos. Leveling-Up in Heroes of Might and Magic III. FUN 2010, LNCS 6099,
pp. 145–155.

[DSST21] Dehghani, Saleh, Seddighin, Teng. Computational Analyses of the Electoral College:
Campaigning Is Hard But Approximately Manageable. AAAI 2021.

[FB10] Furtak, Buro. On the Complexity of Two-Player Attrition Games Played on Graphs.
AIIDE 2010, pp. 113–119.

[Gao19] Gao. The Computational Complexity of Fire Emblem Series and similar Tactical
Role-Playing Games. arXiv:1909.07816, 2019.

[GJ79] Garey, Johnson. *Computers and Intractability: A Guide to the Theory of
NP-Completeness*. Freeman, 1979.

[Har08] Hart. Discrete Colonel Blotto and General Lotto games. *International Journal of
Game Theory* 36(3–4):441–460, 2008.

[HLW20] Hoffmann, Lynch, Winslow. Mad Science is Provably Hard: Puzzles in Hearthstone's
Boomsday Lab are NP-hard. arXiv:2010.08862, 2020.

[Kar72] Karp. Reducibility Among Combinatorial Problems. In *Complexity of Computer
Computations*, Plenum Press, 1972, pp. 85–103.

[KMPPP18] Kowalski, Miernik, Pytlik, Pawlikowski, Piecuch, Sękowski. Strategic Features and
Terrain Generation for Balanced Heroes of Might and Magic III Maps. IEEE CIG 2018.

[Laf18] Lafond. The complexity of speedrunning video games. FUN 2018, LIPIcs 100, art. 27.

[LW86] Lloyd, Witsenhausen. Weapons allocation is NP-complete. *Proc. 1986 Summer
Conference on Simulation*, Reno, NV, 1986.

[PS20] Ponomarenko, Sirotkin. Dota Underlords game is NP-complete. arXiv:2007.05020, 2020.

[PTW23] Polevoy, Trajanovski, de Weerdt. When Effort May Fail: Equilibria of Shared Effort
with a Threshold. arXiv:2312.01513.

[Rob06] Roberson. The Colonel Blotto game. *Economic Theory* 29(1):1–24, 2006.

[RPU25] Romão, de Paula, Ueda. Optimizing for aggressive-style strategies in Flesh and Blood
is NP-hard. arXiv:2501.11683, 2025.

[Sut17] Suttichaya. Desktop Tower Defense Is NP-Hard. PRICAI 2016 Workshops, LNCS 10004,
pp. 19–25, Springer, 2017.

[Vig14] Viglietta. Gaming is a hard job, but someone has to do it! *Theory of Computing
Systems* 54(4):595–621, 2014.

[Zha23] Zhang. Perfect Information Hearthstone is PSPACE-hard. arXiv:2305.12731, 2023.
