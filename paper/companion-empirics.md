# Companion note: the certified optimum against one-shot model allocations

**Status.** This note is part of the verification artifact
(github.com/uson1x/homm3-hardness) for the paper *Two
Sources of Hardness in Generalized Heroes of Might and Magic III Combat* (Ivan
Parfenchuk, 2026). It is **not part of the paper's claims**: the paper's results are the
four hardness theorems and Proposition 1.1, and nothing in the paper depends on the
numbers below. The note carries the empirical study that earlier drafts printed as the
paper's Section 5, verbatim except for the editorial changes listed at the end of this
preamble. Its durable content is the benchmark — 145 instances of `ARMY-ALLOCATION` small
enough to solve exactly, each with a certified optimum (an upper bound met by a witness
play), and 870 model responses scored against those certificates — and everything needed
to recompute every number here ships in `empirics/` of the artifact.

**How it relates to the paper.** The instances live in the same fragment `H3-det-melee`
as the theorems (paper, Section 2.2); the optima and scores are `(‡)` numbers under the
garrison policy of Section 2.4 of the paper; the certificates are computed by the
reference simulator in Python floats and re-derived under the exact rationals the theorems
are stated over (paper, Section 4.2; the measurement is `exact_arithmetic_crosscheck.py`,
its row in the suite table of the artifact's `README.md`). The paper's Section 1.2 points
here in one sentence and claims nothing about the outcome.

**Reproducing.** From the artifact root:

```
python3 empirics/scripts/verify_full_model_optima.py  # every certified optimum, full action model
python3 empirics/scripts/certify_scores.py            # every per-response score, full action model
python3 empirics/scripts/check_defend_policy.py       # (‡) replay; --legacy-defend = negative control
python3 empirics/scripts/stats_recheck.py             # every statistic quoted in Section 3 below
python3 empirics/scripts/exact_arithmetic_crosscheck.py  # floats vs exact rationals (re-runs the three suites twice)
```

The regression battery `scripts/test_regressions.py` pins every number this note quotes —
the ratio table, the `k`-bucket rows, the Spearman pair, the geometry-removal points, the
ability-projection tallies and the instance/response counts — to the artifact that
generates it, exactly as it did when the text was the paper's Section 5.

**Editorial changes relative to the paper's former Section 5 (review round 15).** The
section headings are renumbered 1–4; cross-references that read "Section 2.4", "Section
4.2" now say "of the paper"; the reference "(Section 4.4 table)" now points at the suite
table in the artifact's `README.md`, where that table is rendered. No number, table row,
observation or limitation was changed. The conflict note in Section 2 (the models under
test belong to the family that assisted in writing the paper) stays here and is echoed in
the paper's Acknowledgements.

---

## 1. The question, and a framing rule

The theorems are asymptotic. This section asks a different and more concrete question: on
instances small enough that the optimum can be computed exactly, how close to it do
one-shot, model-proposed allocations come? To our knowledge no paper in this genre measures the gap
between an exactly computed optimum and the decisions of contemporary models, which is why
we include it. One framing rule first, because the word "agent" overpromises: **the
measured object is the value of a model-proposed allocation under oracle-optimal tactical
completion**. The models are one-shot allocation solvers here, not HoMM3-playing agents.

## 2. Design

The corpus is 145 instances of `ARMY-ALLOCATION` in four families, with slot counts
`k ∈ {2,…,7}`: a corridor family (60), a "flower" family with three deployment hexes per
enemy (13), and two natural open-board families (36 + 36). The 72 natural instances take their creature
statistics from the original game (extracted from `CRTRAITS.TXT`); the 73 corridor and flower
instances are synthetic, built to mirror the reductions. Even in the natural families the
statistics are **projected** rather than shipped verbatim, since `H3-det` needs flat damage:
each creature's damage range is collapsed to `dmg_min`. Every instance has `R = 1`, no
shooters and no double-wide creatures. The projection also drops every combat **ability** —
`CRTRAITS.TXT` carries only the numeric block — so a stack labelled `Devil` carries a Devil's
numbers without `BLOCKS_RETALIATION`, a `Crusader` strikes once rather than twice, and a
`Psychic Elemental` hits one target rather than every adjacent one. We count the affected
creatures against VCMI's `config/creatures/*.json` in three scopes, so that the disclosure
cannot understate the projection by picking a flattering subset. Under the narrowest scope —
the five abilities that would change the modelled melee arithmetic itself —
47 of the 72 natural instances name at least one affected creature
(`BLOCKS_RETALIATION` on 53 type-slots,
`ATTACKS_ALL_ADJACENT` on 20, `RETURN_AFTER_STRIKE` on 13, `FIRE_SHIELD` on 8,
`ADDITIONAL_ATTACK` on 5). Adding five more combat-adjacent abilities the projection also
drops (`SPELL_AFTER_ATTACK` on 28, `HP_REGENERATION` on 19, `MAGIC_RESISTANCE` on 12,
`MANA_DRAIN` on 5, `LIFE_DRAIN` on 2)
raises that to 65. Under the widest scope — every shipped ability whatsoever
(`FLYING` alone marks 128 type-slots, `HATE` 73) — all 72 are affected: no natural instance
fields a creature exactly as the game ships it.
The per-instance lists are
`empirics/results/ability_projection.json`, generated by
`audit_ability_projection.py`. The measurements are internally valid — both sides of every
ratio are computed in the same fragment — but "statistics from the original game" means
the numbers alone, not the creatures, and a certified optimum is the optimum of the
*projected* instance: under the shipped abilities the optimal allocation could differ.
How much it can differ is measured rather than conjectured: restoring a single dropped
ability — the Efreet Sultan's `hateGenies`, `+50%` against genies — moves the certified
optimum of `naturalS-k6-02` from 1136 to 2020, so on that instance the projected optimum
is 56% of the optimum of the instance its creature names describe
(`empirics/scripts/check_ability_shift.py`, re-certified on both sides and pinned by the
battery).

Every instance ships with a **certified** optimum, and the certificate is a pair rather than
a single number: an upper bound from a reachability relaxation that dominates every legal
play — including waiting, pure movement, and paths opened by enemy deaths — together with an
allocation and a play attaining that bound in the simulator. An allocation achieving a value
is on its own no evidence of optimality; it is the meeting of the two that is
(`empirics/scripts/verify_full_model_optima.py`, all 145 pass, and
`empirics/scripts/certify_scores.py`, which does the same with the allocation held fixed and
certifies all 870 per-response values). One scope note on arithmetic: these certificates are
computed by the reference simulator in Python floats, whereas the theorems are stated over
the exact rationals of Section 2 of the paper, and the two do not agree on every possible damage call
(paper, Section 4.2). Whether they agree on *these* numbers is therefore measured rather than
assumed: `empirics/scripts/exact_arithmetic_crosscheck.py` re-runs all three certifications
with an exact-rational damage routine installed and requires every recorded optimum, replay
and score to be reproduced — they are (the suite table in the artifact's `README.md`), so the optima and scores below are
certified under both arithmetics.

> **A discrepancy found by external review, and how it was closed.** The corpus was
> generated with a scripted defence that **takes no action at all** (`enemy_policy:
> "hold"`), while an earlier version of the paper's policy `(‡)` had every enemy issue
> `DEFEND` at its own turn. The two differ exactly when an enemy acts before the player
> stack that strikes it — false for all 73 corridor and flower instances, true on 53 of
> the 72 natural ones — and the difference was not cosmetic: under `DEFEND`-at-turn,
> **six of the 145 recorded optima were not attainable at all** — `naturalM-k3-04`
> (recorded 1722 against a generous upper bound of 1564), `naturalS-k2-05` (867 vs 624),
> `naturalS-k5-05` (3111 vs 2826), `naturalS-k6-01` (285 vs 190), `naturalS-k7-01`
> (4311 vs 3895), `naturalS-k7-03` (2136 vs 1068). In `naturalS-k2-05`, for instance, the
> Dragon Flies have speed 13 against the player's speed 6, so they defend before the
> player's blow, their defence rises from 10 to 12, and the blow the corpus records as
> killing (`⌊5·4⌋ = 20` against 20 hit points) delivers `⌊5·4·0.95⌋ = 19` instead.
>
> The resolution is the policy Section 2.4 of the paper now defines: `(‡)` waits, then defends, so
> every enemy's `DEFEND` lands in the `WAIT` phase — after every non-waiting player blow,
> regardless of speeds. Under this `(‡)` the recorded numbers are exact, and the claim is
> machine-checked from both sides rather than argued. The witness side:
> `empirics/scripts/check_defend_policy.py` replays every recorded optimal allocation
> through the attack-only play search in a phase-aware simulation whose defence executes
> `(‡)` literally — `WAIT` at the `NORMAL` activation, `DEFEND`, with the bonus live in
> the damage formula, at the postponed one — and requires exact equality with the
> recorded optimum: 145 of 145 pass, and `empirics/scripts/certify_scores.py` applies the
> same replay to all 870 scored responses. The bound side: the ghost-reach relaxation of
> `empirics/scripts/verify_full_model_optima.py` prices every blow at nominal damage and
> dominates every legal play, so it upper-bounds every `(‡)` play as well. As a negative
> control, the same replay under the old `DEFEND`-at-turn policy
> (`check_defend_policy.py --legacy-defend`) reproduces all six violations above — plus
> eight more, the exact replay being sharper than round 5's generous bound — which is the
> evidence that the phase machinery is live rather than vacuously green. The optima,
> baselines and responses below therefore stand as `(‡)` numbers, not as numbers of a
> scripted-defence variant; the theorems never depended on this corpus either way.

The model's task is the pre-battle allocation only. After it commits, the battle is played
out by exhaustive search over attack-only plays — each stack passes or performs
`WALK_AND_ATTACK`, branching over targets and over every legal approach hex. This is
deliberately generous: we do not want to penalize a model for tactics it did not choose. As
with the optima, the search omits `WAIT` and `MOVE`-only actions, so the value it credits to
an allocation is not on its face an optimum over the whole action model, and a referee is
right to ask whether the published ratios are therefore understated. They are not: the same
relaxation closes with the allocation held fixed instead of quantified over, and all 870
scored responses meet that upper bound (`empirics/scripts/certify_scores.py`, all pass) —
and, as described above, the same script certifies each response's value under `(‡)` by
phase-aware replay, so numerator and denominator alike are `(‡)` numbers.
Each instance appears in two prompt variants:
**assisted**, where the prompt lists which enemy stacks each slot can reach, and **raw**,
where it gives only coordinates and the distance rule. The headline uses `assisted`, because
the claim under test is about the allocation decision, not about hex arithmetic.

Three tiers of one model family were run — `claude-haiku-4-5`, `claude-sonnet-5`,
`claude-opus-5` — **one completion per cell**, no tools, no simulator access, identical
sampling settings across tiers. A conflict note: the same model family assisted
in writing this paper (the Acknowledgements name the models); the subjects here ran
one-shot, without tools, and saw only the task prompts. One provenance limitation is flagged rather than hidden:
the version history preserves every response byte-for-byte and every score is recomputed
from those artifacts, but no per-call parameter manifests survive, so the sampling
conditions themselves (temperature, one-shot discipline) rest on the run protocol, not on
a recorded artifact. One completion per cell means every number below describes
a single realized run: there are no repeats, and therefore no uncertainty intervals; we
draw no conclusions that would need them. The full matrix is 870 cells (3 models × 145
instances × 2 variants) and is complete: tasks were administered in batches of ten, and 12
initially missing cells (token-limit truncations concentrated on hard `sonnet` raw cases,
plus two lost responses) were filled by separate single-task runs rather than dropped —
an easier protocol, which is a heterogeneity we flag rather than hide; the refill lowered
one figure (`sonnet` raw, 0.992 → 0.991) and is reported as such. Both stages of the
response set — the 858-cell batched run and the completed 870-cell matrix — are preserved
in the artifact's version history with the twelve refilled cells identifiable exactly, so
the shift is reproducible, not anecdotal. Responses were scored
against the certified optima; a response that violates the stock budget is invalid and
scores zero, since the budget is the constraint that makes the problem a knapsack. All
three scorer strictness columns (`strict`, `valid_only`, `repaired`) agree to three
decimals, and in the final matrix every one of the 870 responses parsed and was
budget-legal, so the treatment of invalid responses drives nothing.

## 3. Results

Ratio to the certified optimum, and the fraction of instances solved exactly:

| player | assisted | exact | raw | exact |
|---|---|---|---|---|
| `claude-haiku-4-5` | 0.926 | 76.6 % | 0.881 | 74.5 % |
| `claude-sonnet-5` | 0.997 | 97.9 % | 0.991 | 97.9 % |
| `claude-opus-5` | 0.998 | 97.2 % | 0.997 | 97.9 % |
| greedy-value heuristic | 0.954 | 79 % | — | — |
| greedy-density heuristic | 0.899 | 57 % | — | — |
| 100-sample random search baseline | 0.971 | — | — | — |

(The last row is a *search* baseline — the best of 100 random legal allocations per
instance — so it consumes 100 attempts where each model consumes one; it is a yardstick,
not a like-for-like competitor.)

Three observations, all descriptive of this single run.

1. **On this run the gap sits between the weakest tier and the mid tier, not between the mid
   tier and the frontier.** Sonnet and Opus score within 0.001 of each other — a difference
   of about one instance, well within what run-to-run noise or a ceiling effect could
   produce, so we read it as "similar on this benchmark", not as evidence about saturation.
   Haiku loses 7.4 % of the available value and misses the optimum on roughly one instance
   in four — worse than the better of the two greedy heuristics.
2. **The weak tier is below the strong tiers at every slot count, but its scores do not
   decline with the slot count.** Every `k` bucket, assisted:

   | `k` | 2 | 3 | 4 | 5 | 6 | 7 |
   |---|---:|---:|---:|---:|---:|---:|
   | `claude-haiku-4-5` | 0.981 | 0.973 | 0.857 | 0.946 | 0.952 | 0.828 |
   | `claude-sonnet-5` | 1.000 | 1.000 | 1.000 | 0.993 | 1.000 | 0.990 |
   | `claude-opus-5` | 1.000 | 1.000 | 1.000 | 0.993 | 0.998 | 0.995 |

   Haiku's worst buckets are `k = 7` and `k = 4` and its best is `k = 2`, but the sequence
   is **not** monotone — it rebounds at `k = 5` and `k = 6` — and the per-response rank
   correlation between `k` and the ratio is only weakly negative (Spearman `-0.19`, and `-0.25`
   on the natural families alone) — a modest association, not the strong ordering suggested by
   quoting `k = 2`, `4` and `7` alone. Two confounds compound this: the family mix changes with `k`, since the flower family exists
   only at `k ∈ {3, 6}` and contributes ten extra instances at `k = 6`, and the natural
   instances at different `k` draw unrelated creatures and budgets. Restricting to the two
   natural families, the only ones present at every `k`, does not restore a decline either
   (`0.965, 0.943, 0.737, 0.902, 0.915, 0.701`).

   **An earlier draft of this paper claimed monotone degradation in `k` and called it the
   study's most informative figure.** That claim was false, and it was reached by quoting
   `k = 2, 4, 7` and passing over the rebound. We retract it. **We assert no scaling law in
   `k`.** What survives is the tier separation of observation 1, which does not involve `k`.
   Sonnet and Opus stay above `0.985` at every `k`.
3. **Supplied geometry helped mainly the weak tier.** Removing reachability from the prompt
   cost Haiku 4.5 percentage points, Sonnet 0.61, and Opus 0.027 on this run (unrounded, Opus
   scores `0.9976` assisted against `0.9973` raw) — the Opus figure amounts to about one
   instance and is therefore not a measurement at one completion per cell.
   (These are the unrounded gaps as `stats_recheck.py` prints them; an earlier draft
   quoted 0.6 and 0.03, rounded from two different provenances.)

## 4. Limitations, in the text and not in a footnote

The instances are small — they have to be, since the optimum must be computed exactly — and
the 100-sample random baseline already reaches 0.971. The defensible claim is therefore "on
this benchmark, one-shot weak-tier allocations systematically fell short of an exactly
known optimum", **not** "language models cannot solve an NP-hard problem", and **not** any
claim about how the shortfall scales with `k` — observation 2 retracts that. The strong tiers in fact solve these small instances; the
difficulty the theorems describe lives in the asymptotics, and this study illustrates that
rather than contradicting it. The design limits are worth listing plainly: one completion
per cell, so every comparison is descriptive of a single run and differences of a few
thousandths are not evidence of anything; the protocol is heterogeneous (858 cells in
batches of ten, 12 refills in single-task contexts, and the refills sat non-randomly on
hard cases); the `k`-trend is confounded with family composition (observation 2); only one
model family was tested, so a cross-vendor comparison is future work; and
reinforcement-learning agents were not measured, because neither of the two HoMM3 RL
environments we examined can express a pre-battle allocation at all. A publication-grade
version of this study would use fresh single-task contexts throughout, repeated calls per
cell with paired intervals, a balanced generator, and at least one more model family; until
then this section claims description, not inference.

