# Two Sources of Hardness in Generalized Heroes of Might and Magic III Combat — artifact

This repository is the complete verification artifact for the paper
*Two Sources of Hardness in Generalized Heroes of Might and Magic III Combat*
(Ivan Parfenchuk, 2026). It contains the full proofs the paper's body
sketches, the executable model, every verification suite the paper's
Section 4 describes, the engine cross-check harness, and the empirical
study of Section 5 — the paper's `\src{...}` pointers resolve against this
tree's root.

## Layout

| Path | What |
|---|---|
| `paper/` | The paper itself: `main.md` (Markdown master), `main.tex`, `main.pdf` |
| `MODEL.md` | The combat model `H3-det`, every rule cited to VCMI source `file:line` |
| `proofs/candidate-A.md` | Full proofs: Theorem 1 (+ Proposition 1.1), Theorem 2 |
| `proofs/candidate-C-featureless.md` | Full proof: Theorem 4 and its corollaries |
| `proofs/candidate-D-singletype.md` | Theorem 3 working document (the paper's Appendix D supersedes it) |
| `proofs/attempts/` | Failed reduction attempts, kept with the reason each breaks |
| `scripts/` | The executable model and every verification suite (stdlib-only Python 3) |
| `verification_manifest.json` | Single source of truth for every number the paper's verification table quotes |
| `engine-check/` | The VCMI engine cross-check: C++ harness, cases, shipped engine outputs, report |
| `empirics/` | Section 5: instance corpus, certified optima, LLM responses, scoring and statistics |
| `VERIFICATION.md` | The verification protocol log, iteration by iteration (Russian) |
| `LIT-REVIEW.md`, `RELATED-WORK.md`, `LIT-AIIDE.md` | Literature notes with per-citation reading depth |
| `STATE.md`, `ASSESSMENT.md`, `CLAUDE.md` | Working documents of the project, kept for provenance (Russian) |

## Running the checks

Python 3, standard library only (the engine cross-check additionally needs a
VCMI checkout and CMake). The full battery:

```
python3 scripts/test_regressions.py        # the doc-consistency battery + regressions
python3 scripts/verify_mechanics.py        # damage-formula tests vs MODEL.md
python3 scripts/brute_force.py             # Theorems 1-2 reductions, exhaustive play
python3 scripts/verify_x3c.py              # Theorem 3 suite (default tier)
python3 scripts/crosscheck_sol.py          # Theorem 3 independent cross-check
python3 scripts/verify_embedding.py        # Lemma D.4 executed end to end
python3 scripts/verify_featureless.py      # Theorem 4 suite
python3 scripts/dp_single_type.py          # Proposition 1.1 DP vs exhaustive play
python3 scripts/verify_hp_objective.py     # Corollary 4.2 suite
python3 empirics/scripts/verify_full_model_optima.py   # certified optima replayed
python3 empirics/scripts/check_ability_shift.py        # ability projection shifts an optimum
```

Section 4.4 of the paper lists the complete reproduction block with expected
outputs; `test_regressions.py` re-runs the cheap suites itself and pins every
counter the paper quotes to the artifact that generates it.

## VCMI provenance

Every rule in `MODEL.md` and every engine number in `engine-check/` cites a
[VCMI](https://github.com/vcmi/vcmi) source location (GPLv2). Two commit
hashes appear in this artifact:

- **`deeab240c8d6db193101669a7702bfc0e4f4e872`** — the public anchor: a
  merge commit on `vcmi/vcmi` `develop` (2026-06-19). Check citations against
  this commit.
- **`b5cee705b`** — the working checkout the harness was actually built
  from: a fork merge whose sole difference from `deeab240` across `lib/`,
  `config/`, `server/` and `test/` is 18 lines in
  `lib/callback/AIFactory.cpp`, a file nothing here cites. Every cited path
  is byte-identical between the two commits.

Scripts that read a VCMI checkout honour the `VCMI_CHECKOUT` environment
variable (default: the author's local path).

## Licenses

- Code (`scripts/`, `empirics/scripts/`, `verification_manifest.json`): MIT (see `LICENSE`).
- Text (`paper/`, `MODEL.md`, `proofs/`, reports and notes): CC BY 4.0.
- `engine-check/` (builds against VCMI classes): GPL-2.0-or-later, matching VCMI (see `engine-check/LICENSE-note.md`).

## Provenance

Most of this artifact was produced with substantial AI assistance under the
author's direction, and went through eleven adversarial review rounds
(multiple independent model families plus the author's own runs) before
publication; the paper's Acknowledgements and Section 4 describe the process
and the paper trail. The review-round documents themselves live in the
project's private working repository; this artifact is the verified result.
