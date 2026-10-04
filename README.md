# Matchgate Width — Lean Formalization

Lean 4 formalization of [When Matchgate Base Collapse Fails: A Qutrit Trichotomy and Unbounded Exact Width](https://arxiv.org/abs/2610.00079v1), by Chenghua Liu and Boning Meng.

The library covers the paper's 30 numbered theorem-level results, its definitions and substantive remarks, and the supporting unnumbered interfaces. Correspondence is reviewed in the explicit ordered-planar model described below. The main construction has rational matchgate realizations and unbounded minimum exact common width, even against equivalent presentations with arbitrary finite domains and complex weights.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The project pins Lean **4.34.1**, Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, and all transitive dependencies in `lake-manifest.json`. Keep the lockfile. Mathlib's download cache is large; no compiler, dependencies or build artifacts are included in this repository.

## Review the statements

Start with [PaperStatements.lean](PaperStatements.lean), which states 41 propositions with their hypotheses and quantifiers written out explicitly. [PaperProofs.lean](PaperProofs.lean) supplies the corresponding proofs. [PaperChallenge.lean](PaperChallenge.lean) presents the same goals to the official [Lean Comparator](https://github.com/leanprover/comparator).

The challenge's intentional `sorry` placeholders are never imported by the proof library. There are no proof placeholders or project mathematical axioms in the solution. The proof audit permits only `propext`, `Classical.choice` and `Quot.sound` transitively.

- [Paper correspondence](docs/paper-correspondence.md): every numbered result, exact source locations, qualifications and supplementary interfaces.
- [Model conventions](docs/model-conventions.md): ordered planar graphs, external port order, labelled equivalence, coefficient fields and width zero.
- [Verification](docs/verification.md): full compilation, axiom auditing, kernel replay and Comparator commands.

The statement interfaces use the library's mathematical definitions. The correspondence and model documents explain how those definitions and hypotheses express the paper's claims.

## Full verification

With Python 3.11 or later:

```sh
python3 scripts/verify.py --clean
```

This rebuilds the project, audits all project declarations, runs arithmetic and ordering regressions, and rechecks every mathematical module with the pinned Lean kernel. Dependency caches are reused. See the [verification instructions](docs/verification.md) to include the official Comparator's 41 statement checks.

The [verification record](Verification/result.json) identifies the checked inputs and completed checks. Generated logs stay under `.lake/verification/`. The [verification documentation](docs/verification.md) describes the checking methods, local and sandboxed execution modes, and kernel used.

## Layout

| Path | Purpose |
|---|---|
| `MatchgateWidth/` | Mathematical definitions and proofs |
| `MatchgateWidth.lean` | Complete library entry point |
| `PaperStatements.lean`, `PaperProofs.lean`, `PaperChallenge.lean` | Reviewed statements, solution interface and Comparator challenge |
| `Verification/`, `scripts/verify.py` | Project audit, kernel replay and meaningful regressions |
| `docs/` | Correspondence, model and verification notes |
| `paper/ITCS-arxiv.tex` | One copy of the exact arXiv v1 source |
| `.github/workflows/lean.yml` | GitHub build and verification workflow |

Code is distributed under [Apache-2.0](LICENSE). See [NOTICE](NOTICE) for the attributed Lean checker adaptation and the paper's separate distribution terms. Citation metadata is provided in [CITATION.cff](CITATION.cff).
