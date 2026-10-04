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

Start with [PaperStatements.lean](PaperStatements.lean). It contains 41 explicit proposition contracts with their hypotheses and quantifiers. [PaperProofs.lean](PaperProofs.lean) provides proofs of exactly those contracts. [PaperChallenge.lean](PaperChallenge.lean) is the separate trusted challenge for the official [Lean Comparator](https://github.com/leanprover/comparator).

The challenge's intentional `sorry` placeholders are never imported by the proof library. There are no proof placeholders or project mathematical axioms in the solution. The proof audit permits only `propext`, `Classical.choice` and `Quot.sound` transitively.

- [Paper correspondence](docs/paper-correspondence.md): every numbered result, exact source locations, qualifications and supplementary interfaces.
- [Model conventions](docs/model-conventions.md): ordered planar graphs, external port order, labelled equivalence, coefficient fields and width zero.
- [Verification](docs/verification.md): full compilation, axiom auditing, kernel replay and Comparator commands.

Statement contracts share reviewed mathematical definitions with the library. Review those definitions together with the statements; neither Comparator nor a successful build can establish the meaning of an English theorem automatically.

## Full verification

With Python 3.11 or later:

```sh
python3 scripts/verify.py --clean
```

This rebuilds project artifacts, audits declarations by actual originating module (including private helpers), runs arithmetic/order regressions, and replays every mathematical module with the same pinned Lean kernel. Dependency build artifacts are reused. It is not an independent kernel implementation.

The compact release receipt is [Verification/result.json](Verification/result.json). Its source digest identifies the checked mathematical inputs; local logs are under the ignored `.lake/verification/` directory. The release Comparator run uses trusted local mode on macOS, without a build sandbox or an external kernel. The upstream sandboxed mode is documented separately.

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
