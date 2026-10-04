# Verification

## Pinned inputs

Lean is pinned by `lean-toolchain`; Mathlib and all transitive packages are pinned by `lake-manifest.json`. The paper source is arXiv:2610.00079v1, with its SHA-256 recorded in the correspondence document. Do not upgrade these inputs when reproducing this release.

After installing [elan](https://github.com/leanprover/elan):

```sh
lake exe cache get
python3 scripts/verify.py --clean
```

The runner requires Python 3.11+, Git and the pinned Lean installation. `--clean` removes only this project's `.lake/build`; it preserves dependency caches. The build checks the complete library, every paper contract and the arithmetic/order regressions. An import-closure check rejects unimported mathematical modules.

The declaration audit uses Lean's actual originating-module metadata, including private and generated helpers. It rejects project axioms and transitive dependencies on anything except `propext`, `Classical.choice` and `Quot.sound`. Source scanning additionally rejects placeholders, native decision axioms and unsafe or partial mathematical definitions. Scanning is supplementary; the compiled-environment audit is the authoritative axiom check.

The replay driver rechecks every mathematical module using the same Lean kernel, with imported pinned dependency artifacts. It does not independently implement the kernel or rebuild the compiler and all dependencies from source. Verification tools themselves are outside the mathematical axiom audit.

Logs are written to `.lake/verification/`, which is ignored and excluded from releases. A compact receipt can be saved with `--report Verification/result.json`. The receipt is written only after every requested stage succeeds and its frozen inputs remain unchanged.

## Official Comparator

[Comparator](https://github.com/leanprover/comparator) compares the exported challenge and solution, checks the permitted axioms and replays the exported solution in Lean. The compatible revisions are pinned in `Verification/comparator-toolchain.json`. Comparator is not a runtime dependency of the mathematical library.

Build it separately from the repository root:

```sh
git clone https://github.com/leanprover/comparator.git .tooling/comparator
git -C .tooling/comparator checkout d03acab154d269c06e60e4de7e4cc85deebff94b
(cd .tooling/comparator && lake +leanprover/lean4:v4.34.1 build comparator lean4export)
```

The upstream lockfile at this commit pins lean4export to `076e8e57707e813375e8f9da8bf989799ace9680`. The explicit toolchain override uses the same compiler as this project.

For reviewed local code on macOS or Linux:

```sh
python3 scripts/verify.py \
  --comparator .tooling/comparator/.lake/build/bin/comparator \
  --lean4export .tooling/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  --local-comparator
```

Local mode uses a transparent command adapter in place of Landrun. It performs the official statement, axiom and kernel checks, but provides **no build sandbox**. The release receipt records this limitation explicitly. The GitHub workflow also uses this trusted-code mode. No external kernel is enabled.

For the upstream sandboxed Linux mode, install [Landrun](https://github.com/Zouuup/landrun), omit `--local-comparator`, and supply `--landrun /path/to/landrun` (or place Landrun in `PATH`). Follow the current upstream operating-system isolation instructions, including its `systemd-run` restriction on affected kernels. Sandboxed Linux execution was not run on the macOS release host.

## Statements and trust

`PaperStatements.lean` contains explicit proposition definitions with all quantified hypotheses and conclusions. `PaperProofs.lean` proves them by the existing implementation. `PaperChallenge.lean` independently declares the same named theorem targets with intentional placeholders. The solution does not import the challenge, and the challenge is excluded from the mathematical audit and default build.

Comparator checks all 41 targets listed in `Verification/comparator.json`, including separate subparts and definition interfaces. It also compares the dependencies appearing in their statements. This establishes that the exported solution proves the reviewed formal challenge; it cannot determine whether that challenge captures the intended English theorem.

The shared imported definitions, toolchain, dependencies and checking tools are trusted inputs. Definitions and proofs remain together in implementation modules; the paper-facing statement and proof interfaces are separate. This is a maintained review interface, not a second independent formalization of the entire mathematical model.

Dependency checkouts must match all nine locked revisions and have no uncommitted changes. The receipt also counts nonfatal compiler/linter warnings; these are not treated as proof failures or silently disabled.

The source digest in the receipt hashes a sorted map of SHA-256 values for the mathematical Lean files, the challenge, both Comparator JSON files, the two checker modules, the Python runner and the Lake/toolchain files. The outer hash is over Python's `json.dumps(map, sort_keys=True)` UTF-8 serialization. It is a verification-input identifier, not a hash of the entire release archive.
