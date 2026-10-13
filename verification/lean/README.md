The reviewed Source91 solution release has a separate selected-proof runtime
at `reports/solution-review/runtime-source91-selected35-v1`. It contains exactly
the same 1,267 selected checkpoint35 proof sources with new 31 asset hashes. The actual
build and all 11,472 axiom checks pass; unchanged module/import kernel evidence is
reused with its original command, workdir and logs. The source-correspondence rebase
for expanded answers remains pending. The canonical working folder retains
11 unselected future files; use the selected runtime for this exact audit.

# Safe Learning: local Lean verification

This project checks selected mathematical statements from the Safe Learning
primers and modules. The coverage ledgers in
[`../../reports/lean-verification`](../../reports/lean-verification/) identify the
HTML exercises, Lean declarations, assumptions and remaining gaps. A theorem
count is not a count of completely verified exercises.

## Reproduce

Install [elan](https://lean-lang.org/install/manual/), then run from the repository:

```sh
cd verification/lean
lake exe cache get
python3 verify.py
```

The toolchain and dependency manifest pin Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The local run used installed Lean
and cached Mathlib dependencies. A fresh checkout needs network access for these
dependencies. No global toolchain setting is changed.

For the expanded book's current audit, preserve the historical report directory:

```sh
python3 verify.py --output ../../reports/book/lean-verification
```

The runner also checks that every dependency's Git revision matches the pinned
manifest and its working tree is clean. It fingerprints compiled dependency
artifacts before and after verification. The historical `book/check_coverage.py` checks the
earlier published source revision. For the continuing full-coverage work, run
`python3 book/coverage/validate.py` from the repository root. Add
`--require-complete` to check whether every remaining mathematical claim is
finished; that gate currently fails because coverage remains partial.

The runner builds the proof modules, replays each module's declarations with
`lake env leanchecker -v SafeLearning.ModuleName`, and prints every theorem's transitive
axiom dependencies. It rejects `sorry`, custom axioms and native evaluation proof
shortcuts. Dependencies are restricted to Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms; individual results may use fewer.
Logs and source/proof SHA-256 fingerprints are written to
`reports/lean-verification/verification.json` and adjacent files.

Per-module replay avoids starting every imported Mathlib environment at once.
The aggregator must contain exactly one import for every audited module and no
declarations. Each completed replay saves its actual exit code and log hash in
`kernel-progress.json`. After an interrupted run, `--resume-kernel` reuses those
results only if all source, project, dependency and log fingerprints still match.
An interrupted or missing result is never treated as a pass.

For a later frozen batch, `--reuse-kernel-from /absolute/path/to/prior/snapshot`
can reuse a prior actual passing kernel result. The module and every transitive
local import must have identical source hashes, and Lean, project pins and the
compiled dependency environment must match. Reused checks retain the original
command, actual working directory and raw log provenance. The new aggregate
build and every theorem's axiom audit still run. Older reports without dependency
artifact fingerprints cause a fresh replay of all modules. Omitting this option
always runs a fresh replay.

The expanded checkpoint is documented in
[`../../reports/full-coverage/README.md`](../../reports/full-coverage/README.md).
Its current selected batch contains 11,472 theorems in 1,267 files.
Three new modules received fresh kernel replays; 1,264 exact earlier results
were reused under source/import and dependency fingerprints. The normal
aggregate build and every theorem's standard-axiom audit ran again. The
actual audit ran in `runtime-checkpoint-35-source90-v1`. The source-only
snapshot mirrors its bytes and contains no copied build cache or earlier trees.

The inventory contains 556 exercises and 12,774 overlapping material units.
539 exercises are complete, 6 partial and 11 pending; 7,896 material units
remain pending. Source correspondence review can reopen entries while their
formal proofs remain valid. Follow the source-only snapshot reproduction
commands in the continuing audit for the exact selected batch. The working
directory also retains unselected historical sources, and its default
aggregate is not the selected checkpoint35 runtime. In a clean published
checkout the selected sources and aggregate occupy their normal paths.

The separate numerical recomputation can be rerun from the repository root with
`python3 verification/numerical.py` (NumPy and SciPy required). Browser QA uses
`node qa/learning_review.mjs --report reports/lean-verification/browser-final.json`;
run `npm --prefix qa ci` and set `SAFELEARNING_CHROMIUM` to a Chromium executable
when the local cached browser path is unavailable.

## Scope

- `PrimersFoundations.lean`: logic, sets, linear algebra, calculus, convexity,
  optimization and selected exercises from primers 0/A/B.
- `PrimersApplied.lean`: probability, dynamical systems, reinforcement learning
  and selected exercises from primers C/D/E.
- `Modules.lean`: selected mathematical families and exercises from modules
  1–7 and 12–15.
- `CoreModules.lean` and `CoreAnalysis.lean`: exercises and general results from
  modules 8–11, including optimization, safety, convergence and validation.
- `BookApplications.lean`: selected general implications for robust tank
  feedback, one-state policy mixing, held-input barriers, scalar disturbance
  tubes and metric Lipschitz safety transfer. The exact source map and limits
  are in `book/review/new-formal-map.json` at the repository root.

The proofs include universal statements about invariance, convex optimality,
contraction, probability bounds, convergence and minimal sample sizes, as well as
exact worked calculations. Coverage remains partial: many exercise subclaims,
stochastic process interpretations and cited research theorems are not encoded.
Numerical recomputation and browser checks are separate evidence, not proofs of
universal mathematical claims.

Kernel replay uses Lean's own kernel. It checks the course declarations against
the imported environment; this run does not freshly replay all transitive
Mathlib dependencies or use an independent proof checker. Lean verifies the
formal statement that was written, so correspondence with the prose also needs
the recorded human-style source review.

Kernel-progress and final-report JSON are installed atomically, preserving the last complete receipt if a write is interrupted.
