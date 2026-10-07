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

The runner builds the proof modules, replays their declarations with
`lake env leanchecker -v SafeLearning`, and prints every theorem's transitive
axiom dependencies. It rejects `sorry`, custom axioms and native evaluation proof
shortcuts. Dependencies are restricted to Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms; individual results may use fewer.
Logs and source/proof SHA-256 fingerprints are written to
`reports/lean-verification/verification.json` and adjacent files.

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
