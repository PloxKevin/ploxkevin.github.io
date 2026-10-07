# Safe Learning correctness audit

This audit catalogues all 489 exercises, corrects the issues found in the course,
and adds a local Lean 4.34.1 project with 473 theorem declarations passing build,
kernel replay and a standard-axiom audit. The formal results cover selected
statements and exercise subclaims; this is **not a formal proof of the entire
course**. Numerical examples and source review provide separate evidence.

## Evidence

- [Final Lean result](verification.json): pinned versions, theorem names, kernel
  replay, transitive axiom audit and source/proof fingerprints.
- [Reproduction instructions](../../verification/lean/README.md) and
  [proof sources](../../verification/lean/SafeLearning/).
- Coverage: [primers 0/A/B](primers-foundations-coverage.json),
  [primers C/D/E](applied-coverage.json), [modules 1–7 and 12–15](modules-coverage.json),
  [graded modules 8–11](core-coverage.json), and
  [original modules 8–11](core-original-coverage.json).
- [Course corrections](source-changes.patch) against published commit
  `a477f1d78aa9190c9b06655074573209689b3243`, with [file fingerprints](source-changes.json).
- [Browser result](browser-summary.json): all 26 pages and 489 exercises, including
  dynamic math and expanded mobile layouts.
- [Numerical recomputation](numerical-verification.json): seven independent
  scripts, with logs and script fingerprints.
- [Independent research-statement review](modules-certified-peer-review.json)
  and [module semantic review](modules-review.json).

Corrections include missing conditions for Newton descent and contractions,
probability and safety bounds, zero Lipschitz constants, strict grid margins,
trust-region tangencies, a Gram iteration convergence-rate assumption, and a
false converse concerning circular convolutions. The latter has an exact
orthogonal matrix counterexample checked in Lean.

Coverage records distinguish complete mathematical conclusions, partial proofs
and unformalized exercises. Many stochastic-process interpretations and cited
research results remain unformalized. Initial inventory snapshots may retain
pre-correction snippets and default pending statuses; the coverage/review
sidecars and final fingerprints describe the completed audit. No exhaustive
re-proof of the cited literature or independent recheck of all Mathlib is claimed.
