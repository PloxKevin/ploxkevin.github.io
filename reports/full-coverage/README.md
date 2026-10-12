# Continuing full mathematical coverage

Checkpoint 30 passed the local Lean 4.34.1 build and standard-axiom audit:
11,080 public theorems and lemmas in 1,242 selected files. The 45 additions
passed 90 separate compiler commands and received fresh kernel replays in
the [first actual audit](lean-checkpoint-30/verification-original.json).
The [final audit](lean-checkpoint-30-final-css-v1/verification-original.json)
checked the corrected mobile stylesheet, rebuilt the aggregate and reran
every theorem's axiom audit. Its 1,242 earlier successful kernel results were
reused only after exact module, transitive import and dependency identities
matched. There are no nonstandard axiom dependencies.
[Actual commands and times](verify-runtime-checkpoint30-final-css-execution-v1.json)
retain the real runtime directory; no compiler execution in the later
source-only snapshot is claimed.

Coverage remains partial: 535 of 556 exercises are complete, 8 partial and
13 pending. Of 12,774 overlapping material units, 4,770 are reviewed and
8,004 pending. The [working ledger](lean-checkpoint-30/ledger-audit-working-v1.json)
and [frozen ledger](lean-checkpoint-30-final-css-v1/ledger-audit-frozen-v1.json)
passed integrity checks. Independent reviews establish source correspondence;
Lean checks the encoded statements. Whole-exercise decisions preserve their
explicit hypotheses. Component results do not silently complete an exercise.

The additions cover foundational norm, linear-algebra, convergence and
optimization material; delayed control, Gaussian-process calculations,
thermal Bellman bounds, viability and continuous-control examples; and
monitoring, spike and discrete trajectory probability results. Corrections
66–79 repair exact values, rounding, dimensions and theorem assumptions.
[Their actual application](source66-79-corrections-application-v3.json)
retains the original text and fourteen full-page parser checks. The
[owner integration](owner30-reviewed-candidate-integration-v2.json) preserves
the five original ledgers and exact forward/inverse mapping evidence.
General Filippov trajectory existence, the remaining module exercises and
other mathematical teaching material remain in the review queue.

[Static book checks](integration-30-final-css-v1.json) passed on 29 pages,
556 exercises and 21 application labs. [Source-exact fresh browser checks](browser-checkpoint-30-changed-pages-final-v1.json)
passed on all six actual changed pages at five viewport widths each. Five
additional widths were checked on the unchanged optimization primer. The
initial page-list mistake is retained in the original reports and closed by
the separate fresh Primer 0 run. The application-region screenshot review is
bounded; it does not claim whole-page visual coverage. Long display formulas can extend beyond a capture while
remaining inside scroll containers. The CMDP page's two long inline
guarantees now scroll within the column on small phones; [actual mouse-wheel
checks](cmdp-mobile-math30-v1.json) reached both ends at 320px and 360px.
Original failed checks are preserved alongside the subsequent passing checks.

The [selection](checkpoint-30-selection.json) retains all 1,197 earlier
proof sources. The [manifest](checkpoint-30-manifest.json) identifies the
1,298 files in the compact source-only snapshot. Earlier snapshots and Lean
build output were not copied. Historical mathematical bodies, assumptions,
reviews, failures, outputs and times remain at their original hashed paths
and in Git history. Only three unused Applied proof metadata entries are
omitted from the frozen ledger; every claim and original raw ledger is retained.

Checkpoint 30 is published at content commit `ae9e7865`. Its GitHub Pages
workflow completed successfully, and the [fresh live check](live-checkpoint-30-attempt2.json)
verified all 31 asset hashes. The [actual push](publication30-content-push-v1.json)
and [actual check](live30-content-confirmation-execution-v2.json) preserve their
commands, outputs and times. The first live attempt ran while Pages was still
building and remains recorded as unsuccessful. Checkpoint 29's successful
content and metadata delivery is retained. Full mathematical coverage work
continues; delivery does not establish completion of the remaining material.

To reproduce the selected Lean audit and ledger from the local source-only
snapshot, use fresh report paths:

```sh
cd reports/full-coverage/checkpoint-30
python3 book/coverage/validate.py --output reports/ledger-reproduction30.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction30
```

The published repository contains selected inputs at their original paths.
Its [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
and archived audit records remain available in Git. The full coverage
objective remains unfinished.
