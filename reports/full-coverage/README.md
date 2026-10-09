# Continuing full mathematical coverage

The verified checkpoint contains 1,999 theorems in 100 Lean files. Its local build,
kernel checks and standard-axiom audit passed with Lean 4.34.1 and
the pinned Mathlib revision. See
[the publication-source audit](lean-publication-6/verification.json). Nine modules
received fresh kernel replays. The other 91 reuse actual passing results with identical
module sources, transitive local imports and compiled dependency fingerprints.
Every theorem received a fresh axiom audit, and the aggregate was freshly built.

Coverage is still partial. The frozen ledgers account for all 556 exercises and
6,373 overlapping material review units. At this checkpoint, 173 exercises are
marked mathematically complete, 114 partial and 269 pending; 5,766 material units
remain pending review. These author classifications are separately recorded in
[the ledger integrity audit](lean-checkpoint-6/ledger-audit.json). The validator
checks source fingerprints and references; it does not prove semantic coverage.

The checkpoint includes eight documented corrections: zero Lipschitz constants,
nonlinear integrating-factor wording, nonzero starting points for quadratic
step-size claims, bounded/nonempty infimum hypotheses, a falsely rounded error
bound, and explicit grid endpoint and spacing conventions. Exact changes
and reasons are in [material-corrections.json](../../book/coverage/material-corrections.json).
[Static validation](integration-6.json) and
[source-exact browser evidence](browser-checkpoint-6.json) passed. The browser
evidence retains prior actual checks for unchanged pages and reruns the latest
optimization page at five widths; it does not claim a new run of every page.
The [checkpoint manifest](checkpoint-6-manifest.json) identifies frozen inputs.
The publication copy has an additional passing audit after exactly two trailing
spaces were removed; [the formatting record](publication-formatting-6.json)
records that delta and the fresh checks of the changed import closure.
Historical checkpoint 4's author correspondences required subsequent fixes;
those are documented in [the follow-up notes](checkpoint-4-correspondence-notes.json)
and resolved in the current core ledger.

From the repository root, reproduce the checks with:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction
```

Use `--resume-kernel` only to resume a report directory with matching saved
fingerprints. `python3 book/coverage/validate.py --require-complete` remains a
failing gate until every established mathematical subclaim has been addressed.
The objective includes the remaining material and exercises, exact stated
assumptions, source-to-statement review, complete local verification and final
GitHub publication. Publishing this checkpoint does not close that objective.
