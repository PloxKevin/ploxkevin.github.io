# Continuing full mathematical coverage

The verified checkpoint contains 1,195 theorems in 37 Lean files. Its local build,
individual kernel replays and standard-axiom audit passed with Lean 4.34.1 and
the pinned Mathlib revision. See
[the formal audit](lean-checkpoint-1/verification.json).

Coverage is still partial. The frozen ledgers account for all 556 exercises and
6,373 overlapping material review units. At this checkpoint, 83 exercises are
marked mathematically complete, 140 partial and 333 pending; 6,290 material units
remain pending review. These author classifications are separately recorded in
[the ledger integrity audit](lean-checkpoint-1/ledger-audit.json). The validator
checks source fingerprints and references; it does not prove semantic coverage.

The checkpoint also corrects three teaching statements: positive Lipschitz
constants are required before dividing by them, zero constants have a separate
global certificate, and the nonlinear-barrier discussion now refers specifically
to cancellation by the preceding exponential integrating factor. Exact changes
and reasons are in [material-corrections.json](../../book/coverage/material-corrections.json).
[Static validation](integration.json) and
[browser checks of the three changed pages](browser-corrections.json) passed.

From the repository root, reproduce the checks with:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-audit.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction
```

Use `--resume-kernel` only to resume a report directory with matching saved
fingerprints. `python3 book/coverage/validate.py --require-complete` remains a
failing gate until every established mathematical subclaim has been addressed.
The objective includes the remaining material and exercises, exact stated
assumptions, source-to-statement review, complete local verification and final
GitHub publication. Publishing this checkpoint does not close that objective.
