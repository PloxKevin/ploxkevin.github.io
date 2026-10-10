# Continuing full mathematical coverage

The verified checkpoint contains 4,929 theorems in 461 Lean files. Its fresh
9,386-job build, kernel checks and standard-axiom audit passed with Lean 4.34.1
and the pinned Mathlib revision. See [the formal audit](lean-checkpoint-17/verification.json).
Thirty-six modules received fresh kernel replays. The other 425 retain actual
passing replays after identical module sources, transitive local imports and
compiled dependency fingerprints were checked. Every theorem received a fresh
axiom audit. Actual commands, execution directories and original logs are retained;
the complete previous report is preserved verbatim beside the current audit.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried, including surrounding prose, hints and table rows.
The frozen ledgers classify 321 exercises as mathematically complete, 57 partial
and 178 pending; 10,748 material units remain pending review.
See [the exact frozen ledger audit](lean-checkpoint-17/ledger-audit.json).
The validator checks source fingerprints and references; independent reviews
establish the specific source correspondences. Further working additions are
outside this checkpoint and do not count as verified coverage.

The book contains 28 documented teaching corrections. Exact replacements,
assumptions and reasons are in
[material-corrections.json](../../book/coverage/material-corrections.json).
The selected additions prove genuine finite CMDP inverse and spectral claims,
classify actual occupancy-polytope vertices, and cover further probability,
optimization and neural-network exercise components. The grid exercise now gives
exact certificate intervals, and two derivative-bound exercises specify the
positive radius their division requires. Actual path-measure and expectation
correspondences remain beyond this checkpoint. Historical compiler, source and
review evidence remains preserved; no baseline Lean source changed in this audit.

[Static validation](integration-17.json) passed on all 29 pages and 556 exercises;
its page fingerprints match the frozen checkpoint.
[Browser evidence](browser-checkpoint-17.json) retains 95 actual viewport checks
for 19 byte-identical pages and records the failed fresh browser attempt for ten
pages. Chromium launch was blocked by system permissions. No new screenshot or
manual visual-inspection pass is asserted.
The GitHub source push and live delivery are tracked separately. Live HTTP and
Pages API delivery require actual post-push checks; no live-delivery pass is
asserted here. [The checkpoint manifest](checkpoint-17-manifest.json) identifies
all frozen inputs. Historical correspondence and source corrections remain
preserved in their original evidence records.

From the repository root, reproduce the checks with:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction
```

Use `--resume-kernel` only with matching saved fingerprints.
`python3 book/coverage/validate.py --require-complete` remains a failing gate.
The continuing objective includes every remaining mathematical material and
exercise claim, exact assumptions and source correspondence, local Lean
verification and GitHub publication. This checkpoint does not complete it.
