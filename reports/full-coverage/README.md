# Continuing full mathematical coverage

The verified checkpoint contains 4,653 theorems in 425 Lean files. Its fresh
9,350-job build, kernel checks and standard-axiom audit passed with Lean 4.34.1
and the pinned Mathlib revision. See [the formal audit](lean-checkpoint-16/verification.json).
Fifty modules received fresh kernel replays. The other 375 retain actual
passing replays after identical module sources, transitive local imports and
compiled dependency fingerprints were checked. Every theorem received a fresh
axiom audit. Actual commands, execution directories and original logs are retained;
the complete previous report is preserved verbatim beside the current audit.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried, including surrounding prose, hints and table rows.
The frozen ledgers classify 312 exercises as mathematically complete, 62 partial
and 182 pending; 10,944 material units remain pending review.
See [the exact frozen ledger audit](lean-checkpoint-16/ledger-audit.json).
The validator checks source fingerprints and references; independent reviews
establish the specific source correspondences. Further working additions are
outside this checkpoint and do not count as verified coverage.

The book contains 25 documented teaching corrections. Exact replacements,
assumptions and reasons are in
[material-corrections.json](../../book/coverage/material-corrections.json).
The selected additions cover precise finite CMDP occupancy, flow recovery and
linear-program components, Schur complements, Riccati and ellipsoid claims,
thermal extrema and further probability definitions. Exact source reviews retain
the broader gaps in partially covered exercises. The CMDP matrix, vertex and
path-expectation clauses still require further coverage beyond this checkpoint.
Historical compiler, source and review evidence remains unchanged; a deliberate
revision removes two trailing spaces from the linear-program proof and receives
fresh source-matched compiler and kernel checks.

[Static validation](integration-16.json) passed on all 29 pages and 556 exercises;
its page fingerprints match the frozen checkpoint.
[Browser evidence](browser-checkpoint-16.json) retains actual five-width checks
for 22 byte-identical pages and records the failed browser attempt for seven
pages without current passing evidence. Chromium launch was blocked by system
permissions. No new screenshot or manual visual-inspection pass is asserted.
The GitHub source push and live delivery are tracked separately. Live HTTP and
Pages API delivery require actual post-push checks; no live-delivery pass is
asserted here. [The checkpoint manifest](checkpoint-16-manifest.json) identifies
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
