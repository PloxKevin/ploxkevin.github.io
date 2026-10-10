# Continuing full mathematical coverage

The verified checkpoint contains 8,563 theorems in 1,055 Lean files. Its fresh
9,980-job build, kernel checks and standard-axiom audit passed with Lean 4.34.1
and the pinned Mathlib revision. See [the formal audit](lean-checkpoint-19/verification.json).
All 565 added modules received fresh kernel replays. The other 490 retain actual
passing replays after identical module sources, transitive local imports and
compiled dependency fingerprints were checked. Every theorem received a fresh
axiom audit. Actual commands, execution directories and original logs are retained;
the complete previous report is preserved verbatim beside the current audit.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried, including surrounding prose, hints and table rows.
The frozen ledgers classify 475 exercises as mathematically complete, 17 partial
and 64 pending; 8,907 material units remain pending review.
See [the exact frozen ledger audit](lean-checkpoint-19/ledger-audit.json).
The validator checks source fingerprints and references; independent reviews
establish the specific source correspondences. Further working additions are
outside this checkpoint and do not count as verified coverage.

The frozen book contains 44 documented teaching corrections. Exact replacements,
assumptions and reasons are in
[material-corrections.json](../../book/coverage/material-corrections.json).
The selected additions prove genuine finite CMDP inverse and spectral claims,
classify actual occupancy-polytope vertices, and cover further probability,
optimization and neural-network exercise components. The grid exercise now gives
exact certificate intervals, and two derivative-bound exercises specify the
positive radius their division requires. The selected additions also construct actual history-dependent path probability measures
and prove their flow, expected-return and occupancy-polytope correspondences. Historical compiler, source and
review evidence remains preserved; no baseline Lean source changed in this audit.

[Static validation](integration-19.json) passed on all 29 pages and 556 exercises;
its page fingerprints match the frozen checkpoint.
[Browser evidence](browser-checkpoint-19.json) records a fresh pass on all 29 pages
at five widths: 145 actual viewport checks. It includes 48 screenshots and ten
explicitly skipped captures on pages without lab or reference targets. Manual
visual review covers only the top regions of six screenshots; broader visual
review remains pending. The initial layout failure and isolated replay remain
preserved beside the successful run.
The original serial kernel run was interrupted after completed commands were
preserved. Four workers ran the remaining new modules, and the unchanged frozen
verifier then resumed successfully, including a fresh complete axiom audit and
final fingerprint checks. [The resume execution](verify-checkpoint19-resume-execution.json)
records the actual command, directory, times and exit code. The earlier interrupted
execution retains its actual failure status.
GitHub delivery of checkpoint19 is being prepared; checkpoint18 remains the
last verified live delivery until the new push and live checks pass.
[The checkpoint manifest](checkpoint-19-manifest.json) identifies
all frozen inputs. Historical correspondence and source corrections remain
preserved in their original evidence records.

From the repository root, reproduce the checks with:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction
```

The reproducible source44 checkout is `reports/full-coverage/checkpoint-19`.
Further source47 edits and new standalone Lean files are outside this checkpoint.
Use `--resume-kernel` only with matching saved fingerprints.
`python3 book/coverage/validate.py --require-complete` remains a failing gate.
The continuing objective includes every remaining mathematical material and
exercise claim, exact assumptions and source correspondence, local Lean
verification and GitHub publication. This checkpoint does not complete it.
