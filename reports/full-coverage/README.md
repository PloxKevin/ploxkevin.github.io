# Continuing full mathematical coverage

The verified checkpoint contains 2,735 theorems in 174 Lean files. Its local build,
kernel checks and standard-axiom audit passed with Lean 4.34.1 and the pinned
Mathlib revision. See [the formal audit](lean-checkpoint-9/verification.json).
Twenty-seven modules received fresh kernel replays. The other 147 retain actual
passing replays after identical module sources, transitive local imports and
compiled dependency fingerprints were checked. Every theorem received a fresh
axiom audit and the aggregate was freshly built. Commands, actual execution
directories and original logs are retained.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried, including ordinary surrounding prose, hints and
table rows. The frozen publication ledgers classify 223 exercises as
mathematically complete, 95 partial and 238 pending; 11,866 material units remain
pending review. See [the ledger audit](publication-checks/ledger-checkpoint-9.json).
The validator checks source fingerprints and references; it does not establish
semantic completeness. Further working additions are outside this checkpoint.

Both specific clauses reopened after checkpoint 7 now have actual Lean proofs:
the barrier hint's unconstrained minimizer and the Lyapunov answer's one-sided
function limit. Their full sources were independently reviewed again. Earlier
reports and their recorded classifications remain historical evidence.

The book contains eleven documented teaching corrections. Exact replacements and
reasons are in [material-corrections.json](../../book/coverage/material-corrections.json).
The newest correction states the finite-moment and nonzero-denominator
conditions for the general variance-minimizing policy-gradient baseline.
[Static validation](publication-checks/integration-checkpoint-9.json) passed on
the publication copy. [Browser evidence](browser-checkpoint-9.json) combines
actual prior checks for 28 byte-identical pages with actual new five-width runs
for the changed policy-gradient primer. It asserts no new manual screenshot inspection.
[The checkpoint manifest](checkpoint-9-manifest.json) identifies frozen inputs.
Historical checkpoint 4 correspondence fixes remain in
[the follow-up notes](checkpoint-4-correspondence-notes.json).

From the repository root, reproduce the checks with:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction
```

Use `--resume-kernel` only with matching saved fingerprints.
`python3 book/coverage/validate.py --require-complete` remains a failing gate.
The ongoing objective includes every remaining mathematical material and
exercise claim, exact assumptions and source correspondence, local Lean
verification and GitHub publication. This checkpoint does not complete it.
