# Continuing full mathematical coverage

The verified checkpoint contains 2,463 theorems in 147 Lean files. Its local build,
kernel checks and standard-axiom audit passed with Lean 4.34.1 and the pinned
Mathlib revision. See [the formal audit](lean-checkpoint-8/verification.json).
Twenty-five modules received fresh kernel replays. The other 122 retain actual
passing replays after identical module sources, transitive local imports and
compiled dependency fingerprints were checked. Every theorem received a fresh
axiom audit and the aggregate was freshly built. Commands, actual execution
directories and original logs are retained.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried, including ordinary surrounding prose, hints and
table rows. The frozen publication ledgers classify 208 exercises as
mathematically complete, 99 partial and 249 pending; 11,946 material units remain
pending review. See [the ledger audit](publication-checks/ledger-checkpoint-8.json).
The validator checks source fingerprints and references; it does not establish
semantic completeness. Further working additions are outside this checkpoint.

Both specific clauses reopened after checkpoint 7 now have actual Lean proofs:
the barrier hint's unconstrained minimizer and the Lyapunov answer's one-sided
function limit. Their full sources were independently reviewed again. Earlier
reports and their recorded classifications remain historical evidence.

The book contains ten documented teaching corrections. Exact replacements and
reasons are in [material-corrections.json](../../book/coverage/material-corrections.json).
The two new corrections state the necessary initial projection for degenerate
power iteration and the determinant modulus for complex Cayley transforms.
[Static validation](publication-checks/integration-checkpoint-8.json) passed on
the publication copy. [Browser evidence](browser-checkpoint-8.json) combines
actual prior checks for 27 byte-identical pages with actual new five-width runs
for the two changed pages. It asserts no new manual screenshot inspection.
[The checkpoint manifest](checkpoint-8-manifest.json) identifies frozen inputs.
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
