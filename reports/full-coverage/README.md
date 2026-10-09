# Continuing full mathematical coverage

The verified checkpoint contains 3,619 theorems in 290 Lean files. Its local build,
kernel checks and standard-axiom audit passed with Lean 4.34.1 and the pinned
Mathlib revision. See [the formal audit](lean-checkpoint-13/verification.json).
Twenty-six modules received fresh kernel replays. The other 264 retain actual
passing replays after identical module sources, transitive local imports and
compiled dependency fingerprints were checked. Every theorem received a fresh
axiom audit and the aggregate was freshly built. Commands, actual execution
directories and original logs are retained.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried, including ordinary surrounding prose, hints and
table rows. The frozen publication ledgers classify 270 exercises as
mathematically complete, 81 partial and 205 pending; 11,248 material units remain
pending review. See [the ledger audit](publication-checks/ledger-checkpoint-13.json).
The validator checks source fingerprints and references; it does not establish
semantic completeness. Further working additions are outside this checkpoint.

Both specific clauses reopened after checkpoint 7 now have actual Lean proofs:
the barrier hint's unconstrained minimizer and the Lyapunov answer's one-sided
function limit. Their full sources were independently reviewed again. Earlier
reports and their recorded classifications remain historical evidence.

The book contains nineteen documented teaching corrections. Exact replacements and
reasons are in [material-corrections.json](../../book/coverage/material-corrections.json).
The newest corrections state the generic classification-radius domain conditions
and mark rounded information calculations as approximations.
[Static validation](publication-checks/integration-checkpoint-13.json) passed on
the publication copy. [Browser evidence](browser-checkpoint-13.json) combines
actual prior checks for 27 byte-identical pages with the recorded failed
browser attempt for the two changed pages. Chromium launch was blocked by sandbox
permissions, so those two pages have no current viewport pass. The changed source
was statically validated. No new manual screenshot inspection is asserted.
The GitHub source push is tracked separately from live delivery. HTTP and the
Pages API currently fail with DNS/network access errors, so no live-delivery
pass is asserted for this checkpoint.
[The checkpoint manifest](checkpoint-13-manifest.json) identifies frozen inputs.
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
