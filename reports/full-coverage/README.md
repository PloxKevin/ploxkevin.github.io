# Continuing full mathematical coverage

Checkpoint 20 passed the actual system Lean 4.34.1 audit: 8,667 theorems in
1,068 files, a fresh 9,993-job build, kernel verification and a fresh axiom audit
of every theorem. Only `propext`, `Classical.choice` and `Quot.sound` occur.
See [the original formal audit](lean-checkpoint-20/verification-original.json)
and [its actual execution](verify-checkpoint20-execution.json).
All 13 additions received fresh kernel replays. The other 1,055 retain their
original actual passing replays after exact module, transitive local import,
Lean version and dependency artifact fingerprints were checked. The previous
report and raw logs retain their original commands, directories and times.

Coverage remains partial. All 556 exercises and 12,774 overlapping material
review units are inventoried. The frozen ledgers classify 484 exercises as
mathematically complete, 16 partial and 56 pending. There are 4,068 reviewed
material units and 8,706 pending units. See [the frozen ledger audit](lean-checkpoint-20/ledger-audit.json).
The validator checks literal source fingerprints and declarations; independent
reviews establish the specific mathematical correspondence. Future additions
are outside this verified checkpoint and add no verified coverage.

The source47 book contains 47 documented teaching corrections. The latest
corrections specify the hypotheses behind topology and asymptotic statements,
distinguish exact FOCOPS formulas from decimal approximations, and distinguish
the true Gaussian CVaR from a rounded numerical estimate. Exact replacements,
assumptions and reasons are in [material-corrections.json](../../book/coverage/material-corrections.json).
The additions prove the actual finite FOCOPS probability laws, regularized and
hard constrained optimizers, dual derivatives, branch conditions and numerical
root bounds. Further verification practices now have individually reviewed
finite, calibration, planner and scenario proofs. Earlier approved overlapping
material components remain preserved alongside fresh pending gaps.

[Static validation](integration-20.json) passed on all 29 pages and 556 exercises.
[Browser evidence](browser-checkpoint-20.json) covers all 29 pages at five widths:
15 fresh checks on the three corrected pages and 130 retained actual checks on
26 pages after their source bytes and both QA helpers matched exactly. The
31 book assets and QA hashes match the frozen checkpoint. There are 48 screenshot
artifacts and ten explicit skipped captures on pages without capture targets.
The new screenshots have no manual visual pass; the earlier limited top-region
inspection remains historical. Browser checks do not establish mathematical
correctness.

The [checkpoint manifest](checkpoint-20-manifest.json) identifies the exact
frozen inputs. The [selection](checkpoint-20-selection.json) retains all 1,055
baseline proof fingerprints, original compiler evidence and historical inputs.
The [actual freeze](freeze-checkpoint20-execution.json) prepares inputs; the
separate actual audit establishes its formal verification. Located source
passages remain audit evidence; full external papers retain their attributed
reference scope. Original failed and interrupted historical runs are preserved.
GitHub content delivery is being prepared; live delivery has not yet been
asserted for this checkpoint.

From the repository root, reproduce the checks with:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction
```

The reproducible source47 checkout is `reports/full-coverage/checkpoint-20`.
Use `--resume-kernel` only with matching saved fingerprints.
`python3 book/coverage/validate.py --require-complete` remains a failing gate.
The continuing objective includes every remaining mathematical material and
exercise claim, exact assumptions and source correspondence, local Lean
verification and GitHub publication. This checkpoint does not complete it.
