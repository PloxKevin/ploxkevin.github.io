# Continuing full mathematical coverage

Checkpoint 26 passed the actual Lean 4.34.1 build, kernel and axiom audit:
9,503 public theorems in 1,167 selected files. [The original audit](lean-checkpoint-26/verification-original.json)
and [its measured execution](verify-checkpoint26-execution-v1.json) retain actual commands and times.
The 11 additions received fresh kernel replays; the 1,156 earlier files retain their
successful replays after exact source, transitive import and dependency fingerprints matched.
Every indexed theorem received a fresh axiom audit.

Coverage remains partial: 517 of 556 exercises are complete,
18 partial and 21 pending. Of 12,774 overlapping
material units, 4,561 are reviewed and 8,213 pending.
[The frozen ledger](lean-checkpoint-26/ledger-audit.json) checks literal fingerprints
and selected declarations. Independent reviews establish source correspondence;
Lean certifies the encoded statements.

The additions cover metric and isometry arguments, conditional distributions,
the scalar convex scenario exercise, wind-model classifications, fractional CVaR
selectors and randomized Gaussian smoothing. MPC components prove safety and
convergence for an explicitly switched controller under stated premises; deriving
the general robust replanning certificate remains an open obligation.

Source53 clarifies finite terminal-set entry, pre-entry controller error bounds
and the scenario theorem's unique original-objective minimizers. [Static checks](integration-26.json)
passed on all 29 pages and 556 exercises. [Browser evidence](browser-checkpoint-26.json)
contains five fresh viewport checks for the changed page and 140 retained checks
for 28 unchanged pages after exact page and QA hashes matched. It includes 48
application captures and ten explicitly skipped targets. Six changed paragraph
captures were inspected; whole-site manual screenshot review remains pending.

[The manifest](checkpoint-26-manifest.json) binds 47,277 frozen inputs.
[The selection](checkpoint-26-selection.json) preserves all 1,156 prior proof sources.
Exact content bindings retain every original checkpoint25 path and byte hash.
Original semantic bodies, hypotheses, commands, failed and passing outputs, and
times remain unchanged. Checkpoint25's completed GitHub Pages delivery is preserved
in the progress history. Checkpoint 26 is [pushed to GitHub](https://github.com/PloxKevin/ploxkevin.github.io/commit/68fa8a62c5085c3dbc92ec6c80e5dfd9f3e2e381).
The [actual Pages workflow](https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/38124319984)
completed successfully, and [live delivery](live-checkpoint-26-attempt2.json)
matched all 31 book asset hashes and the built commit exactly. Full coverage work continues.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce checks into new output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction26.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction26.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction26
```

The local frozen checkout is `reports/full-coverage/checkpoint-26`. Publication
places selected inputs at their original paths. This checkpoint leaves the full
coverage objective unfinished.
