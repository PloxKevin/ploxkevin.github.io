# Continuing full mathematical coverage

Checkpoint 28 passed the local Lean 4.34.1 build, kernel and axiom audit:
9,896 public theorems and lemmas in 1,186 selected files. The
[original audit](lean-checkpoint-28/verification-original.json) and
[measured execution](verify-checkpoint28-execution-v1.json) preserve actual
commands, results and times. Eleven additions received fresh kernel replays;
1,175 earlier modules retained successful replays after exact source,
transitive import and dependency fingerprints matched. The build and
all-theorem axiom audit are fresh.

Coverage remains partial: 523 of 556 exercises are complete, 14 partial and
19 pending. Of 12,774 overlapping material units, 4,621 are reviewed and
8,153 pending. [The frozen ledger](lean-checkpoint-28/ledger-audit.json)
checks literal fingerprints and selected declarations. Independent source
reviews establish correspondence; Lean verifies the encoded statements.

The additions cover 21 whole foundation units and 26 whole module units,
including four complete exercises. They address residual identification,
integer allocation, derivatives and Jacobians, affine interval bounds,
CROWN radii, sensor commissioning and double-integrator walls. Remaining
MPC, barrier, stochastic and other material obligations stay pending.

Corrections 56–60 clarify MPC state domains and row constraints, probability
dependence, zero-weight box corners and the sensor threshold rounding.
[Static checks](integration-28.json) passed on 29 pages and 556 exercises.
[Browser checks](browser-checkpoint-28.json) contain 20 fresh viewport
checks on four changed pages and 125 exact retained checks. Of 48 application
captures, eight fresh regions and 40 retained regions were inspected; ten
capture targets were explicitly skipped. Some narrow-screen formulas extend
past static captures. [Separate actual mouse-wheel checks](source60-four-page-math-scroll28-v3.json)
establish access to both ends of all eight overflowing containers on the
four changed pages at 390px. The original static reviews retain their exact
scope and times; whole-page visual coverage is not claimed.

[The selection](checkpoint-28-selection.json) retains all 1,175 earlier
sources. [The manifest](checkpoint-28-manifest.json) fingerprints frozen
inputs. Exact content bindings retain all 48,662 prior frozen paths and bytes.
Original mathematical bodies, hypotheses, reviews, failed and passing commands,
raw outputs and times remain unchanged. Checkpoint 27's completed content and
metadata GitHub Pages delivery is preserved in the progress history.
Checkpoint 28 is prepared; its push, actual Pages workflow and live hashes
remain pending. Full mathematical coverage work continues.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce into new output paths:

```sh
python3 book/validate28_v1.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction28.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction28.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction28
```

The local frozen checkout is `reports/full-coverage/checkpoint-28`.
Publication places selected inputs at their original paths. The full coverage
objective remains unfinished.
