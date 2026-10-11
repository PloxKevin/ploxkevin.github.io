# Continuing full mathematical coverage

Checkpoint 27 passed the local Lean 4.34.1 build, kernel and axiom audit:
9,644 public theorems and lemmas in 1,175 selected files. The
[original audit](lean-checkpoint-27/verification-original.json) and
[measured execution](verify-checkpoint27-execution-v1.json) preserve actual
commands, results and times. Eight additions received fresh kernel replays;
1,167 earlier modules retained their successful replays after exact source,
transitive import and dependency fingerprints matched. The build and all-theorem
axiom audit are fresh.

Coverage remains partial: 519 of 556 exercises are complete, 16 partial and
21 pending. Of 12,774 overlapping material units, 4,574 are reviewed and
8,200 pending. [The frozen ledger](lean-checkpoint-27/ledger-audit.json)
checks literal fingerprints and selected declarations. Independent full-source
reviews establish correspondence; Lean verifies the encoded statements.

The additions complete the conformal-rank and explorer-slope exercises and
eight supporting module units. Five linear-algebra units now have complete
sensor-reconstruction, spectral and residual-orthogonality mappings. Eleven
precise MPC components have proofs under their stated hypotheses. The whole
robust replanning certificate remains pending.

Corrections 54 and 55 clarify the original incremental-stability domains and
the joint-distinctness or independently randomized tie treatment for strict
conformal ranks. [Static checks](integration-27.json) passed on 29 pages and
556 exercises. [Browser checks](browser-checkpoint-27.json) contain ten fresh
viewport checks on the two changed pages and 135 exact retained checks.
The 48 application-region captures were inspected: four fresh regions and
44 unchanged regions. Some narrow-screen formulas extend past the static
image edge; horizontal scrolling and whole-page visual coverage were not
established by those captures. Ten capture targets were explicitly skipped.

[The selection](checkpoint-27-selection.json) retains all 1,167 earlier proof
sources. [The manifest](checkpoint-27-manifest.json) fingerprints the frozen
inputs. Exact content bindings preserve all 47,277 prior frozen paths and
bytes. Original review bodies, hypotheses, commands, failed and passing
outputs and times remain unchanged. Checkpoint 26's completed GitHub Pages
and live delivery remain in the progress history. Checkpoint 27 delivery
awaits an actual push, Pages build and live asset-hash checks.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce checks into new output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction27.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction27.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction27
```

The local frozen checkout is `reports/full-coverage/checkpoint-27`. Publication
places selected inputs at their original paths. The full coverage objective
remains unfinished.
