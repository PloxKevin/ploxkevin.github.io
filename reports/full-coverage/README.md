# Continuing full mathematical coverage

Checkpoint 25 passed the actual Lean 4.34.1 build, kernel and axiom audit:
9,369 public theorems in 1,156 selected files. [The original audit](lean-checkpoint-25/verification-original.json)
and [its measured execution](verify-checkpoint25-execution-v1.json) retain the actual commands and times.
The 12 additions received fresh kernel replays; the 1,144 earlier files reuse their
original successful replays only after exact source, transitive import and dependency
fingerprints matched. Every indexed theorem received a fresh axiom audit.

Coverage remains partial: 514 of 556 exercises are complete,
19 partial and 23 pending.
Of 12,774 overlapping material units, 4,500 are reviewed and
8,274 remain pending. [The frozen-ledger check](lean-checkpoint-25/ledger-audit.json)
checks exact literal fingerprints and selected declarations. Independent reviews establish
source correspondence; Lean checks certify the encoded statements.

The new proofs cover a barrier-control example, the quadratic twenty-point grid,
scalar calculus, Gaussian models and conditioning, and precise temporal multiplier
components. The corrected shifted-tanh answer(b) has a complete source review with
selected universal order lemmas. The three temporal components retain their exact
hypotheses. The whole answer(c) and neural-network exercise remain unfinished.

The Source52 website assets are byte-identical to checkpoint24. [Static validation](integration-25.json)
passed on all 29 pages and 556 exercises. [The retained browser report](browser-checkpoint-24.json)
records 145 earlier viewport checks, 48 screenshots and ten explicit skipped captures.
All 31 site-asset hashes and both QA helper hashes match. These are retained checks,
not a new browser run or a new Pages deployment.

[The manifest](checkpoint-25-manifest.json) binds 44,111 frozen inputs.
[The selection](checkpoint-25-selection.json) preserves all 1,144 earlier proof sources
and their ordinary evidence. Exact content bindings retain every one of the 40,485
checkpoint24 paths and hashes with 57 new unique aliases.
Four historical owner-evidence paths use the genuine archived prior bytes, with entire
original rows retained. One independently reviewed future preparation helper gained
four archive patterns after its unexecuted draft was frozen; its old snapshot and
actual first-run bytes are both preserved under Root's exact single-file authorization.
Original semantic bodies, hypotheses, commands, failed/passing outputs and times remain unchanged.

Checkpoint25 has passed the local audit and awaits an actual GitHub Pages build and
live asset checks. Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Full external references retain their separate attribution scope.

From the published repository root, reproduce checks into NEW output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction25.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction25.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction25
```

The local frozen checkout is `reports/full-coverage/checkpoint-25`; publication places
selected inputs at their original paths. Kernel reuse requires exact matching saved
fingerprints. This checkpoint does not complete the coverage objective.
