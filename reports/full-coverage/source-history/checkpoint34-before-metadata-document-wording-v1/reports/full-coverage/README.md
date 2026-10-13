# Continuing full mathematical coverage

Checkpoint 34 passed the Lean 4.34.1 build, kernel checks and standard-axiom
audit: **11,459 public theorems in 1,264 selected files**. Three new files
passed standalone and named builds and fresh kernel replays. The 1,261 earlier
kernel results were reused after exact source, transitive import and dependency
identities matched. The aggregate build and every theorem's axiom audit ran again.
The [original audit](lean-checkpoint-34-source90-v1/verification-original.json)
and [actual execution](verify-runtime34-execution-v1.json) preserve their provenance.

Coverage remains partial: **538 of 556 exercises are complete, 7 partial and
11 pending**. Of 12,774 overlapping material units, **4,858 are reviewed and
7,916 pending**. The [working ledger](ledger34-working-v1.json) and
[frozen ledger](ledger34-frozen-source-only-v1.json) pass integrity checks.

The batch adds 114 theorems about shifted temporal IQCs, scalar neural feedback
and conditional expectation. Independently reviewed mappings complete Exercises
14.3 and 14.6 and seven whole teaching-material units. Source corrections 89–90
make the neural-loop stability and conditional-expectation domains precise.
The [owner review](../../book/coverage/checks/checkpoint34-review/independent-four-owner34-candidates-review-v3.json)
retains earlier proved claims, pending obligations and historical evidence.
Earlier failed and superseded candidate attempts retain their actual outcomes.

[Static checks](integration34-source90-v1.json) pass for all 29 pages, 556 exercises
and 21 labs. The [functional and visual review](../../book/coverage/checks/checkpoint34-review/browser34-source90-independent-visual-and-functional-closure-v1.json)
binds both changed pages at five widths, ten changed-region captures and mobile
formula scrolling to their exact source hashes. Print was skipped in these runs.
The finite scalar trajectories are bounded floating-point observations;
neither all-time formal safety nor numerical correctness of the 2D explorer is inferred.

The [selection](checkpoint-34-selection.json) retains every checkpoint33 proof.
The [manifest](checkpoint-34-manifest.json) identifies a source-only snapshot.
The actual compiler ran in `runtime-checkpoint-34-source90-v1`; the frozen
snapshot mirrors its exact proof, site and project bytes. No earlier snapshot
or Lean build tree is copied. Three unused Applied proof metadata entries are
omitted from the frozen ledger; every claim is preserved.

Checkpoint 34 content is published at `4d8c1b5f`. Its Pages jobs
completed successfully, and the [fresh live check](live-checkpoint-34-attempt1.json)
verified all 31 asset hashes. The [actual content delivery](publication34-content-delivery-v1.json)
preserves the commit, push and served-byte evidence. The later delivery-metadata
commit, push and live check remain pending. Full mathematical coverage remains unfinished.
Checkpoint33 delivery is [fully confirmed](publication33-finish-v1.json).
The [continuation note](../../book/coverage/CONTINUATION.md) and
[remaining exercises](../../book/coverage/remaining-exercises34.json) identify further work.

To reproduce the selected snapshot with fresh output paths:

```sh
cd reports/full-coverage/checkpoint-34
python3 book/coverage/validate.py --output reports/ledger-reproduction34.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction34
```

The published checkout places selected Lean sources at their normal paths.
The working tree also retains unselected historical sources; its default
aggregate differs from the selected runtime.
