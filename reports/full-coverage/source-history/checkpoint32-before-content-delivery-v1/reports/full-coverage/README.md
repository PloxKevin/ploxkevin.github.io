# Continuing full mathematical coverage

Checkpoint 32 passed the local Lean 4.34.1 build, kernel checks and standard-axiom
audit: **11,267 public theorems in 1,254 selected files**. Six new files passed
standalone and named builds and received fresh kernel replays. The 1,248 earlier
kernel results were reused only after exact module, transitive import and pinned
dependency identities matched. The aggregate build and every theorem's axiom
audit ran again. There are no nonstandard axioms. The
[original audit](lean-checkpoint-32-source81-recovery-v1/verification-original.json)
and [actual execution](verify-runtime32-recovery-execution-v1.json) retain source
hashes, commands, logs, times and actual runtime paths.

Coverage remains partial: **536 of 556 exercises are complete, 8 partial and
12 pending**. Of 12,774 overlapping material units, 4,841 are reviewed and
7,933 pending. The [working ledger](ledger32-working-recovery-v1.json) and
[frozen ledger](ledger32-frozen-source-only-recovery-v1.json) pass integrity
checks. Independent reviews establish correspondence with exact lesson text and
assumptions; Lean checks the encoded statements.

The batch adds 83 theorems about Frobenius norms and rank comparisons, weighted
angles, metric distances and certified balls, convolution/kernel reversal,
static versus dynamic regret, and continuous polygonal paths built from actual
Filippov Euler velocities. The
[independent mapping review](../../book/coverage/checks/recovery32-review/six-whole-material-candidate32-independent-review-v1.json)
approves six complete teaching-material units. The
[owner integration](owner32-recovery-integration-v1.json) records the exact
replacements and preserves prior ledgers. Polygonal construction is a component:
general Filippov integral-curve existence and the enclosing exercise remain pending.

[Static checks](integration32-recovery-v3.json) pass for 29 pages, 556 exercises
and 21 labs. The site's 31 asset hashes are unchanged from checkpoint 31, so its
[changed-page browser checks](browser-checkpoint-31-changed2-v1.json) and
[region captures](browser31-source81-two-changed-regions-v1.json) retain their
original scope and provenance. No new browser execution is inferred. The
obsolete validator's failed attempts are preserved; current checks use
`book/validate28_v1.py`, which handles the exact chained correction records.

The [selection](checkpoint-32-selection.json) retains every checkpoint 31 proof
source. The [manifest](checkpoint-32-manifest.json) identifies a source-only
snapshot without old snapshots or Lean build trees. The compiler ran in
`runtime-checkpoint-32-source81-recovery-v1`; the frozen snapshot mirrors its
source bytes. Only three unused Applied proof metadata entries are omitted from
the frozen owner ledger; every claim and original record is retained. The working
tree also contains unselected historical proofs. The published checkout uses the
selected sources and aggregate at the normal paths.

Checkpoint 32 is verified locally; its GitHub delivery is pending.
Checkpoint 31's content and metadata delivery is
[fully confirmed](publication31-finish-recovery-v1.json), including successful
Pages jobs and a fresh all-31-asset check. The previous session's interrupted
status update has been recovered. Full mathematical coverage remains unfinished.

To reproduce from the selected source snapshot, use fresh report paths:

```sh
cd reports/full-coverage/checkpoint-32
python3 book/coverage/validate.py --output reports/ledger-reproduction32.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction32
```

The [published Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
and original evidence are retained in Git. Further conditional-expectation,
IQC, Newton, norm and neural-loop work remains outside this selected batch until
compilation and exact independent source review are complete.
