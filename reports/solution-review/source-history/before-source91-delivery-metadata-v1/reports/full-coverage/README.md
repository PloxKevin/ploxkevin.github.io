# Formal coverage and worked solutions

The current teaching pages are Source91. All 556 solutions have independent
mathematical/student-depth review; 251 are expanded and 305 retained. Actual rendered,
reader and selected-proof checks pass. See [the solution release](../../book/solutions/RELEASE.md).
Source91 formal correspondence for rewritten answers awaits an explicit rebase.

The following checkpoint35 counts and reports describe its historical Source90
bytes. Its delivery is complete at `069532b7` / `36b715de`; see
[the actual delivery receipt](publication35-finish-v1.json).

# Continuing full mathematical coverage

Checkpoint35 passed the Lean4.34.1 build, kernel replay and standard-axiom audit:
**11,472 public theorems in 1,267 selected files**. Three new modules received
fresh kernel checks; 1,264 earlier results were reused only after exact source,
transitive-import and dependency identities matched. The aggregate build and
every theorem's axiom audit ran again. The [original audit](lean-checkpoint-35-source90-v1/verification-original.json)
and [native execution](verify-runtime35-execution-v1.json) retain actual provenance.

Coverage remains partial: **539 of 556 exercises complete, 6 partial, 11 pending**.
Of 12,774 overlapping teaching units, **4,878 reviewed and 7,896 pending**.
The [working ledger](ledger35-working-v1.json), [frozen ledger](ledger35-frozen-source-only-v1.json)
and [manifest](checkpoint-35-manifest.json) pass exact integrity checks.

The batch adds 13 theorems about genuine conditional Gaussian laws, finite-horizon
noise envelopes, exact rational enclosures and diagonal activation QCs.
Independent reviews complete Exercise 5.B2, 14 mathematical units and 6 literal
navigation/citation labels. Three existing proved mappings are refreshed without
extra completion credit. Rounded envelope/radius values are approximations;
the exact expressions and stated probability/model hypotheses carry the certificate.
Broader antiderivative and other overlapping parent scopes remain pending.

All 31 site assets retain checkpoint34's exact hashes and functional/visual scope.
The [fresh static check](integration35-source90-v1.json) passes all 29 pages,
556 exercises and 21 labs. No browser or numerical-explorer guarantee is widened.
The [selection](checkpoint-35-selection.json) retains all checkpoint34 proofs.
The source-only snapshot mirrors the actual runtime bytes and shares immutable
objects; no previous archive or build cache is copied. Unused Applied proof
metadata is omitted from the frozen ledger while all claims remain preserved.

Workspace reproduction, with fresh output paths:

```sh
cd reports/full-coverage/checkpoint-35
python3 book/coverage/validate.py --output reports/ledger-reproduction35.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction35
```

In the published checkout the selected sources occupy their normal paths:
run `python3 book/coverage/validate.py`, then run `lake exe cache get` and
`python3 verify.py` from `verification/lean`. The workspace's default aggregate
also retains unselected historical sources and differs from this selected runtime.

Delivery is tracked separately in the [progress ledger](../../book/coverage/progress.json).
Checkpoint34 content/metadata delivery is [confirmed](publication34-finish-v1.json).
The [continuation note](../../book/coverage/CONTINUATION.md) and
[remaining exercises](../../book/coverage/remaining-exercises35.json) retain further work.

Native command recording passed nine interruption/restart/corruption scenarios.
Atomic kernel/final-report writes, source-only exact reruns and finalizer log
checks passed isolated failure-injection tests. Earlier failed attempts remain
untouched. These tests establish pipeline behavior and do not diagnose a client crash.

