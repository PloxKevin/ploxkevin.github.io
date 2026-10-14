# Current Source92 recovery checkpoint

The recovered solution pass reviews **113 exercises** and expands **56 answers**:
all 50 exercises in Primer 0, the first three in each other primer, and the first
three actual document-order exercises on each non-primer exercise page. Questions,
hints, anchors, scripts, retained answers and all other page bytes are preserved.
All 18 changed pages pass reader/rendered-math checks at 320–1280 pixels.
See the [release and review provenance](../../book/solutions/releases/source92-opening-v1/README.md).

The selected Source92 audit passes **1,272 files and 11,522 theorems**. Formal
piece02 adds 14 theorem bodies, **15 mathematical clauses and five complete
source leaves**. Exact unchanged-byte rebase retains piece01 too: 27 clauses
and 12 complete leaves in the current source, with **zero complete whole-exercise
credit**. Exercise 1.5 remains partial. The mixed erfc paragraph still needs a
numerical model for CDF rounding and tail underflow; part (iii) remains pending.
See the [current rebase](../../book/solutions/releases/source92-opening-v1/formal-rebase-v1.json).

Compilation, kernel replay and the all-theorem axiom audit verify encoded
statements. They do not make unreviewed source scopes complete. Actual delivery
is recorded separately. The earlier Source91/Source90 reports below are history.

# Historical Source91 formal piece 01

**Exercise 1.5(i)** in the Landscape module has independent correspondence review
for 12 mathematical clauses and seven complete direct leaf units. Its exact
[ledger](../../book/coverage/source91-piece01/ledger-v1.json) closes only part (i):
zero newly complete whole exercises. Parts (ii)/(iii) and parent scopes remain
pending. Full formal coverage is still in progress.

The selected native audit passes **1,271 proof files and 11,508 theorems**,
including 36 newly selected theorem bodies, four fresh kernel replays and 1,267
exact prior reuses. The aggregate build and all-theorem standard-axiom audit run
again. See the [unaltered actual report](source91-piece01/lean-audit/verification-original.json),
[native execution](source91-piece01/selected-audit-native-v1.json) and
[completed local scope](source91-piece01/completion-v1.json).

Source91 has 556 exercises and 14,270 overlapping material units. Only the exact
piece above has new current-source completion credit; all other entries need
explicit rebase or review. All 556 worked solutions remain independently
student-depth reviewed (251 expanded, 305 retained), and all 31 reader assets
stay unchanged in this formal piece. Historical Source90 totals below are
preserved with their own original source and owner ledgers.

The workspace audit runs in `runtime-source91-piece01-v1`; a published checkout
contains the selected sources at their normal paths. Reproduction instructions,
interruption history and the next part (ii) scope are in
[the piece instructions](../../book/coverage/source91-piece01/README.md).
Actual publication and live delivery are recorded separately from proof completion.

# Formal coverage and worked solutions

The current teaching pages are Source91. All 556 solutions have independent
mathematical/student-depth review; 251 are expanded and 305 retained. Actual rendered,
reader and selected-proof checks pass. See [the solution release](../../book/solutions/RELEASE.md).
Source91 formal correspondence advances in bounded pieces described below.

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


Source91 content is delivered at `e98d46758478cf51f5be2e6f66381596756ab572`. All three Pages jobs and all
31 live asset hashes pass. Metadata delivery at `54a8fac0` is complete; see
[the actual final receipt](../solution-review/source91-publication-finish-v1.json).
See [actual content delivery](../../reports/solution-review/source91-content-delivery-attempt4.json).
