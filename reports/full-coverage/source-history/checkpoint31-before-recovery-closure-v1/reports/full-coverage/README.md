# Continuing full mathematical coverage

Checkpoint 31 passed the local Lean 4.34.1 build, kernel checks and standard-axiom
audit: **11,184 public theorems in 1,248 selected files**. Six new files passed
twelve standalone and named compiler commands, then received fresh kernel
replays. The 1,242 earlier kernel results were reused only after exact module,
transitive import and dependency identities matched. The normal aggregate build
and every theorem's axiom audit ran again. There are no nonstandard axioms.
The [original audit](lean-checkpoint-31-source81-v1/verification-original.json)
and [actual execution record](verify-runtime-checkpoint31-source81-execution-v1.json)
preserve commands, outputs, hashes, times and the real runtime directory.

Coverage remains partial: **536 of 556 exercises are complete, 8 partial and
12 pending**. Of 12,774 overlapping material units, 4,835 are reviewed and
7,939 pending. The [working ledger](lean-checkpoint-31/ledger-audit-working-v1.json)
and [frozen ledger](lean-checkpoint-31/ledger-audit-frozen-v1.json) pass integrity
checks. Independent reviews establish correspondence with the exact lesson
text and assumptions; Lean checks the encoded statements. Component proofs
do not silently complete whole exercises or enclosing paragraphs.

The new sources cover full spectral induction including repeated eigenvalues,
logarithmic and polynomial growth comparisons, log-determinant Taylor
estimates, discounted-return and fixed-point explorer captions, and integral
tracking with exact offsets and spectral radii. Actual bounded Filippov
velocities and discrete Euler nodes are proved as components; integral-curve
existence and the whole invariance exercise remain pending. [Corrections 80–81](source80-81-corrections-application-v3.json)
add the positive-dimension qualification to eigenbasis nonuniqueness and
distinguish exact values from rounded integral-tracking numbers. Full-page
parser checks, preserved originals and exact inverse evidence accompany
the [five reviewed owner records](owner31-reviewed-candidate-integration-v4.json).

[Static book checks](integration-31-source81-v2.json) pass for 29 pages,
556 exercises and 21 application labs. [Browser checks](browser-checkpoint-31-changed2-v1.json)
pass on both corrected pages at five widths each. [Separate captures](browser31-source81-two-changed-regions-v1.json)
show the corrected original proof sketch and Exercise 14.5 at 360px and 1280px;
their visual review is limited to those regions. All failed earlier attempts
remain preserved alongside their subsequent passing records.

The [selection](checkpoint-31-selection.json) retains all 1,242 earlier proof
sources. The [manifest](checkpoint-31-manifest.json) identifies
1,304 files in the source-only snapshot.
No old snapshot or Lean build tree was copied. The actual compiler ran in
`runtime-checkpoint-31-source81-v1`; the later frozen snapshot mirrors its
source bytes. Only three unused Applied proof metadata entries are omitted
from the frozen owner ledger; all claims and original raw records remain.
The working tree has additional unselected historical sources, and its
default aggregate differs from the selected runtime. In the published
checkout, selected sources and their aggregate occupy the normal paths.

Checkpoint 31 is published at content commit `06271d02`. Its Pages jobs
completed successfully, and the [fresh live check](live-checkpoint-31-attempt2.json)
verified all 31 asset hashes. The [actual push](publication31-content-push-v1.json)
preserves its command, output and time. The delivery metadata commit is pending;
full mathematical coverage remains unfinished.
Checkpoint 30's content and metadata delivery is [fully confirmed](publication30-finish-root-v1.json),
including successful Pages jobs and the [fresh metadata all-31-asset check](live-checkpoint-30-attempt3.json).
Further conditional-expectation, IQC, Newton, norm and convolution work remains
outside this selected batch until compilation and independent source review.

To reproduce the selected Lean audit and ledger from this local snapshot,
use fresh report paths:

```sh
cd reports/full-coverage/checkpoint-31
python3 book/coverage/validate.py --output reports/ledger-reproduction31.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction31
```

The [published Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
and original audit records are available in Git. The full coverage objective
remains unfinished.
