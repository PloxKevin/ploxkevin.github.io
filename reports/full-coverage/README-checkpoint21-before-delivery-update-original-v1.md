# Continuing full mathematical coverage

Checkpoint 21 passed the actual system Lean 4.34.1 audit: 8,821 public theorems in
1,089 files, a fresh 10,014-job build, kernel verification and a fresh axiom audit
of every indexed theorem. See [the original formal audit](lean-checkpoint-21/verification-original.json)
and [its actual execution](verify-checkpoint21-execution-v1.json).
All 21 additions received fresh kernel replays. The other 1,068 retain their
original actual passing replays only after exact module, transitive local import,
Lean version and dependency fingerprints matched. Original reports and raw logs
retain their commands, directories and times; private proof dependencies are
covered by module compilation and kernel replay.

Coverage remains partial. The frozen ledgers classify 502 of 556 exercises as
complete, 16 partial and 38 pending. Of the 12,774 overlapping material review
units, 4,312 are reviewed and 8,462 remain pending.
[The actual frozen-ledger check](lean-checkpoint-21/ledger-audit.json) validates
literal fingerprints and selected declarations; independent reviews establish
specific mathematical correspondence. A successful Lean audit establishes the
encoded statements, not completion of the remaining material.

The source48 book contains 48 documented teaching corrections. The latest
clarifies the Chow example's exact costs, visit counts, LP optimizers and feasible
policy limits, and the difference between almost-sure termination and a uniform
finite termination bound. Nine source-matched proof files now cover that whole
exercise. Seventeen further Viability and LipSDP practices received independent
whole-exercise reviews, including their questions, hints and every worked step.
Foundation material has additional individual source decisions; retained pending
gaps are explicit. Future22 canonical proofs and retained trial archives add no
verified coverage to this checkpoint.

[Static validation](integration-21.json) passed on all 29 pages and 556 exercises.
[Browser evidence](browser-checkpoint-21.json) covers all 29 pages at five widths:
five fresh checks on the corrected page and 140 retained actual checks after
source bytes and both QA helpers matched exactly. The 31 book assets and QA
hashes match the frozen checkpoint. There are 48 standard screenshot artifacts
and ten explicit skipped captures. Additional expanded Chow screenshots were
actually viewed at phone and desktop widths. An initial preview concern was
superseded by [actual measured containment](chow21-rendered-exercise-manual-observation-followup-v2.json):
no cropping was reproduced at the five checked widths. This limited observation
adds no manual visual pass for the entire book.

[The manifest](checkpoint-21-manifest.json) identifies the 32,040 frozen inputs.
[The selection](checkpoint-21-selection.json) preserves every baseline proof
fingerprint and original compiler evidence. A separate exact content-binding map
retains every one of the previous checkpoint's 30,207 original input paths and
hashes, sharing identical bytes where possible. Independent review confirmed
all bindings. Located source excerpts remain audit evidence; full external
papers retain their separate attributed reference scope. Original failed
selection runs and older interrupted executions remain preserved.

The authorized GitHub publication of checkpoint 21 is being prepared. The
previous checkpoint20 content and live delivery passed; the new checkpoint is
not yet described as deployed. Complete audit archives and
[Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Literal archive exclusions keep the current book, partial
ledgers and actual audit reports in the website build.

From the published repository root, reproduce checks into NEW output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction21.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction21.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction21
```

The local complete frozen source48 checkout is `reports/full-coverage/checkpoint-21`;
the Git publication places its selected inputs at their original repository paths.
Use kernel reuse only with matching saved fingerprints.
`python3 book/coverage/validate.py --require-complete` remains a failing gate.
The continuing objective includes every remaining mathematical material and
exercise claim, exact assumptions, system Lean verification and GitHub delivery.
This checkpoint does not complete it.
