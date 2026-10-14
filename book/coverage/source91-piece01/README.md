# Source91 formal coverage, piece 01

This piece covers only **Exercise 1.5(i)** in `SafeLearning/landscape.html`
(`landscape.html::exercise-19`). Its 12 mathematical clauses cover centering,
the first two substitutions, unrolling, actual independent Gaussian noise
moments, state moments, the geometric variance formula and limits, the
stationary Gaussian characterization, convergence in distribution on one
infinite noise space, and almost-sure nonconvergence of noisy paths.

The exact source packet is `claims-v2.json`. Seven complete direct leaf units
are separately reviewed; the containing answer/exercise and parts (ii)/(iii)
remain pending. Whole-exercise completion credit is zero. The Source91
inventory has 556 exercises and 14,270 overlapping material units. Historical
Source90 owner counts are preserved and are not current Source91 completion
counts.

Completion requires the independent literal source-to-statement decision and
an actual selected Lean build, four fresh kernel replays and every theorem's
standard-axiom audit. The expected selected bundle contains 1,271 proof files
and 11,508 public theorems, including 36 newly selected theorem bodies.
`ledger-v1.json` and `../../../reports/full-coverage/source91-piece01/completion-v1.json`
record actual completed scope only after those gates pass. Independent runtime
and export/finish protocol reviews are recorded with their exact helper hashes.

Use `prepare_runtime.py --plan` and its pinned `--apply --plan-sha256` protocol
for an immutable selected runtime. The runtime links the existing dependency
cache but never copies it or earlier trees. Run the recorded verifier command
there with a fresh native record and fresh output names. A published checkout
has exactly the selected proofs and aggregate at their normal paths; run
`python3 verify.py --output ../../reports/piece01-reproduction` from
`verification/lean`. Omitting prior-kernel reuse makes a fresh replay of every
selected module. The working directory retains eight unselected future modules
and should use the frozen runtime for this audit.

Keep failed compile attempts, earlier helper versions and interrupted fixture
receipts as history. The current packet is v2; v1 binds the earlier failed
wrapper and is not a completion receipt. No student solution, exercise question,
hint or site asset changes in this formal piece. Publication staging, the real
commit/push, all three Pages jobs and all 31 live asset hashes are recorded
separately. Final delivery receipts can be published with the next bounded
piece, avoiding a recursive metadata commit.

Next piece: **Exercise 1.5(ii)**, actual Gaussian upper tails, expectation of the
finite indicator sum, zero-noise handling and the integral definition of erfc.
Part (iii) then needs numerical enclosures and the joint-failure interpretation.
Full formal coverage remains in progress.
