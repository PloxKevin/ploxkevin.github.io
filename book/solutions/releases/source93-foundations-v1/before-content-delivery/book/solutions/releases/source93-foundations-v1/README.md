# Block 0 foundation expansion, Source93

Block 0 now has **80 exercises**, with **30 new guided problems** and deeper
worked reasoning for **all 50 existing questions**. Six algebra warm-ups
establish signs, fractions, powers, finite sums, inequality directions,
absolute-value intervals and integer stopping budgets. Twenty-four local
problems build smaller steps through the seven chapter sections. Questions
keep separate hints, review links and full worked answers. The first-reading
route distinguishes the guided build-up from graded and mixed review.

The original questions and hints are retained exactly. Every original anchor,
theory block and script survives; only recorded exercise insertions, solution
bodies and the reading-route/TOC prose change. Four short solutions on minimax,
minimum existence, growth bounds and computational budgets are replaced with
numbered derivations. Application answers are edited in their author fragment
and match its integrated page. All other thirty reader assets are unchanged.

Validation is recorded in `ready.json`:

- `installation.json` and `preservation-check.json` restore the frozen Source92
  page after reversing every declared edit; they also check all old questions,
  hints, IDs, scripts, author mirrors and the actual practice category counts.
- `arithmetic-check.json` recomputes values and boundary cases for all eighty
  exercises. Exact rational cosine enclosures check the fixed-point iteration;
  all 256 deterministic four-state maps are exhaustively checked.
- `mathematical-self-review.json` records author review. Finite calculations
  are not treated as universal proofs, and no independent agent is invented.
- `book-integration.json` checks all 29 pages, 21 labs, links, author mirrors,
  586 exercises and two actual disposable builds. Current count expectations
  are explicit in `book/exercise-counts.json`.
- The installed browser report and required `qa/check.mjs` report have no
  errors. Expanded layouts pass at five widths from 320 to 1280. Hints and
  answers operate independently; all reasoning opens for printing and the
  original disclosure state is restored afterwards.
- `visual-review.json` records actual inspection of eight practice panels and
  two A4 print pages. It does not claim an eye review of every print page.

The pinned Lean audit passes 1,272 proof files and 11,522 theorems. The selected
proof files are identical to Source92. The build and all-theorem axiom audit
are fresh; per-module kernel evidence is reused only after exact source,
import and dependency checks. The actual native execution and current source
hashes are retained under `reports/solution-review/`.

This expansion has **no new formal completion credit**. All eighty foundation
answers require exact correspondence review; `foundation-formal-status.json`
also records old-to-new exercise keys. The other 506 reader exercises are
byte-identical. `formal-rebase.json` preserves only the exact unchanged
Landscape Exercise 1.5 scope: 27 proved clauses, 12 complete leaves, and a
partial whole exercise. Full formal coverage remains in progress.

Useful local reproduction commands, from the workspace root:

```sh
python3 -B book/solutions/releases/source93-foundations-v1/build_foundations.py check
python3 -B book/solutions/releases/source93-foundations-v1/verify_source.py integration
python3 -B book/solutions/releases/source93-foundations-v1/check_math.py
node qa/learning_review.mjs primer-basics.html --report reports/solution-review/source93-browser-rerun.json
cd qa && node check.mjs ../SafeLearning/primer-basics.html
```

For a fresh complete proof audit, use the publishing checkout's selected proof
tree or recreate the frozen runtime; do not scan the workspace's unselected
future files. Historical checks and failed candidate observations are kept
separately. Publication plans and live delivery receipts are recorded under
`reports/solution-review/` after the actual commit and deployment.
