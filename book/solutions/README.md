# Exercise solution review

The Source90 baseline contains all **556 exercises on 22 pages**. Every row is
pending pedagogical review. This queue records existing content and a review
rubric; it does not assess a solution by its length or infer adequacy from a
structural check.

The audience has first-course linear algebra and single-variable calculus.
Review the method, assumptions and notation, intermediate work, reasons for
steps, and interpretation of the result. Calculation, proof, conceptual,
algorithm and application questions have corresponding guidance in
`baseline-source90/manifest.json` and `review-tracker.json`.

`baseline-source90/pages/<page>.json` contains exact exercise, question, hint and
solution HTML/text/hashes. Its paired page manifest records solution ranges and
all protected segment hashes. UTF-8 byte ranges have an exclusive end; line
numbers start at one and columns at zero. The baseline stores the original page
and authoring bytes in `baseline-source90/sources/`.

489 exercises are authored directly in `SafeLearning/`, 58 application exercises
in `book/chapters/`, and 9 project exercises in `book/case-studies.html`. The
baseline verifies each integrated exercise against its exact authored fragment.
All 556 have one solution disclosure; 427 have a hint and 129 do not.

Read excerpts without changing sources:

```sh
python3 -B book/solutions/solution_review.py list --page primer-linalg.html --limit 3 --chars 1800
```

Use the exact `solution.html` body and `solution.sha256` when preparing a draft.
Keep the existing solution summary, disclosure and body-container markup. Draft
JSON can be an array or an object with an `exercises`, `solutions` or `proposals`
array. Each decision needs these fields:

```json
{
  "inventory_key": "page.html#existing-anchor",
  "source_file": "SafeLearning/page.html",
  "original_solution_sha256": "exact baseline solution SHA256",
  "decision": "retain or replace",
  "thoroughness_rationale": "Exercise-specific assessment",
  "replacement_html": "Exact replacement body for a replace decision"
}
```

A retained solution must have unchanged bytes. A replacement must contain the
actual worked reasoning. Generic wrappers do not establish thoroughness.

Create local candidates and validate the decisions:

```sh
python3 -B book/solutions/validate_solution_draft.py \
  --draft book/solutions/drafts/page-solutions.json \
  --output-dir book/solutions/candidates/page-v1 \
  --report reports/solution-review/page-candidates-v1.json \
  --require-complete-pages
```

This mirrors application/project changes into both the canonical candidate and
the authoring candidate. It preserves every other byte and checks questions,
hints, exercise counts, anchor IDs, script blocks and inline script hooks. All
swaps are validated before any candidate file is written. It leaves the actual
teaching pages, authored fragments, coverage records and publication untouched.

Validate an independently prepared full-page or authoring-fragment candidate:

```sh
python3 -B book/solutions/solution_review.py validate \
  --source SafeLearning/page.html \
  --candidate book/solutions/candidates/page-v1/SafeLearning/page.html \
  --report reports/solution-review/page-preservation-v1.json
```

Use fresh output/report names for different bytes. Preservation validation does
not approve the mathematics, pedagogical completeness or rendered appearance.
Those reviews remain explicit before any solution is adopted.
