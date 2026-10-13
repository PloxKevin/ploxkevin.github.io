# SafetyBased: Safe Learning study notes

Interactive research notes on safe RL, safe learning-based control and certified neural networks. The Trimpe group
(RWTH Aachen, DSME) and Patricia Pauli (TU/e) get extra depth. Six math primers (0, A–E) take a reader from one first
course in linear algebra (plus single-variable calculus) to every tool the fifteen modules use. Readers who need a
refresher can start with the study guide’s short checks and the recaps in Primers 0, A and B. Each module opens with a
"Before you start" box linking the exact primer sections and earlier modules it relies on. Everything is here: the website, the verified
bibliography, the paper library, the Claude and Codex reviews with their fix logs, and the tools used to build
and check the pages.

## View the site

```sh
python3 -m http.server -d SafeLearning 8000   # then open http://localhost:8000/
```

Opening `SafeLearning/index.html` directly in a browser also works. KaTeX and D3 load from CDNs, so you need to be online.

## Publish to GitHub Pages

`SafeLearning/` here is the source of truth. The publishing checkout sits in
`~/Dropbox/ploxkevin.github.io/SafeLearning/`, and the portfolio `index.html` there already has a card linking to it.

```sh
rsync -a --delete ~/SafetyBased/SafeLearning/ ~/Dropbox/ploxkevin.github.io/SafeLearning/
cd ~/Dropbox/ploxkevin.github.io
git diff --stat -- SafeLearning
git add SafeLearning
git commit -m "Update Safe Learning notes"
git push origin main
```

## Layout

| Path | What |
|---|---|
| `SafeLearning/` | The site: 6 primer pages (`primer-basics`, `-linalg`, `-optimization`, `-probability`, `-systems`, `-rl-nn`), 15 module pages, `study-guide.html` (refresher checks and practice routes), `formulas.html` (181 formulas), `papers.html` (Paper Atlas, 249 papers), `open-problems.html` (30 open problems and directions, hand-written 2026-10-01; its problem-map dots must match the module links in each problem block), `index.html`, `style.css`, `components.js` (the MODULES array drives the sidebar) |
| `research/` | Literature data. `bib_<topic>.json` is the final verified and merged bibliography per topic (trimpe, pauli, constrained_rl, safe_exploration, control_safety, certified_nn). `claude_sweep_*` and `claude_verify_*` are the Claude web sweeps and their adversarial verification. `codex_*.json` are the Codex sweeps. `merge_*` holds the Codex-only papers, verified. `critic.json` lists the gaps a completeness critic found. `bib_module_*.json` is the bibliography slice for each page. |
| `sources/` | Paper library: 259 PDFs and 453 text extractions (469 papers). `INDEX.tsv` columns: id, text size, text path, PDF path, title. |
| `briefs/`, `curriculum.mjs`, `page_contract.md` | Page design. `curriculum.mjs` is the single source of truth (modules, section ids, content briefs, notation); `page_contract.md` holds the authoring rules every page follows. |
| `qa/` | `check.mjs` renders pages in headless Chromium and reports KaTeX errors, unrendered `$`, broken links and anchors, JS errors and phone-width overflow, including content cut off inside expanded collapsible boxes (`mobileOverflowExpanded`, added 2026-10-01; boxes clip, so this is checked per box, not via page width). `clipped.mjs` names the elements that cause such clipping. `open_problems_examples.py` recomputes every number in the worked examples of `open-problems.html`. `foundations_examples.py` does the same for the KKT material in Primer B §6 and the worked examples added to Modules 2 and 3 (2026-10-01). `extract_boxes.mjs` builds the digests the formula sheet was compiled from. `codex_review_*.json` and `codex_review2_*.json` are Codex reviews, rounds 1 and 2, with their prompts. |
| `reports/` | Claude verifier and triage reports (`verify_*.json`, `triage2_*.json`) and fix logs (`*.log.md`). `work/` holds the scripts the agents used to check claims numerically (e.g. `triage_lmi/paternain_scale.mjs`). `page-snapshots/` holds earlier versions of pages. |
| `digest/` | Definition and theorem boxes extracted from each page. |
| `primers_plan.json` | The primers: ids, titles, section ids and scopes. `gen.mjs` puts them first in `components.js` (they are not in `curriculum.mjs`). |
| `reports/accessibility/` | The 2026-09-30/10-01 accessibility pass: `audit/` (Codex audit per module: every concept used, where it is taught, and the steps a fresh student could not follow), `patch/` (Codex's patch log per page, `result_*.json`, and the Claude review log `*.review.md`), `primers/` (Codex reviews of the primers and the Claude triage logs), `briefs_primer/`, `briefs_patch/`. |
| `reports/page-snapshots/pre-accessibility/` | The 15 module pages as they were before the accessibility pass. |
| `workflows/accessibility/` | Prompts and scripts of the accessibility pass (audit, primer writers, patchers, reviewers, triage). |
| `workflows/` | The Claude Code workflow scripts that built this: research, write, finish/resume, triage. |
| `screenshots/` | Preview images. |

## Everyday use

```sh
cd qa && node check.mjs ../SafeLearning/lipsdp.html   # QA one page (or several); prints a JSON report
node qa/nested.mjs                                    # check that nested collapsibles open and close independently
cd qa && node clipped.mjs ../SafeLearning/landscape.html # list elements cut off inside boxes at phone width
python3 qa/open_problems_examples.py                  # recompute the Open Problems worked-example numbers
python3 qa/foundations_examples.py                    # recompute the Primer B KKT and Module 2-3 worked-example numbers
node qa/learning_review.mjs                           # all pages: 320–1280px expanded layouts, practice, math, links and interactions
python3 qa/learning_module_examples.py                # Module 8–11 graded practice numerical/semantic checks
/usr/bin/python qa/applied_primer_math.py             # Primer C–E practice checks (NumPy and SciPy required)
cd qa && OPEN=1 node snap.mjs ../SafeLearning/open-problems.html op-T1 out.png  # screenshot with boxes expanded
node gen.mjs                                          # regenerate SafeLearning/components.js, briefs and bib slices from curriculum.mjs + research/
node gen_papers.mjs                                   # regenerate SafeLearning/papers.html from research/bib_*.json (overwrites it)
```

`check.mjs` uses the Chromium in `~/.cache/ms-playwright/`. If that is missing, run `npx playwright install chromium-headless-shell`.
To add a module: add it to `curriculum.mjs`, run `node gen.mjs`, write the page against the section ids in
`components.js`, then run `check.mjs`.

## Earlier course reviews

The primer and module pages were reviewed during the original course preparation in three stages:
1. An adversarial Claude review, including a Codex review in round 1 for 9 pages.
2. A fresh Codex review of the corrected page (round 2, all pages).
3. A Claude triage that checked each Codex finding against the sources before accepting it.

About 470 fixes were applied, each one logged in `reports/`.

Accessibility pass (2026-09-30/10-01), so that everything is followable from a first linear algebra course:
1. Codex audited every module: 1,349 concepts inventoried (where each is taught) and 737 steps a fresh student could not follow.
2. Claude wrote the six primers from that audit (each concept with a "Where this is used" link into the modules); Codex reviewed them and a Claude triage checked every finding (136 accepted, 30 further fixes).
3. Codex patched every module (1,768 logged changes: prerequisite boxes, the missing steps, precise statements of cited results).
4. Claude reviewed every patch against the cited papers: 813 corrections, mostly Codex "Theorem (Author Year)" boxes that were its own reformulations with invented or missing assumptions. Where a paper appears to contain a typo, the page says
so and marks the formula as "our reading". A few 2026 references are preprints and are labelled as such.

## Reader review (October 2026)

The reader review adds local Easy/Medium/Hard practice throughout the primers, twelve graded problems per research
module, separate hints and explained solutions, readiness checks and a study guide. Coverage, independent content
reviews, numerical checks and browser reports are in `reports/learning-review/`. The browser check visits every
walkthrough step and flashcard, exercises slider limits, checks keyboard proof toggles and mobile navigation, and
opens every box at phone, tablet and desktop widths.

## Book expansion and local formal verification (2026-10-08)

The book adds an application lab to each of the six primers and fifteen modules,
plus a reading path, glossary and three connected projects. The 67 new exercises
have separate hints and worked solutions. All 556 solutions now have independent
mathematical and student-depth review; the exercise questions and hints are preserved. Start at `SafeLearning/book.html`.

The authored application sources live in `book/chapters/`; the three reference
page sources are `book/frontmatter.html`, `book/case-studies.html` and
`book/glossary.html`. Regenerate their integration with:

```sh
python3 book/build.py
python3 -B book/solutions/solution_release.py check --plan-sha256 58455c17c48c091f9c6934165d64d003ff43bfee7bda888d10f438d02e7cc11e --report reports/solution-review/reproduce-source91-integration-v1.json
python3 book/checks/foundations.py
python3 book/checks/applied.py
python3 book/checks/modules.py
python3 book/checks/core.py
python3 book/checks/projects.py
python3 book/check_coverage.py
```

`book/solutions/solution_release.py check` checks static links, navigation, disclosures,
all selected solutions and the exact protected-byte preservation chain. The Lean project pins Lean 4.34.1
and Mathlib; its runner builds the proofs, replays course declarations in Lean's
kernel and audits their axiom dependencies. The formal coverage is partial:
theorem counts do not count completely verified exercises. Read
`reports/book/coverage.json` and `book/review/new-formal-map.json` for the scope
and remaining gaps.

The [worked-solution release](book/solutions/RELEASE.md) reviews all 556 solutions:
251 are expanded and 305 retained. Full-site reader and rendered-math checks pass.
The selected proof audit passes 11,472 theorems in 1,267 files with the new asset
fingerprints. The current working Lean tree also contains unselected future
proofs; use the selected Source91 runtime to reproduce this exact bundle.

Checkpoint35 is published and delivered at content `069532b7` and metadata
`36b715de`. Its Source90 formal coverage remains historical: 539 complete,
6 partial and 11 pending exercises, with 7,896 pending material units.
Expanded-answer formal correspondence requires a separate rebase. Publication
of the reviewed Source91 answers is recorded separately in the
[progress ledger](book/coverage/progress.json).
