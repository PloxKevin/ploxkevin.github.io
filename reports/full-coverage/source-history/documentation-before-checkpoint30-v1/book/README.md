# Safe Learning book sources

The book contains six foundation chapters, fifteen learning/control chapters,
three connected projects, a reading path and a glossary. Open
[`../SafeLearning/book.html`](../SafeLearning/book.html) to begin, or serve
`SafeLearning/` with `python3 -m http.server -d SafeLearning 8000`.
KaTeX and the interactive plotting dependencies load from CDNs.

Application labs are authored in `chapters/`. The front matter, projects and
glossary are `frontmatter.html`, `case-studies.html` and `glossary.html`.
From the repository root, rebuild their integration and verify the static site:

```sh
python3 book/build.py
python3 book/validate.py
```

The builder preserves the earlier teaching bodies and updates book navigation.
The validator checks local links, exercise hints/solutions, source preservation
and repeated-build consistency. It does not execute a browser.

Recompute the application examples with these five checks; the applied-primer
check needs NumPy and SciPy:

```sh
python3 book/checks/foundations.py
python3 book/checks/applied.py
python3 book/checks/modules.py
python3 book/checks/core.py
python3 book/checks/projects.py
```

Selected statements also have Lean proofs. Follow the
[pinned Lean setup](../verification/lean/README.md), then run:

```sh
python3 verification/lean/verify.py --output reports/book/lean-verification
python3 book/check_coverage.py
```

The current [correctness audit](../reports/book/README.md) records 499 theorem
declarations, exact source fingerprints, independent reviews and remaining
formalization gaps. A theorem count does not count fully verified exercises.

For rendered verification, use Node 20 or newer, a Chromium executable and CDN
access. `npm ci` installs the
Playwright library; it does not install a browser. Set the executable path:

```sh
npm --prefix qa ci
SAFELEARNING_CHROMIUM=/absolute/path/to/chromium node qa/learning_review.mjs --report reports/book/browser-final.json --artifacts reports/book/browser-artifacts
```

Inspect the saved screenshots and representative PDFs as well as the machine
report. The audit README links the recorded browser results and independent
visual reviews; source hashes identify the version they checked.
