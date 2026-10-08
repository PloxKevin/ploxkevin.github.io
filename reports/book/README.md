# Book expansion: correctness evidence

The expanded book contains 29 pages and 556 exercises: 489 preserved originals,
58 new chapter application exercises and 9 connected-project exercises. All 21
primer/module pages have an application lab. A reading path, glossary and three
larger projects connect the material.

The local Lean 4.34.1 audit checks **499 theorem declarations in six files**,
including 26 new application theorems. It builds the project, replays the course
declarations in Lean's kernel and audits transitive axiom dependencies. No
`sorry`, custom axioms or native evaluation proof shortcuts are permitted.
Mathlib and the other cached dependencies match their pinned Git revisions.

This is partial formal coverage. It does not formally verify every exercise,
the cited literature or the physical/statistical validity of the models.

- [Lean results and exact fingerprints](lean-verification/verification.json)
- [Coverage ledger for all 67 new exercises](coverage.json)
- [Exact new theorem statements, source anchors and limits](../../book/review/new-formal-map.json)
- [Independent statement-to-prose review](../../book/review/book-lean-peer.json)
- [Independent core/project review and corrections](../../book/review/core-projects-peer.json)
- [Independent module review](../../book/review/modules-peer.json)
- [Independent foundations review](../../book/review/foundations-peer.json)
- [Applied-primer review and peer corrections](../../book/review/applied.json)
- [Five application calculation checks and logs](math-checks.json)
- [Seven original-course numerical regression checks](../lean-verification/numerical-verification.json)
- [Static integration, links, hints/solutions and original-source preservation](../../book/review/integration.json)
- [Static syntax checks and prose word counts](static-supplement.json)
- [Publication patch, locally applied and compared exactly](publication-preparation.json)
- [Independent book completion review](../../book/review/completion-content.json)
- [Current input and evidence fingerprints](fingerprint-recheck-2.json)
- [Browser QA readiness and explicit runtime block](browser-readiness.json)
- [Independent browser QA source review](../../book/review/browser-qa-peer.json)
- [Publication dependency review](../../book/review/publication-dependencies.json)
- [Isolated-checkout static validation](checkout-validation.log) and [coverage check](checkout-coverage.log)

Known issues corrected include a certificate failure incorrectly implying a
physical violation, a proposed viability remedy that cannot work with the
failed actuator, insufficient rollout independence assumptions, and a strict
radius supremum incorrectly called a maximum. Model domains, fresh noise laws
and local links were also clarified.

Rendered QA is **pending**: the final QA runner's Chromium attempt aborts before
launch under the current sandbox ([log](browser-readiness-attempt.log)). Static checks do not establish KaTeX
rendering, expanded mobile layouts, keyboard interaction or print behavior.
The runner now covers new exercise disclosures, book navigation, representative
PDF exports and expanded screenshots, and preserves incomplete-run statuses.
Its slider checks are input/error smoke; they do not certify explorer results.
GitHub DNS resolution also fails ([log](remote-recheck-2.log)); this expansion has
not been pushed. The historical October 7 browser/publication reports describe
the previous 26-page version.

A writable isolated Git checkout packages the site, authored book fragments,
proofs and evidence while preserving unrelated portfolio files. Its static
validator and coverage checker pass. This is a local draft pending rendered QA
and publication.

Reproduction commands are in the [book source README](../../book/README.md) and the
[Lean project README](../../verification/lean/README.md). Rebuild authored
fragments before checking them. Current book audit reports use this directory
so that the historical formal and browser evidence remains distinguishable.
