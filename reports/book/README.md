# Safe Learning book: verification evidence

The book contains 29 pages and 556 exercises: 489 preserved originals,
58 new chapter applications and nine connected-project exercises. All six
primers and fifteen modules have an application lab, learning objectives,
worked examples and review prompts. The reading path, glossary and three
larger projects connect the material.

The local Lean 4.34.1 audit passed for **499 theorem declarations in six
files**, including 26 new application theorems. It builds the pinned project,
replays the course declarations in Lean's kernel and audits transitive axiom
dependencies. No `sorry`, custom axioms or native evaluation proof shortcuts
are permitted. Dependency revisions match the Lake manifest.

Formal coverage is partial. The new-exercise ledger records ten partially
covered exercises and 57 not formalized in this audit. The proofs check the
encoded statements; they do not establish every exercise subclaim, cited
research theorem or empirical model assumption.

- [Lean results, commands and current source fingerprints](lean-verification/verification.json)
- [Coverage ledger for all 67 new exercises](coverage.json)
- [Exact new theorem statements, anchors and limits](../../book/review/new-formal-map.json)
- [Independent statement-to-prose review and whitespace revision history](../../book/review/book-lean-peer.json)
- [Five application calculation checks](math-checks.json) and [seven original regression checks](../lean-verification/numerical-verification.json)
- [Static integration: links, source preservation and repeated-build consistency](../../book/review/integration.json)
- [Independent content completion review](../../book/review/completion-content.json)
- [Independent core/project](../../book/review/core-projects-peer.json), [module](../../book/review/modules-peer.json), [foundation](../../book/review/foundations-peer.json) and [applied-primer](../../book/review/applied.json) reviews

The final Chromium run passed on all **29 pages**, including 145 expanded
viewport checks at 320, 390, 768, 820 and 1280 pixels. It tested all 67 new
native exercises with click, Enter and Space, independent hint/solution
visibility and restoration. It also checked book navigation, rendered math
through walkthrough and flashcard steps, slider inputs and print restoration.
Slider checks are input/error smoke; calculation evidence is separate.

Independent reviewers inspected all 48 saved application/reference content
screenshots at 390 and 1280 pixels, plus four screenshots with mobile controls
visible. Five representative A4 PDFs were exported with 12 mm margins. The
book, glossary and case-study PDFs were reviewed completely; the two long
chapter PDFs were sampled on the pages listed in their reviews. The raw
machine report retains `visualInspection: pending`; the separate review
reports record the actual inspection scope and exact artifact hashes.

- [Final browser report](browser-final.json), [observed completion](browser-execution.json) and [execution log](browser-run.log)
- [Browser scope and earlier launch history](browser-readiness.json)
- [Independent QA source review](../../book/review/browser-qa-peer.json)
- [Foundations and reference visual review](../../book/review/foundations-rendered.json)
- [Application and case-study visual review](../../book/review/applied-rendered.json)
- [First seven modules and LMI print review](../../book/review/modules-rendered.json)
- [Controls-visible mobile checks](mobile-navigation.json) and [saved artifacts](browser-artifacts/)
- [Current input and artifact hash audit](input-audit.json)

The rendered review corrected mobile title/menu overlap, inline mathematics
spacing in the new reference pages and glossary print breaks. The spacing
report proves that all TeX spans, HTML tags and non-whitespace source text were
preserved. Earlier mathematical review corrected certificate/violation
reasoning, viability remedies, rollout independence and strict-radius
supremum wording; the source reviews document those changes and assumptions.

- [Whitespace-only rendered copy fixes](rendered-spacing-fixes.json)
- [Static supplement and prose word-count method](static-supplement.json)
- [Publication patch and exact site hashes](publication-preparation.json)
- [Publication dependencies](../../book/review/publication-dependencies.json)
- [Isolated-checkout static validation](checkout-validation.log) and [coverage check](checkout-coverage.log)
- [Current status](status.json) and [completion audit](completion-audit-final.json)

Publication is pending the authorized push and live delivery check. The
isolated checkout preserves unrelated portfolio work.

Earlier blocked-browser, DNS and incomplete-run reports are historical
diagnostics. October 7 formal/browser/publication reports describe the prior
26-page site. Use the current status, final browser report and current input
audit to identify the version verified here.

Reproduction commands are in the [book source README](../../book/README.md)
and [Lean project README](../../verification/lean/README.md). Build the authored
fragments before checking them. Browser reproduction needs an actual Chromium
executable, Node dependencies and CDN access.
