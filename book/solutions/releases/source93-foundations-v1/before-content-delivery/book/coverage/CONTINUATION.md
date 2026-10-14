# Continue from Source93

The user's latest request is implemented: Block 0 has 80 exercises, with 30
new guided questions and expanded worked solutions for all 50 original
questions. Six algebra warm-ups precede 63 local practice exercises, four
application questions and seven mixed review problems. The whole book has
586 exercises. The current release is
`../solutions/releases/source93-foundations-v1/README.md`.

Arithmetic checks cover all eighty exercises. Browser checks pass at 320,
390, 768, 820 and 1280 pixels with disclosures expanded. Print behaviour and
all twenty-one integrated labs pass. Source93's new material is self-reviewed;
no new independent agent review is claimed. The original questions, hints,
IDs, scripts and theory are preserved, and every other reader asset is exact.

The current inventory is
`../solutions/releases/source93-foundations-v1/source93-inventory/inventory.json`.
The selected audit ran in
`../../reports/solution-review/runtime-source93-foundations-v1`; it passes 1,272
unchanged proof files and 11,522 theorems. Use a new report directory when
auditing a later revision. Canonical proof sources still contain eight
unselected future files; publication contains only the selected proofs.

The thirty new questions and fifty expanded answers receive no automatic
formal completion credit. Review
`../solutions/releases/source93-foundations-v1/foundation-formal-status.json`
before using an old Primer 0 mapping: adding warm-ups and local practice has
shifted ordinal keys. Exact correspondence for all eighty current answers
is pending; the other 506 reader exercise bodies are unchanged from Source92.

Landscape Exercise 1.5 remains byte-identical, so its mapping is rebased in
`../solutions/releases/source93-foundations-v1/formal-rebase.json`. It retains
27 proved clauses and 12 complete leaves, with zero whole-exercise completion.
The next unfinished formal piece is still the mixed part(ii) erfc paragraph:
derive CDF rounding and tail underflow in a genuine numerical model, then
handle part(iii)'s numerical enclosures and joint-failure interpretation.
Full book coverage remains in progress. Source90's 539 complete / 6 partial /
11 pending totals and the older 556-exercise inventories are historical.

Publish only exact verified sources and selected evidence to
`../../reports/book/publication-repo`. Record GitHub Pages jobs and live asset
hashes separately from local checks. Unique failed/interrupted candidate
evidence is retained. Final storage cleanup remains due after full formal
coverage and final publication; build caches are excluded from publication.
The cause of the earlier application crash remains undiagnosed.
