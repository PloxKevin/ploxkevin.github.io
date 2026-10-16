# Complete mathematical coverage work

This audit extends the earlier selected-statement audit. It is not complete
until every exercise and every established mathematical teaching claim has a
reviewed correspondence to checked Lean declarations.

The current [Source93 inventory](../solutions/releases/source93-foundations-v1/source93-inventory/inventory.json)
contains 586 exercises and 14,889 overlapping source units. Regenerate inventories
in a fresh versioned output directory; retain historical inventories unchanged.
The queue itself is not proof coverage. Review surrounding prose too; mathematical
assertions can lack TeX. The [continuation](CONTINUATION.md) identifies the latest
selected audit and distinguishes kernel checks from independent source review.

Domain ledgers are `foundations.json` (0/A/B), `applied.json` (C/D/E),
`modules.json` (1–7 and12–15), and `core.json` (8–11, projects and reference
material). Each should use schema version1 and include:

- `scope_pages`, `source_sha256`, `proof_files` and an honest overall `status`.
- `exercises`, each with its canonical `inventory_key` from `inventory.json`,
  source/locator/label, and a list of mathematical `claims`.
- `material_claims`, each tied to the source-unit keys it addresses. A claim
  can cover multiple overlapping units; any excluded unit needs a reason.
- For each claim: stable `id`, exact `statement_in_prose`, `kind`,
  `lean_declarations`, `status`, `hypotheses`, `correspondence` and
  `remaining_gaps`.

Claim statuses are `proved`, `definition_encoded`, `not_a_formal_claim`,
`open_problem_statement` or `pending`. Exercise statuses are `complete_math`,
`partial` or `pending`. A declaration reference alone does not establish full
coverage. All requested mathematical conclusions, including necessity,
optimality, limits and counterexamples, must be addressed individually.

Standard mathematical hypotheses may be explicit. Assuming the conclusion,
omitting a requested general argument, or replacing it with a numerical
identity does not close a claim. Physical model validity and teaching advice
are not mathematical theorems. Open research problems must remain labeled as
open; formalizing their statements does not prove them.

The previous published reports remain evidence for their recorded versions.
New work must use fresh reports and current source fingerprints.
