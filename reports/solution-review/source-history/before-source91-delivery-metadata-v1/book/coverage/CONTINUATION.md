# Continue full mathematical coverage

The student solution release has independent approval for all 556 exercises:
251 expanded, 305 retained. Actual installation, authored integration, all 29-page
reader QA and the selected proof audit pass. See
`../solutions/RELEASE.md` and `../../reports/solution-review/source91-release-ready-v1.json` for exact evidence.
Source91 publication is pending its actual commit, push, Pages jobs and live hashes.

Checkpoint35 delivery is complete at content `069532b7` / metadata `36b715de`.
Its exact Source90 audit verifies 11,472 theorems in 1,267 selected files and historical
coverage 539 complete / 6 partial / 11 pending exercises; 4,878 reviewed / 7,896 pending
material units. All earlier proofs, owner decisions and failure evidence remain.

Source91 changes solution explanations and adds an inventory of 14,270 overlapping
material units. The selected proof statements remain unchanged and pass their
native build/kernel-provenance/axiom audit. HTML-to-proof mappings for rewritten
answers require explicit rebase before new coverage claims. Retain the Source90
inventory and owner ledgers as historical evidence; do not simply replace their
source hashes with Source91 hashes. The 17 old incomplete exercise families and
unselected checkpoint36 work also remain to be completed.

The project root is not a Git repository. Publication uses
`../../reports/book/publication-repo`. Native commands use
`checks/checkpoint35-root/record_native35.py`; failed or unfinished attempts require
fresh names. `book/solutions/solution_release.py apply` accepts each target only
at its recorded before/after SHA and saves atomic per-file completion receipts.
The completed Source91 plan SHA is `58455c17c48c091f9c6934165d64d003ff43bfee7bda888d10f438d02e7cc11e`.

Actual verification runs in
`../../reports/solution-review/runtime-source91-selected35-v1` with exactly the
selected 1,267 proofs and 31 site assets. Runtime cache symlinks and immutable hardlinked
objects stay local. The working canonical proof folder retains 11 unselected files.
Never copy prior snapshots, recursive archives or .lake caches into publication.
Final device-bloat cleanup remains due after full mathematical coverage and final
publication. Pipeline recovery is tested; client/application crash causes remain
undiagnosed.
