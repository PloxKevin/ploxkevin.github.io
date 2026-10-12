"""Describe actual checkpoint30 verification and the unfinished original work."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
HISTORY = ROOT / 'reports/full-coverage/source-history/documentation-before-checkpoint30-v1'
RESULT = ROOT / 'reports/full-coverage/checkpoint30-documentation-preparation-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads((ROOT / n).read_bytes())


def ref(n):
    return {'file': n, 'sha256': sha(ROOT / n)}


assert not HISTORY.exists() and not RESULT.exists()
manifest = read('reports/full-coverage/checkpoint-30-manifest.json')
ledger = read('reports/full-coverage/lean-checkpoint-30-final-css-v1/ledger-audit-frozen-v1.json')
audit = read('reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json')
browser = read('reports/full-coverage/browser-checkpoint-30-changed6-v2.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert audit['status'] == 'passed' and audit['proof_file_count'] == 1242 and audit['theorem_count'] == 11080
assert ledger['integrity_status'] == 'passed' and ledger['errors'] == []
assert ledger['mathematical_coverage_complete'] is False
assert len(browser) == 6 and all(r['status'] == 'passed' and r['errors'] == [] and len(r['viewports']) == 5 for r in browser)
counts = ledger['counts']
assert [counts['statuses'][n] for n in ['exercise:complete_math', 'exercise:partial', 'exercise:pending']] == [535, 8, 13]
assert counts['material_review_statuses'] == {'reviewed': 4770, 'pending': 8004}
files = ['reports/full-coverage/README.md', 'book/coverage/progress.json', 'book/README.md', 'verification/lean/README.md']
HISTORY.mkdir(parents=True)
originals = {}
for n in files:
    target = HISTORY / n
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / n, target)
    assert sha(target) == sha(ROOT / n)
    originals[n] = {'file': target.relative_to(ROOT).as_posix(), 'sha256': sha(target)}
progress = read('book/coverage/progress.json')
progress['previous_checkpoint29_delivery'] = {
    'original_progress': originals['book/coverage/progress.json'],
    'content_commit': '196b26b2c3951cf21d6a35f82cad4e0853fdaea2',
    'metadata_commit': '01b95073d2f78d066ef88c1aa3fd20af1d631e22',
    'actual_fresh_all31_live_check': ref('reports/full-coverage/live-checkpoint-29-attempt1.json'),
    'actual_live_check_execution': ref('reports/full-coverage/live29-current-metadata-confirmation-execution-v1.json'),
    'scope': 'Original successful checkpoint29 delivery retained unchanged; these receipts do not establish checkpoint30 delivery.'}
progress['verified_checkpoint'] = {
    'checkpoint': 30, 'proof_files': 1242, 'theorems': 11080, 'status': 'passed', 'coverage_complete': False,
    'report': 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json',
    'actual_audit_workdir': '/home/oxrexkevin/SafetyBased/reports/full-coverage/runtime-checkpoint-30-final-css-v1/verification/lean',
    'actual_execution': ref('reports/full-coverage/verify-runtime-checkpoint30-final-css-execution-v1.json'),
    'initial45_fresh_kernel_audit': ref('reports/full-coverage/lean-checkpoint-30/verification-original.json')}
progress['current_frozen_audit'] = {'snapshot': manifest['snapshot'], 'source_only': True, 'proof_files': 1242,
    'status': 'source_exact_mirror_of_actual_runtime_audit', 'snapshot_execution_claimed': False,
    'manifest': ref('reports/full-coverage/checkpoint-30-manifest.json')}
progress['publication_status'] = 'prepared_source_exact_checkpoint_30_awaiting_delivery'
progress['live_delivery_status'] = 'checkpoint30_not_yet_pushed_or_live_verified'
progress['live_delivery_evidence'] = {'previous_checkpoint29': progress['previous_checkpoint29_delivery']}
progress['current_documented_material_corrections'] = 79
progress['inventory_sha256'] = ledger['inventory_sha256']
progress['working_coverage_report'] = 'reports/full-coverage/lean-checkpoint-30/ledger-audit-working-v1.json'
progress['current_published_ledger_candidate'] = 'reports/full-coverage/lean-checkpoint-30-final-css-v1/ledger-audit-frozen-v1.json'
progress['working_next_checkpoint_preparation'] = {
    'status': 'checkpoint30_selected_verified_and_mapped_original_full_coverage_objective_unfinished',
    'inventory': 'book/coverage/inventory.json', 'inventory_sha256': ledger['inventory_sha256'],
    'exercise_counts': {'complete': 535, 'partial': 8, 'pending': 13},
    'material_review_units': counts['material_review_statuses'],
    'owner30_integration': ref('reports/full-coverage/owner30-reviewed-candidate-integration-v2.json'),
    'coverage_complete': False}
(ROOT / 'book/coverage/progress.json').write_text(json.dumps(progress, indent=2) + '\n')
text = '''# Continuing full mathematical coverage

Checkpoint 30 passed the local Lean 4.34.1 build and standard-axiom audit:
11,080 public theorems and lemmas in 1,242 selected files. The 45 additions
passed 90 separate compiler commands and received fresh kernel replays in
the [first actual audit](lean-checkpoint-30/verification-original.json).
The [final audit](lean-checkpoint-30-final-css-v1/verification-original.json)
checked the corrected mobile stylesheet, rebuilt the aggregate and reran
every theorem's axiom audit. Its 1,242 earlier successful kernel results were
reused only after exact module, transitive import and dependency identities
matched. There are no nonstandard axiom dependencies.
[Actual commands and times](verify-runtime-checkpoint30-final-css-execution-v1.json)
retain the real runtime directory; no compiler execution in the later
source-only snapshot is claimed.

Coverage remains partial: 535 of 556 exercises are complete, 8 partial and
13 pending. Of 12,774 overlapping material units, 4,770 are reviewed and
8,004 pending. The [working ledger](lean-checkpoint-30/ledger-audit-working-v1.json)
and [frozen ledger](lean-checkpoint-30-final-css-v1/ledger-audit-frozen-v1.json)
passed integrity checks. Independent reviews establish source correspondence;
Lean checks the encoded statements. Whole-exercise decisions preserve their
explicit hypotheses. Component results do not silently complete an exercise.

The additions cover foundational norm, linear-algebra, convergence and
optimization material; delayed control, Gaussian-process calculations,
thermal Bellman bounds, viability and continuous-control examples; and
monitoring, spike and discrete trajectory probability results. Corrections
66–79 repair exact values, rounding, dimensions and theorem assumptions.
[Their actual application](source66-79-corrections-application-v3.json)
retains the original text and fourteen full-page parser checks. The
[owner integration](owner30-reviewed-candidate-integration-v2.json) preserves
the five original ledgers and exact forward/inverse mapping evidence.
General Filippov trajectory existence, the remaining module exercises and
other mathematical teaching material remain in the review queue.

[Static book checks](integration-30-final-css-v1.json) passed on 29 pages,
556 exercises and 21 application labs. [Fresh browser checks](browser-checkpoint-30-changed6-v2.json)
passed on all six changed pages at five viewport widths each. Twelve
application-region captures were independently inspected; this is a bounded
visual review. Long display formulas can extend beyond a capture while
remaining inside scroll containers. The CMDP page's two long inline
guarantees now scroll within the column on small phones; [actual mouse-wheel
checks](cmdp-mobile-math30-v1.json) reached both ends at 320px and 360px.
Original failed checks are preserved alongside the subsequent passing checks.

The [selection](checkpoint-30-selection.json) retains all 1,197 earlier
proof sources. The [manifest](checkpoint-30-manifest.json) identifies the
1,298 files in the compact source-only snapshot. Earlier snapshots and Lean
build output were not copied. Historical mathematical bodies, assumptions,
reviews, failures, outputs and times remain at their original hashed paths
and in Git history. Only three unused Applied proof metadata entries are
omitted from the frozen ledger; every claim and original raw ledger is retained.

Checkpoint 30 is verified locally and prepared for GitHub publication;
delivery is still pending. Checkpoint 29's successful content and metadata
delivery, including the [fresh all-31-asset check](live-checkpoint-29-attempt1.json),
remains preserved. Full mathematical coverage work continues.

To reproduce the selected Lean audit and ledger from the local source-only
snapshot, use fresh report paths:

```sh
cd reports/full-coverage/checkpoint-30
python3 book/coverage/validate.py --output reports/ledger-reproduction30.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction30
```

The published repository contains selected inputs at their original paths.
Its [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
and archived audit records remain available in Git. The full coverage
objective remains unfinished.
'''
(ROOT / 'reports/full-coverage/README.md').write_text(text)
p = ROOT / 'book/README.md'
old = p.read_text()
before = '''The current [correctness audit](../reports/book/README.md) records 499 theorem
declarations, exact source fingerprints, independent reviews and remaining
formalization gaps. A theorem count does not count fully verified exercises.'''
after = '''The [earlier book audit](../reports/book/README.md) records its original
499 declarations. The [continuing audit](../reports/full-coverage/README.md)
now checks 11,080 theorems in 1,242 selected files; 535 of 556 exercises are
complete, and the remaining exercises and material are explicit in the ledgers.
Use that audit's source-only snapshot commands to reproduce the selected batch.
A theorem count does not count fully verified exercises.'''
assert old.count(before) == 1
p.write_text(old.replace(before, after))
p = ROOT / 'verification/lean/README.md'
old = p.read_text()
start = old.index('Its 3,002 theorems in 202 files')
end = old.index('\n\nThe separate numerical recomputation', start)
replacement = '''Its current selected batch contains 11,080 theorems in 1,242 files.
All 45 new modules received fresh kernel replays in the first audit. After a
targeted mobile stylesheet fix, a fresh normal aggregate build and axiom audit
passed again, with 1,242 earlier kernel checks reused under exact source/import
and dependency fingerprints. The actual audit ran in the separately recorded
runtime directory. The later source-only snapshot mirrors those bytes and
contains no copied build cache or earlier snapshot trees.

The inventory contains 556 exercises and 12,774 overlapping material units.
535 exercises are complete, 8 partial and 13 pending; 8,004 material units
remain pending. Source correspondence review can reopen entries while their
formal proofs remain valid. For the exact selected batch in this working tree,
follow the source-only snapshot reproduction commands in the continuing audit.
The working Lean directory also retains unselected historical drafts; its
default aggregate is not the selected checkpoint30 runtime. In a clean
published checkout the selected sources and aggregate occupy their normal paths.'''
p.write_text(old[:start] + replacement + old[end:])
report = {'status': 'actual_checkpoint30_documentation_prepared_delivery_pending',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'original_bytes_preserved': originals,
    'updated_files_sha256': {n: sha(ROOT / n) for n in files},
    'counts': counts, 'coverage_complete': False, 'publication_success_claimed': False}
with RESULT.open('x') as f:
    f.write(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'updated_files': 4, 'coverage_complete': False}))
