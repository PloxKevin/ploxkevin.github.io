"""Document genuine checkpoint29 results; preserve completed28 and keep new delivery pending."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
INVENTORY = '5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
CORRECTIONS = '5c3a871bbc5782a02c5b19bfa33a8fa6e4dc311a9e72c525d76fcc526f37eafd'
PRIOR_SELECTION = 'e954d6a3f22139ec6ebafbe4164c46f184fe5e2c672860c9fce5829f73424632'
COMPLETED28 = 'book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json'
COMPLETED28_SHA = '621f475f2a08deecf7fb1f75c6c977099208a49c33db65cc6735a511a7bb7c7d'
ORIGINAL_DOCUMENTS = {
    'book/coverage/progress.json': '98574c65c0025db8555f10842e609d2b1d25c7147eeb34b1ff0e6278db01b8ab',
    'reports/full-coverage/README.md': 'c82b14821d70f6a5d44dc696680326958c0f17302ade2e5faa2222e607333c4c'}
AUDIT = 'reports/full-coverage/lean-checkpoint-29/verification-original.json'
COVERAGE = 'reports/full-coverage/root-source65-final-owner-integration29-v1.json'
EXECUTIONS = {
    'verify-checkpoint29-execution-v1': ['python3', 'reports/full-coverage/checkpoint-29/verification/lean/verify.py', '--reuse-kernel-from', str(ROOT/'reports/full-coverage/checkpoint-28')],
    'export-checkpoint29-execution-v1': ['python3', 'book/coverage/export_audit29_v1.py', '--snapshot', 'reports/full-coverage/checkpoint-29', '--output', 'reports/full-coverage/lean-checkpoint-29'],
    'export-integrity29-execution-v1': ['python3', 'book/coverage/checks/root_check_export29_integrity_v1.py'],
    'static-checkpoint29-execution-v1': ['python3', 'book/validate28_v1.py', '--allow-reviewed-corrections', '--output', 'reports/full-coverage/integration-29.json'],
    'frozen-ledger-checkpoint29-execution-v1': ['python3', 'reports/full-coverage/checkpoint-29/book/coverage/validate.py', '--output', 'reports/full-coverage/lean-checkpoint-29/ledger-audit.json']}

def safe(base, n):
    assert type(n) is str and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r*?[')
    p = base/n
    assert p.resolve().is_relative_to(base) and not p.is_symlink()
    return p

def sha(n, base=ROOT):
    return hashlib.sha256(safe(base, n).read_bytes()).hexdigest()

def read(n, base=ROOT):
    return json.loads(safe(base, n).read_bytes())

def ref(n):
    return {'file': n, 'sha256': sha(n)}

def aliases(d, keys, required=False, kind=None):
    values = [d[k] for k in keys if k in d]
    assert values or not required
    assert all((kind is None or type(v) is kind) and v == values[0] for v in values)
    return values[0] if values else None

def zero(d):
    code = aliases(d, ['actual_exit_code', 'exit_code', 'actual_runner_exit_code'], True, int)
    assert code == 0 and ('status' not in d or d['status'] == 'passed')

def native(n, command):
    d = read(n)
    zero(d)
    assert d['status'] == 'passed'
    assert aliases(d, ['actual_command', 'command'], True, list) == command
    assert aliases(d, ['actual_workdir', 'cwd', 'workdir', 'working_directory'], True, str) == str(ROOT)
    log = aliases(d, ['log', 'raw_log'], True, str)
    log_sha = aliases(d, ['log_sha256', 'raw_log_sha256'], True, str)
    assert sha(log) == log_sha
    helper = command[1]
    assert d['helper_sha256_before'] == d['helper_sha256_after'] == {helper: sha(helper)}
    return d

def readiness():
    selection = read('reports/full-coverage/checkpoint-29-selection.json')
    manifest = read('reports/full-coverage/checkpoint-29-manifest.json')
    audit, coverage = read(AUDIT), read(COVERAGE)
    assert sha('book/coverage/inventory.json') == sha('book/coverage/inventory-after-correction65.json') == INVENTORY
    assert sha('book/coverage/material-corrections.json') == CORRECTIONS
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
    assert manifest['selection_sha256'] == sha('reports/full-coverage/checkpoint-29-selection.json')
    assert manifest['proof_files'] == selection['proof_files']
    assert audit['status'] == 'passed' and audit['proof_file_count'] == selection['proof_file_count'] == len(selection['proof_files']) == 1197
    assert audit['theorem_count'] == 10114 and selection['new_file_count'] == 11
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert manifest['successful_verification']['report_sha256'] == sha(AUDIT)
    names = [d['name'] for d in audit['declarations']]
    assert len(names) == len(set(names)) == len(audit['axiom_dependencies']) == 10114
    assert set(names) == set(audit['axiom_dependencies'])
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert set(audit['allowed_standard_axioms']) == allowed
    assert all(set(a) <= allowed for a in audit['axiom_dependencies'].values())
    for c in audit['checks']:
        zero(c)
        aliases(c, ['command', 'actual_command'], True, list)
        aliases(c, ['cwd', 'workdir', 'working_directory', 'actual_workdir'], kind=str)
    assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 11
    assert sum(c.get('evidence_mode') == 'reused_identical_module_and_transitive_local_imports' for c in audit['checks']) == 1186
    assert sha('reports/full-coverage/checkpoint-28-selection.json') == PRIOR_SELECTION
    baseline = read('reports/full-coverage/checkpoint-28-selection.json')['proof_files']
    assert len(baseline) == 1186 and set(baseline) <= set(selection['proof_files'])
    assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline.items())
    additions = set(selection['proof_files']) - set(baseline)
    assert len(additions) == 11 and sum(d['file'] in additions for d in audit['declarations']) == 218
    assert coverage['integrity_status'] == 'passed' and coverage['errors'] == [] and coverage['mathematical_coverage_complete'] is False
    assert coverage['inventory_sha256'] == INVENTORY
    assert coverage['counts']['material_review_statuses'] == {'reviewed': 4663, 'pending': 8111}
    assert {k: coverage['counts']['statuses'][k] for k in ['exercise:complete_math', 'exercise:partial', 'exercise:pending']} == {'exercise:complete_math': 526, 'exercise:partial': 11, 'exercise:pending': 19}
    assert read('reports/full-coverage/integration-29.json')['status'] == 'PASS'
    assert read('reports/full-coverage/lean-checkpoint-29/export-output-integrity-v1.json')['status'] == 'passed'
    for key, command in EXECUTIONS.items():
        native('reports/full-coverage/'+key+'.json', command)
    ledger = read('reports/full-coverage/lean-checkpoint-29/ledger-audit.json')
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
    assert ledger['inventory_sha256'] == INVENTORY and ledger['counts']['material_review_statuses'] == {'reviewed': 4663, 'pending': 8111}
    assert sha(COMPLETED28) == COMPLETED28_SHA
    closed = read(COMPLETED28)
    assert closed['status'] == 'passed_actual_checkpoint28_content_and_metadata_delivery'
    assert closed['content_commit'] == 'c3245229f722a678927d2f95fd756286a100598d'
    assert closed['metadata_commit'] == 'fa1e92e55ea0b8fac9ba30ef2b0450b5e5281702'
    for n, h in closed['exact_native_evidence_sha256'].items():
        assert sha(n) == h
    held = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    held.update({n: h for n, h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/'+k+'.json' for k in ['core', 'foundations', 'applied', 'modules', 'applied-promotions']]})
    held.update({'book/coverage/inventory.json': INVENTORY, 'book/coverage/material-corrections.json': CORRECTIONS})
    assert len([n for n in held if n.startswith('SafeLearning/')]) == 31
    assert all(sha(n) == h for n, h in held.items())
    browser = read('reports/full-coverage/browser-checkpoint-29.json')
    assert browser['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
    assert (browser['page_count'], browser['requested_viewport_count'], browser['verified_viewport_count'], browser['fresh_verified_viewport_count'], browser['retained_verified_viewport_count']) == (29, 145, 145, 20, 125)
    assert browser['source_sha256'] == {n: h for n, h in held.items() if n.startswith('SafeLearning/')}
    visual = browser['manual_visual_inspection']
    assert browser['screenshot_count'] == 48 and browser['skipped_capture_target_count'] == 10
    assert visual['status'] == 'all48_actual_captured_regions_inspected_with_explicit_scope_limits'
    assert (visual['fresh_actual_captures'], visual['retained_exact_capture_count']) == (8, 40) and visual['whole_page_visual_approval'] is False
    manual_ref = visual['new_original_eight_review']
    assert sha(manual_ref['file']) == manual_ref['sha256']
    manual = read(manual_ref['file'])
    assert manual['status'] == 'completed_actual_eight_original_image_inspections_of_captured_regions' and len(manual['inspected_captures']) == 8
    for capture in manual['inspected_captures']:
        assert sha(capture['path']) == capture['sha256']
    scroll = read('reports/full-coverage/source65-four-page-math-scroll29-v2.json')
    assert scroll['status'] == 'passed' and scroll['errors'] == [] and scroll['source_sha256'] == browser['source_sha256']
    assert len(scroll['pages']) == 4 and scroll['actual_overflow_container_count'] == 4
    assert all(p['status'] == 'passed' and all(c['status'] == 'passed' for c in p['overflow_containers']) for p in scroll['pages'])
    native('reports/full-coverage/source65-four-page-math-scroll29-execution-v2.json', ['node', 'book/coverage/checks/root_check_math_scroll29_v2.mjs'])
    return selection, manifest, audit, coverage, held

README = '''# Continuing full mathematical coverage

Checkpoint 29 passed the local Lean 4.34.1 build, kernel and axiom audit:
10,114 public theorems and lemmas in 1,197 selected files. The
[original audit](lean-checkpoint-29/verification-original.json) and
[measured execution](verify-checkpoint29-execution-v1.json) preserve actual
commands, results and times. Eleven additions received fresh kernel replays;
1,186 earlier modules retained successful replays after exact source,
transitive import and dependency fingerprints matched. The build and
all-theorem axiom audit are fresh.

Coverage remains partial: 526 of 556 exercises are complete, 11 partial and
19 pending. Of 12,774 overlapping material units, 4,663 are reviewed and
8,111 pending. [The frozen ledger](lean-checkpoint-29/ledger-audit.json)
checks literal fingerprints and selected declarations. Independent source
reviews establish correspondence; Lean verifies the encoded statements.

The additions address inner products, finite norm formulas and comparison,
the complete MPC exercise and its implemented-policy statistical route,
projected dual bounds, leaky-activation constraints and scalar semidefinite
certificates. Eight foundation mathematics units and eight bibliography rows
received individual whole-unit decisions. Fixed-selector monitoring has an
explicit component scope. Generic stochastic execution and remaining
mathematical material stay pending.

Corrections 61–65 qualify hyperplane measure and compactness, timing and
backpropagation, leaky-activation convexity, norm exponents and input radii,
and scalar certificate ratios and eigenvalue rounding.
[Static checks](integration-29.json) passed on 29 pages and 556 exercises.
[Browser checks](browser-checkpoint-29.json) contain 20 fresh viewport
checks on four changed pages and 125 exact retained checks. Of 48 application
captures, eight fresh regions and 40 retained regions were inspected; ten
capture targets were explicitly skipped. Some narrow-screen formulas extend
past static captures. [Separate actual mouse-wheel checks](source65-four-page-math-scroll29-v2.json)
establish access to both ends of all four overflowing containers in the
four checked application regions at 390px. The original static reviews retain
their exact scope and times; whole-page visual coverage is not claimed.

[The selection](checkpoint-29-selection.json) retains all 1,186 earlier
sources. [The manifest](checkpoint-29-manifest.json) fingerprints frozen
inputs. Exact content bindings retain all 50,797 prior frozen paths and bytes.
Original mathematical bodies, hypotheses, reviews, failed and passing commands,
raw outputs and times remain unchanged. Checkpoint 28's completed content and
metadata GitHub Pages delivery is preserved in the progress history.
Checkpoint 29 is prepared; its push, actual Pages workflow and live hashes
remain pending. Full mathematical coverage work continues.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce into new output paths:

```sh
python3 book/validate28_v1.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction29.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction29.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction29
```

The local frozen checkout is `reports/full-coverage/checkpoint-29`.
Publication places selected inputs at their original paths. The full coverage
objective remains unfinished.
'''

def main():
    _, _, _, coverage, held = readiness()
    backups = {
        'book/coverage/progress.json': 'reports/full-coverage/progress-checkpoint29-before-preparation-original-v1.json',
        'reports/full-coverage/README.md': 'reports/full-coverage/readme-checkpoint29-before-preparation-original-v1.md'}
    output = 'reports/full-coverage/checkpoint29-document-preparation-v1.json'
    assert all(sha(n) == h for n, h in ORIGINAL_DOCUMENTS.items())
    assert all(not safe(ROOT, n).exists() for n in [*backups.values(), output])
    originals = {n: safe(ROOT, n).read_bytes() for n in backups}
    progress = read('book/coverage/progress.json')
    progress['previous_checkpoint28_delivery'] = {
        'entire_original_progress': {'file': backups['book/coverage/progress.json'], 'sha256': ORIGINAL_DOCUMENTS['book/coverage/progress.json']},
        'entire_original_readme': {'file': backups['reports/full-coverage/README.md'], 'sha256': ORIGINAL_DOCUMENTS['reports/full-coverage/README.md']},
        'content_commit': 'c3245229f722a678927d2f95fd756286a100598d',
        'metadata_commit': 'fa1e92e55ea0b8fac9ba30ef2b0450b5e5281702',
        'completed_content_and_metadata_delivery': ref(COMPLETED28)}
    progress['inventory_sha256'] = coverage['inventory_sha256']
    progress['verified_checkpoint'] = {'proof_files': 1197, 'theorems': 10114, 'status': 'passed', 'coverage_complete': False,
        'report': AUDIT, 'actual_audit_workdir': str(ROOT/'reports/full-coverage/checkpoint-29/verification/lean')}
    progress['current_frozen_audit'] = {'snapshot': 'reports/full-coverage/checkpoint-29', 'proof_files': 1197, 'status': 'passed_actual_build_kernel_and_axiom_audit'}
    progress['current_documented_material_corrections'] = 65
    progress['working_coverage_report'] = COVERAGE
    progress['publication_status'] = 'prepared_source_exact_checkpoint_29_awaiting_delivery'
    progress['live_delivery_status'] = 'checkpoint29_pending_actual_pages_and_live_checks'
    progress['live_delivery_evidence'] = None
    progress['current_published_ledger_candidate'] = 'reports/full-coverage/publication-checks/ledger-checkpoint-29.json'
    progress['working_next_checkpoint_preparation'] = {'status': 'checkpoint29_actual_frozen_audit_passed_delivery_pending_full_coverage_work_continues',
        'coverage_complete': False, 'inventory': 'book/coverage/inventory-after-correction65.json',
        'expected_proof_files': 1197, 'expected_public_theorems': 10114,
        'exercise_counts': {'complete': 526, 'partial': 11, 'pending': 19},
        'material_review_units': {'reviewed': 4663, 'pending': 8111},
        'integration_execution': 'reports/full-coverage/owner29-reviewed-candidate-integration-execution-v1.json', 'global_integrity': COVERAGE}
    payloads = {'book/coverage/progress.json': (json.dumps(progress, indent=2)+'\n').encode(), 'reports/full-coverage/README.md': README.encode()}
    assert all(sha(n) == h for n, h in held.items()) and all(sha(n) == h for n, h in ORIGINAL_DOCUMENTS.items())
    for n, backup in backups.items():
        with safe(ROOT, backup).open('xb') as f:
            f.write(originals[n])
        assert sha(backup) == ORIGINAL_DOCUMENTS[n]
    for n, data in payloads.items():
        safe(ROOT, n).write_bytes(data)
    assert all(sha(n) == h for n, h in held.items())
    result = {'status': 'actual_checkpoint29_documented_delivery_pending', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'original_documents': {n: ref(p) for n, p in backups.items()},
        'current_documents': {n: ref(n) for n in payloads}, 'actual_audit': ref(AUDIT), 'coverage_complete': False}
    with safe(ROOT, output).open('x') as f:
        f.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
