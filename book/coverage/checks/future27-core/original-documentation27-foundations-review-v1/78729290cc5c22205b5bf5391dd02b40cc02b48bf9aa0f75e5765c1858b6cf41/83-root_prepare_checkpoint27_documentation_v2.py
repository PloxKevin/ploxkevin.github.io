"""Document genuinely passed checkpoint27 checks; delivery remains pending."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
def safe(name):
    assert isinstance(name, str) and name
    p = Path(name)
    assert not p.is_absolute() and '..' not in p.parts and p.as_posix() == name
    assert (ROOT / p).resolve().is_relative_to(ROOT.resolve())
    return ROOT / p
def sha(p):
    p = safe(p) if isinstance(p, str) else p
    assert p.resolve().is_relative_to(ROOT.resolve())
    return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name): return json.loads(safe(name).read_bytes())
def ref(name): return {'file': name, 'sha256': sha(name)}
def checked_ref(r):
    assert set(r) >= {'file', 'sha256'} and sha(r['file']) == r['sha256']
    return read(r['file'])
def zero(value): return type(value) is int and value == 0
def actual(name, command, helpers=None):
    d = read(name)
    assert d['status'] == 'passed' and zero(d['actual_exit_code'])
    if 'exit_code' in d: assert zero(d['exit_code'])
    assert d['actual_command'] == command and d['actual_workdir'] == str(ROOT)
    assert sha(d['log']) == d['log_sha256']
    if 'raw_log' in d: assert d['raw_log'] == d['log'] and d['raw_log_sha256'] == d['log_sha256']
    assert isinstance(d['elapsed_seconds'], (int, float)) and not isinstance(d['elapsed_seconds'], bool) and d['elapsed_seconds'] >= 0
    assert datetime.fromisoformat(d['started_at_utc']) <= datetime.fromisoformat(d['finished_at_utc'])
    if helpers is not None:
        assert d['helper_sha256_before'] == d['helper_sha256_after']
        assert set(d['helper_sha256_after']) == set(helpers) and helpers
        for n, h in d['helper_sha256_after'].items(): assert sha(n) == h
    return d

selectionn = 'reports/full-coverage/checkpoint-27-selection.json'
selection = read(selectionn)
manifest = read('reports/full-coverage/checkpoint-27-manifest.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
assert manifest['snapshot'] == 'reports/full-coverage/checkpoint-27' and manifest['selection'] == selectionn
assert manifest['selection_sha256'] == sha(selectionn) and manifest['proof_files'] == selection['proof_files']
assert selection['proof_file_count'] == len(selection['proof_files']) == 1175 and selection['new_file_count'] == 8
assert selection['coverage_complete'] is False
baselinen = 'reports/full-coverage/checkpoint-26-selection.json'
baseline = read(baselinen)
assert selection['baseline_selection'] == baselinen and selection['baseline_selection_sha256'] == sha(baselinen)
assert len(baseline['proof_files']) == 1167 and set(baseline['proof_files']) <= set(selection['proof_files'])
newproofs = set(selection['proof_files']) - set(baseline['proof_files'])
assert len(newproofs) == 8
for n, row in baseline['proof_files'].items(): assert selection['proof_files'][n]['sha256'] == row['sha256'] == sha(n)
for n, row in selection['proof_files'].items():
    assert sha(n) == row['sha256'] == manifest['frozen_inputs_sha256'][n]
    assert sha('reports/full-coverage/checkpoint-27/' + n) == row['sha256']

peern = 'book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json'
assert sha(peern) == 'd2d887d743e2760825e765580bbb0f12f83829636b6e9696e40abe33cc2830c8'
peer = read(peern)
assert peer['status'] == 'passed' and peer['errors'] == [] and peer['coverage_complete'] is False
assert peer['actual_aggregate_or_publication_claim'] is False and peer['all_claim_declarations_selected'] is True
assert (peer['proof_files'], peer['new_sources'], peer['public_theorem_or_lemma_exports'], peer['all_typed_public_names'], peer['old_frozen_paths_retained_exact']) == (1175, 8, 9644, 12589, 47277)
assert peer['selection'] == ref(selectionn)
peer_original_dir = 'book/coverage/checks/future27-core/original-independent-module-production-output-peer-v1/'
def peer_closed(r):
    name = r['file']
    if name.startswith('/tmp/'):
        assert Path(name).parent == Path('/tmp')
        name = peer_original_dir + Path(name).name
    assert sha(name) == r['sha256']
    return read(name) if name.endswith('.json') else None
for n, h in peer['closed_evidence_sha256'].items(): peer_closed({'file': n, 'sha256': h})
peer_actual = peer_closed(peer['actual_independent_execution'])
assert peer_actual['actual_exit_code'] == 0 and type(peer_actual['actual_exit_code']) is int
assert peer_actual['log_sha256'] == peer['actual_independent_raw_log']['sha256']
for owner in peer['owners'].values():
    for key in ['offer', 'ledger', 'mapping_peer']: checked_ref(owner[key])
    mapping_peer = read(owner['mapping_peer']['file'])
    assert mapping_peer['status'].startswith('passed') and mapping_peer.get('errors', []) == []

content_ref = selection['previous_frozen_input_content_binding']
binding = checked_ref(content_ref)
assert binding['status'] == 'all_original_frozen_inputs_retained_by_exact_content_fingerprints'
assert binding['original_input_count'] == len(binding['input_bindings']) == 47277
assert peer['content_map'] == {'file': content_ref['file'], 'sha256': content_ref['sha256']}
prior = checked_ref(peer['baseline26_manifest'])
assert binding['baseline_manifest'] == peer['baseline26_manifest']['file'] and binding['baseline_manifest_sha256'] == peer['baseline26_manifest']['sha256']
oldinputs = prior['frozen_inputs_sha256']
assert len(oldinputs) == 47277 and {r['original_frozen_path'] for r in binding['input_bindings']} == set(oldinputs)
for row in binding['input_bindings']:
    assert oldinputs[row['original_frozen_path']] == row['sha256']
    assert manifest['frozen_inputs_sha256'][row['retained_input']] == row['sha256'] == sha(row['retained_input'])

auditn = 'reports/full-coverage/lean-checkpoint-27/verification-original.json'
audit = read(auditn)
assert audit['status'] == 'passed' and audit['proof_file_count'] == len(audit['proof_sha256']) == 1175
assert audit['theorem_count'] == len(audit['declarations']) == len(audit['axiom_dependencies']) == 9644
names = [d['name'] for d in audit['declarations']]
assert len(set(names)) == 9644 and set(names) == set(audit['axiom_dependencies'])
assert all(d['file'] in selection['proof_files'] for d in audit['declarations'])
assert audit['proof_sha256'] == {n: row['sha256'] for n, row in selection['proof_files'].items()}
assert audit['lean_version'].startswith('Lean (version 4.34.1,')
assert audit['mathlib_revision'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
assert set(audit['allowed_standard_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(v) <= set(audit['allowed_standard_axioms']) for v in audit['axiom_dependencies'].values())
checks = audit['checks']
assert len(checks) == 1178 and all(zero(c['exit_code']) for c in checks)
assert checks[0]['command'] == ['lean', '--version'] and checks[1]['command'] == ['lake', 'build']
assert checks[-1]['command'] == ['lake', 'env', 'lean', str(REPORTS / 'checkpoint-27/verification/lean/AxiomAudit.lean')]
assert all('evidence_mode' not in checks[i] for i in [0, 1, len(checks)-1])
modules = {n.removeprefix('verification/lean/').removesuffix('.lean').replace('/', '.') for n in selection['proof_files']}
newmodules = {n.removeprefix('verification/lean/').removesuffix('.lean').replace('/', '.') for n in newproofs}
kernel_checks = checks[2:-1]
assert len(kernel_checks) == len({c['module'] for c in kernel_checks}) == 1175
assert {c['module'] for c in kernel_checks} == modules
for c in kernel_checks:
    assert c['command'] == ['lake', 'env', 'leanchecker', '-v', c['module']]
    expected_mode = 'fresh_kernel_replay' if c['module'] in newmodules else 'reused_identical_module_and_transitive_local_imports'
    assert c['evidence_mode'] == expected_mode
    if expected_mode == 'fresh_kernel_replay': assert c['actual_workdir'] == str(REPORTS / 'checkpoint-27/verification/lean')
assert sum(c['evidence_mode'] == 'fresh_kernel_replay' for c in kernel_checks) == 8
assert sum(c['evidence_mode'] == 'reused_identical_module_and_transitive_local_imports' for c in kernel_checks) == 1167
assert manifest['successful_verification']['report_sha256'] == sha(auditn)
assert sha('reports/full-coverage/checkpoint-27/reports/lean-verification/verification.json') == sha(auditn)
assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets) == 31
assert audit['source_sha256'] == assets
for field in ['source_sha256', 'proof_sha256', 'project_sha256']:
    for n, h in audit[field].items(): assert sha('reports/full-coverage/checkpoint-27/' + n) == h == sha(n)

execution_specs = {
    'verify': (['python3', 'reports/full-coverage/checkpoint-27/verification/lean/verify.py', '--reuse-kernel-from', str(REPORTS / 'checkpoint-26')], ['reports/full-coverage/checkpoint-27/verification/lean/verify.py']),
    'export': (['python3', 'book/coverage/export_audit.py', '--snapshot', 'reports/full-coverage/checkpoint-27', '--output', 'reports/full-coverage/lean-checkpoint-27'], ['book/coverage/export_audit.py']),
    'export-integrity': (['python3', 'book/coverage/checks/root_check_export27_integrity_v1.py'], ['book/coverage/checks/root_check_export27_integrity_v1.py']),
    'frozen-ledger': (['python3', 'reports/full-coverage/checkpoint-27/book/coverage/validate.py', '--output', 'reports/full-coverage/frozen-ledger-checkpoint27-v1.json'], ['reports/full-coverage/checkpoint-27/book/coverage/validate.py']),
    'static': (['python3', 'book/validate.py', '--allow-reviewed-corrections', '--output', 'reports/full-coverage/integration-27.json'], ['book/validate.py'])}
closed_execution = {}
for stem, (command, helpers) in execution_specs.items():
    n = 'reports/full-coverage/' + stem + '-checkpoint27-execution-v1.json'
    d = actual(n, command, helpers)
    assert d['selection_sha256'] == sha(selectionn)
    closed_execution[n] = sha(n); closed_execution[d['log']] = d['log_sha256']
export_integrity = read('reports/full-coverage/lean-checkpoint-27/export-output-integrity-v1.json')
assert export_integrity['status'] == 'passed' and export_integrity['original_report_sha256'] == sha(auditn)
assert (export_integrity['fresh_kernel_replays'], export_integrity['exact_original_kernel_replays_reused'], export_integrity['actual_check_count']) == (8, 1167, 1178)
audited_outputs = {c['output_file'].replace('reports/lean-verification/', 'reports/full-coverage/lean-checkpoint-27/', 1) for c in checks}
reused_reports = {c['reused_from']['report'].replace('reports/lean-verification/', 'reports/full-coverage/lean-checkpoint-27/', 1) for c in checks if c.get('reused_from')}
assert set(export_integrity['paths_sha256']) == audited_outputs | reused_reports
for c in checks:
    n = c['output_file'].replace('reports/lean-verification/', 'reports/full-coverage/lean-checkpoint-27/', 1)
    assert n.startswith('reports/full-coverage/lean-checkpoint-27/')
    if 'log_sha256' in c: assert c['log_sha256'] == export_integrity['paths_sha256'][n]
    if c.get('reused_from'):
        n = c['reused_from']['report'].replace('reports/lean-verification/', 'reports/full-coverage/lean-checkpoint-27/', 1)
        assert c['reused_from']['report_sha256'] == export_integrity['paths_sha256'][n]
for n, h in export_integrity['paths_sha256'].items(): assert sha(n) == h

ledger = read('reports/full-coverage/lean-checkpoint-27/ledger-audit.json')
assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
inventory = read('book/coverage/inventory.json')
assert ledger['inventory_sha256'] == sha('book/coverage/inventory.json') == sha('book/coverage/inventory-after-correction55.json') == '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert inventory['counts']['exercises'] == len(inventory['exercises']) == 556
assert inventory['counts']['material_source_units'] == len(inventory['material_source_units']) == 12774
assert ledger['source_sha256'] == inventory['source_sha256']
for n, h in inventory['source_sha256'].items(): assert assets[n] == h == sha(n)
assert len(read('book/coverage/material-corrections.json')['corrections']) == 55
assert sha('book/coverage/material-corrections.json') == '21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
counts = ledger['counts']; statuses = counts['statuses']; material = counts['material_review_statuses']
assert (counts['exercises'], counts['material_source_units']) == (556, 12774)
assert (statuses['exercise:complete_math'], statuses['exercise:partial'], statuses['exercise:pending']) == (519, 16, 21)
assert material == {'reviewed': 4574, 'pending': 8200}
global_report = checked_ref(peer['global_integrity'])
assert global_report['integrity_status'] == 'passed' and global_report['errors'] == []
assert global_report['counts'] == ledger['counts'] and global_report['inventory_sha256'] == ledger['inventory_sha256']
frozen_ledger = read('reports/full-coverage/frozen-ledger-checkpoint27-v1.json')
assert frozen_ledger['integrity_status'] == 'passed' and frozen_ledger['errors'] == [] and frozen_ledger['mathematical_coverage_complete'] is False
assert frozen_ledger['counts'] == ledger['counts'] and frozen_ledger['inventory_sha256'] == ledger['inventory_sha256']
integration = checked_ref(peer['actual_integration_result'])
assert integration['applied'] is True and len(integration['exact_replacements']) == 5
for row in integration['exact_replacements']: assert sha(row['destination']) == row['candidate']['sha256'] == sha(row['candidate']['file'])
static = read('reports/full-coverage/integration-27.json')
assert static['status'] == 'PASS' and static['errors'] == []
assert (static['counts']['html_pages'], static['counts']['all_current_exercises']) == (29, 556)
assert static['page_source_sha256'] == inventory['source_sha256']

browsern = 'reports/full-coverage/browser-checkpoint-27.json'
browser = read(browsern)
assert browser['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence' and browser['coverage_complete'] is False
assert browser['source_sha256'] == assets
for n, h in browser['qa_source_sha256'].items(): assert sha(n) == h
assert (browser['page_count'], browser['requested_viewport_count'], browser['verified_viewport_count'], browser['fresh_verified_viewport_count'], browser['retained_verified_viewport_count'], browser['screenshot_count'], browser['skipped_capture_target_count']) == (29, 145, 145, 10, 135, 48, 10)
inputs = checked_ref({'file': browser['fresh_run_inputs'], 'sha256': browser['fresh_run_inputs_sha256']})
browser_command = ['node', 'qa/learning_review.mjs', '--report', 'reports/full-coverage/browser-source55-27-v1.json', '--artifacts', 'reports/full-coverage/browser-artifacts-source55-27-v1', 'lyapunov-mpc.html', 'verification.html']
browser_execution = actual(browser['actual_execution'], browser_command)
assert sha(browser['actual_execution']) == browser['actual_execution_sha256'] == inputs['actual_execution']['sha256']
assert inputs['actual_execution']['file'] == browser['actual_execution']
assert inputs['entire_original_actual_body_and_time'] == browser_execution
assert browser_execution['source_sha256_before'] == browser_execution['source_sha256_after'] == assets
assert browser_execution['qa_source_sha256'] == browser['qa_source_sha256']
fresh_pages = checked_ref(inputs['fresh_original_report'])
old_browser = checked_ref(inputs['retained_original_report'])
assert browser_execution['report'] == inputs['fresh_original_report']['file'] and browser_execution['report_sha256'] == inputs['fresh_original_report']['sha256']
assert len(fresh_pages) == 2 and {p['file'] for p in fresh_pages} == {'lyapunov-mpc.html', 'verification.html'}
assert len(browser['pages']) == len({p['file'] for p in browser['pages']}) == 29
assert set(browser['evidence_modes']) == {p['file'] for p in browser['pages']}
captures = []; skipped = []
for page in browser['pages']:
    assert page['status'] == 'passed' and page['errors'] == [] and len(page['viewports']) == 5
    assert {v['width'] for v in page['viewports']} == {320, 390, 768, 820, 1280}
    mode = browser['evidence_modes'][page['file']]
    fresh = page['file'] in {'lyapunov-mpc.html', 'verification.html'}
    assert mode['evidence_mode'] == ('fresh_actual_source55_browser_execution' if fresh else 'retained_exact_unchanged_source_and_QA_original26_record')
    assert mode['original_report'] == (inputs['fresh_original_report'] if fresh else inputs['retained_original_report'])
    original_pages = fresh_pages if fresh else old_browser['pages']
    assert page == next(p for p in original_pages if p['file'] == page['file'])
    if not fresh: assert old_browser['source_sha256']['SafeLearning/' + page['file']] == assets['SafeLearning/' + page['file']]
    for capture in page['screenshots']:
        if capture['status'] == 'passed':
            assert sha(capture['path']) == capture['sha256']; captures.append(capture)
        else:
            assert capture['status'] == 'skipped'; skipped.append(capture)
assert len(captures) == len({c['path'] for c in captures}) == 48 and len(skipped) == 10
assert len(inputs['screenshot_aliases']) == 48
for alias in inputs['screenshot_aliases']:
    assert sha(alias['original']) == alias['sha256'] == sha(alias['file'])
    assert any(c['path'] == alias['original'] and c['sha256'] == alias['sha256'] for c in captures)
manual = browser['manual_visual_inspection']
assert manual['status'] == 'all48_actual_captured_regions_inspected_with_explicit_scope_limits'
assert (manual['fresh_actual_captures'], manual['retained_exact_capture_count']) == (4, 44)
assert manual['horizontal_scroll_interaction_verified'] is False and manual['whole_page_visual_approval'] is False
assert manual['new_original_four_review'] == inputs['new_four_capture_review']
new_manual = checked_ref(manual['new_original_four_review'])
assert new_manual['status'] == 'completed_actual_four_original_image_inspections_of_captured_regions'
assert new_manual['horizontal_scroll_interaction_verified'] is False and new_manual['whole_page_visual_approval'] is False
fresh_captures = [c for p in fresh_pages for c in p['screenshots'] if c['status'] == 'passed']
assert len(new_manual['inspected_captures']) == len(fresh_captures) == 4
assert new_manual['inspected_captures'] == fresh_captures
for c in new_manual['inspected_captures']: assert sha(c['path']) == c['sha256']
catalogn = 'book/coverage/checks/future27-core/original-checkpoint27-support-reviews-v1/original-support-review-byte-aliases-v1.json'
assert sha(catalogn) == 'dc40a7778a877414654aaac7a9b2db8c0a6faf78e3e62e647ed478772fadbb46'
catalog = read(catalogn)
def support_closed(r):
    if not r['file'].startswith('/tmp/'): return checked_ref(r)
    row = catalog['original_closed_byte_aliases'][r['file'] + '::' + r['sha256']]
    assert row['original_file'] == r['file'] and row['original_sha256'] == r['sha256']
    return checked_ref(row['immutable_byte_copy'])
old_manual_ref = manual['entire_original48_checkpoint26_review']
assert old_manual_ref['sha256'] == 'e2f4ed6013788e0e0ec90b307aa7428b6d0d8911f40d05eb71f613f6a7f9b12e'
old_manual = support_closed(old_manual_ref)
assert old_manual == inputs['historical_original48_capture_review']['entire_original_body_and_time']
assert inputs['historical_original48_capture_review']['file'] == old_manual_ref['file'] and inputs['historical_original48_capture_review']['sha256'] == old_manual_ref['sha256']
assert old_manual['status'] == 'all48_actual_captured_region_inspections_closed_with_formula_visibility_limits'
assert old_manual['actual_image_count'] == len(old_manual['observations']) == 48
assert old_manual['horizontal_scroll_manually_verified'] is False and old_manual['whole_pages_or_mathematical_proofs_approved'] is False and old_manual['all_formulas_visible_in_static_mobile_captures'] is False
for n, h in old_manual['original_browser26_and_scoped_manual6_unchanged_sha256'].items():
    assert Path(n).is_relative_to(ROOT) and sha(Path(n)) == h
for review in old_manual['review_records_original_bodies_and_times_unchanged']:
    original_review = support_closed(review)
    assert original_review == review['original_body_with_all_review_times_unchanged']
for observed in old_manual['observations']:
    assert sha(observed['image']['file']) == observed['image']['sha256']
    support_closed(observed['review_record'])
retained_captures = [c for c in captures if c not in fresh_captures]
assert len(retained_captures) == 44
for c in retained_captures:
    assert any(o['original_alias'] == c['path'] and o['image']['sha256'] == c['sha256'] for o in old_manual['observations'])

progressn = 'book/coverage/progress.json'; readmen = 'reports/full-coverage/README.md'
old_progress = (ROOT / progressn).read_bytes(); old_readme = (ROOT / readmen).read_bytes()
progress_archive = REPORTS / 'progress-checkpoint27-before-preparation-original-v2.json'
readme_archive = REPORTS / 'readme-checkpoint27-before-preparation-original-v2.md'
result_path = REPORTS / 'progress-checkpoint27-preparation-update-v2.json'
assert not any(p.exists() for p in [progress_archive, readme_archive, result_path])
progress = json.loads(old_progress)
assert progress['verified_checkpoint']['proof_files'] == 1167
assert progress['verified_checkpoint']['report'] == 'reports/full-coverage/lean-checkpoint-26/verification-original.json'
assert progress['publication_status'] == 'checkpoint26_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
assert progress['live_delivery_status'] == 'passed_all31_asset_sha256'
assert progress['live_delivery_evidence'] == 'reports/full-coverage/live-checkpoint-26-attempt2.json'
progress['previous_checkpoint26_delivery'] = {'entire_original_progress': {'file': progress_archive.relative_to(ROOT).as_posix(), 'sha256': hashlib.sha256(old_progress).hexdigest()}, 'entire_original_readme': {'file': readme_archive.relative_to(ROOT).as_posix(), 'sha256': hashlib.sha256(old_readme).hexdigest()}, 'content_commit': progress['last_published_content_commit'], 'live_evidence': progress['live_delivery_evidence'], 'publication_status': progress['publication_status']}
progress['verified_checkpoint'] = {'proof_files': 1175, 'theorems': 9644, 'status': 'passed', 'coverage_complete': False, 'report': auditn, 'actual_audit_workdir': str(REPORTS / 'checkpoint-27/verification/lean')}
progress['inventory_sha256'] = ledger['inventory_sha256']
progress['inventory_counts'] = inventory['counts']
progress['working_coverage_report'] = 'reports/full-coverage/root-source55-final-owner-integration27-v1.json'
progress['current_frozen_audit'] = {'snapshot': 'reports/full-coverage/checkpoint-27', 'proof_files': 1175, 'status': 'passed_actual_build_kernel_and_axiom_audit'}
progress['publication_status'] = 'checkpoint27_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
progress['live_delivery_status'] = 'checkpoint27_awaiting_actual_pages_and_live_checks'
progress['live_delivery_evidence'] = None
progress['current_documented_material_corrections'] = 55
progress['current_published_ledger_candidate'] = 'reports/full-coverage/publication-checks/ledger-checkpoint-27.json'
progress['working_next_checkpoint_preparation'] = {'status': 'checkpoint27_actual_frozen_audit_passed_delivery_pending_full_coverage_work_continues', 'coverage_complete': False, 'inventory': 'book/coverage/inventory-after-correction55.json', 'expected_proof_files': 1175, 'expected_public_theorems': 9644, 'exercise_counts': {'complete': 519, 'partial': 16, 'pending': 21}, 'material_review_units': material, 'integration_execution': 'reports/full-coverage/owner27-reviewed-candidate-integration-execution-v1.json', 'global_integrity': progress['working_coverage_report']}
readme = '''# Continuing full mathematical coverage

Checkpoint 27 passed the local Lean 4.34.1 build, kernel and axiom audit:
9,644 public theorems and lemmas in 1,175 selected files. The
[original audit](lean-checkpoint-27/verification-original.json) and
[measured execution](verify-checkpoint27-execution-v1.json) preserve actual
commands, results and times. Eight additions received fresh kernel replays;
1,167 earlier modules retained their successful replays after exact source,
transitive import and dependency fingerprints matched. The build and all-theorem
axiom audit are fresh.

Coverage remains partial: 519 of 556 exercises are complete, 16 partial and
21 pending. Of 12,774 overlapping material units, 4,574 are reviewed and
8,200 pending. [The frozen ledger](lean-checkpoint-27/ledger-audit.json)
checks literal fingerprints and selected declarations. Independent full-source
reviews establish correspondence; Lean verifies the encoded statements.

The additions complete the conformal-rank and explorer-slope exercises and
eight supporting module units. Five linear-algebra units now have complete
sensor-reconstruction, spectral and residual-orthogonality mappings. Eleven
precise MPC components have proofs under their stated hypotheses. The whole
robust replanning certificate remains pending.

Corrections 54 and 55 clarify the original incremental-stability domains and
the joint-distinctness or independently randomized tie treatment for strict
conformal ranks. [Static checks](integration-27.json) passed on 29 pages and
556 exercises. [Browser checks](browser-checkpoint-27.json) contain ten fresh
viewport checks on the two changed pages and 135 exact retained checks.
The 48 application-region captures were inspected: four fresh regions and
44 unchanged regions. Some narrow-screen formulas extend past the static
image edge; horizontal scrolling and whole-page visual coverage were not
established by those captures. Ten capture targets were explicitly skipped.

[The selection](checkpoint-27-selection.json) retains all 1,167 earlier proof
sources. [The manifest](checkpoint-27-manifest.json) fingerprints the frozen
inputs. Exact content bindings preserve all 47,277 prior frozen paths and
bytes. Original review bodies, hypotheses, commands, failed and passing
outputs and times remain unchanged. Checkpoint 26's completed GitHub Pages
and live delivery remain in the progress history. Checkpoint 27 delivery
awaits an actual push, Pages build and live asset-hash checks.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce checks into new output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction27.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction27.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction27
```

The local frozen checkout is `reports/full-coverage/checkpoint-27`. Publication
places selected inputs at their original paths. The full coverage objective
remains unfinished.
'''
for p, body in [(progress_archive, old_progress), (readme_archive, old_readme)]:
    with p.open('xb') as f: f.write(body)
(ROOT / progressn).write_text(json.dumps(progress, indent=2) + '\n')
(ROOT / readmen).write_text(readme)
result = {'status': 'passed_actual_checkpoint27_audit_documentation_prepared_delivery_pending', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'helper': ref(Path(__file__).relative_to(ROOT).as_posix()), 'current_progress': ref(progressn), 'current_readme': ref(readmen), 'original_progress': ref(progress_archive.relative_to(ROOT).as_posix()), 'original_readme': ref(readme_archive.relative_to(ROOT).as_posix()), 'actual_verification': ref('reports/full-coverage/verify-checkpoint27-execution-v1.json'), 'actual_frozen_ledger': ref('reports/full-coverage/lean-checkpoint-27/ledger-audit.json'), 'browser27_report': ref(browsern), 'closed_actual_execution_evidence_sha256': closed_execution, 'independent_production_selection_peer': ref(peern), 'content_binding': ref(content_ref['file']), 'manual4_review': ref(manual['new_original_four_review']['file']), 'old48_original_byte_alias_catalog': ref(catalogn), 'exercise_counts': {'complete': 519, 'partial': 16, 'pending': 21}, 'material_review_units': material, 'coverage_complete': False}
with result_path.open('x') as f: f.write(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
