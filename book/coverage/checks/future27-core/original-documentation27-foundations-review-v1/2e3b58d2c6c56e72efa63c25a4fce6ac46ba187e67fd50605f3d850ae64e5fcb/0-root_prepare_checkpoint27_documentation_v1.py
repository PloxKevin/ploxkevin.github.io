"""Document only actually passed checkpoint27 checks; delivery remains pending."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n): return json.loads((ROOT / n).read_bytes())
def ref(n): return {'file': n, 'sha256': sha(ROOT / n)}
def actual(n):
    d = read(n)
    assert type(d['actual_exit_code']) is int and d['actual_exit_code'] == 0
    assert sha(ROOT / d['log']) == d['log_sha256']
    assert d['helper_sha256_before'] == d['helper_sha256_after']
    for name, digest in d['helper_sha256_after'].items(): assert sha(ROOT / name) == digest
    return d
auditn = 'reports/full-coverage/lean-checkpoint-27/verification-original.json'
audit = read(auditn)
assert audit['status'] == 'passed' and audit['proof_file_count'] == len(audit['proof_sha256']) == 1175
assert audit['theorem_count'] == len(audit['declarations']) == len(audit['axiom_dependencies']) == 9644
assert audit['checks'] and all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 8
assert sum(c.get('evidence_mode') == 'reused_identical_module_and_transitive_local_imports' for c in audit['checks']) == 1167
assert all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in audit['axiom_dependencies'].values())
manifest = read('reports/full-coverage/checkpoint-27-manifest.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert manifest['successful_verification']['report_sha256'] == ref(auditn)['sha256']
execution = actual('reports/full-coverage/verify-checkpoint27-execution-v1.json')
assert execution['actual_command'] == ['python3', 'reports/full-coverage/checkpoint-27/verification/lean/verify.py', '--reuse-kernel-from', str(REPORTS / 'checkpoint-26')]
for name in ['export-checkpoint27-execution-v1', 'export-integrity-checkpoint27-execution-v1', 'frozen-ledger-checkpoint27-execution-v1', 'static-checkpoint27-execution-v1']:
    actual('reports/full-coverage/' + name + '.json')
ledger = read('reports/full-coverage/lean-checkpoint-27/ledger-audit.json')
assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
assert ledger['inventory_sha256'] == sha(ROOT / 'book/coverage/inventory-after-correction55.json')
counts = ledger['counts']; statuses = counts['statuses']; material = counts['material_review_statuses']
assert (statuses['exercise:complete_math'], statuses['exercise:partial'], statuses['exercise:pending']) == (519, 16, 21)
assert material == {'reviewed': 4574, 'pending': 8200}
static = read('reports/full-coverage/integration-27.json')
assert static['status'] == 'PASS' and static['errors'] == [] and static['counts']['html_pages'] == 29 and static['counts']['all_current_exercises'] == 556
browser = read('reports/full-coverage/browser-checkpoint-27.json')
assert browser['coverage_complete'] is False and browser['source_sha256'] == {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert (browser['fresh_verified_viewport_count'], browser['retained_verified_viewport_count'], browser['screenshot_count']) == (10, 135, 48)
progressn = 'book/coverage/progress.json'; readmen = 'reports/full-coverage/README.md'
old_progress = (ROOT / progressn).read_bytes(); old_readme = (ROOT / readmen).read_bytes()
progress_archive = REPORTS / 'progress-checkpoint27-before-preparation-original-v1.json'
readme_archive = REPORTS / 'readme-checkpoint27-before-preparation-original-v1.md'
result_path = REPORTS / 'progress-checkpoint27-preparation-update-v1.json'
assert not any(p.exists() for p in [progress_archive, readme_archive, result_path])
progress = json.loads(old_progress)
assert progress['verified_checkpoint']['proof_files'] == 1167
progress['previous_checkpoint26_delivery'] = {'entire_original_progress': {'file': progress_archive.relative_to(ROOT).as_posix(), 'sha256': hashlib.sha256(old_progress).hexdigest()}, 'entire_original_readme': {'file': readme_archive.relative_to(ROOT).as_posix(), 'sha256': hashlib.sha256(old_readme).hexdigest()}, 'content_commit': progress['last_published_content_commit'], 'live_evidence': progress['live_delivery_evidence'], 'publication_status': progress['publication_status']}
progress['verified_checkpoint'] = {'proof_files': 1175, 'theorems': 9644, 'status': 'passed', 'coverage_complete': False, 'report': auditn, 'actual_audit_workdir': str(REPORTS / 'checkpoint-27/verification/lean')}
progress['inventory_sha256'] = ledger['inventory_sha256']
progress['working_coverage_report'] = 'reports/full-coverage/root-source55-final-owner-integration27-v1.json'
progress['current_frozen_audit'] = {'snapshot': 'reports/full-coverage/checkpoint-27', 'proof_files': 1175, 'status': 'passed_actual_build_kernel_and_axiom_audit'}
progress['publication_status'] = 'checkpoint27_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
progress['live_delivery_status'] = 'checkpoint27_awaiting_actual_pages_and_live_checks'
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
result = {'status': 'passed_actual_checkpoint27_audit_documentation_prepared_delivery_pending', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'helper': ref(Path(__file__).relative_to(ROOT).as_posix()), 'current_progress': ref(progressn), 'current_readme': ref(readmen), 'original_progress': ref(progress_archive.relative_to(ROOT).as_posix()), 'original_readme': ref(readme_archive.relative_to(ROOT).as_posix()), 'actual_verification': ref('reports/full-coverage/verify-checkpoint27-execution-v1.json'), 'coverage_complete': False}
with result_path.open('x') as f: f.write(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
