"""Document actual checkpoint28 checks while keeping delivery explicitly pending."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]

def sha(n):
    return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()

def read(n):
    return json.loads((ROOT/n).read_bytes())

def ref(n):
    return {'file': n, 'sha256': sha(n)}

audit_name = 'reports/full-coverage/lean-checkpoint-28/verification-original.json'
audit = read(audit_name)
manifest = read('reports/full-coverage/checkpoint-28-manifest.json')
selection = read('reports/full-coverage/checkpoint-28-selection.json')
coverage = read('reports/full-coverage/root-source60-final-owner-integration28-v1.json')
assert audit['status'] == 'passed' and audit['proof_file_count'] == 1186 and audit['theorem_count'] == 9896
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
assert manifest['successful_verification']['report_sha256'] == sha(audit_name)
for c in audit['checks']:
    codes = [c[k] for k in ['exit_code', 'actual_exit_code', 'actual_runner_exit_code'] if k in c]
    assert codes and all(type(v) is int and v == 0 for v in codes)
assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 11
assert sum(c.get('evidence_mode') == 'reused_identical_module_and_transitive_local_imports' for c in audit['checks']) == 1175
assert set(audit['allowed_standard_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(a) <= set(audit['allowed_standard_axioms']) for a in audit['axiom_dependencies'].values())
assert coverage['integrity_status'] == 'passed' and coverage['errors'] == [] and coverage['mathematical_coverage_complete'] is False
assert coverage['counts']['material_review_statuses'] == {'reviewed': 4621, 'pending': 8153}
assert read('reports/full-coverage/integration-28.json')['status'] == 'PASS'
assert read('reports/full-coverage/lean-checkpoint-28/export-output-integrity-v1.json')['status'] == 'passed'
for n in ['verify-checkpoint28-execution-v1', 'export-checkpoint28-execution-v1', 'static-checkpoint28-execution-v1', 'frozen-ledger-checkpoint28-execution-v1']:
    d = read('reports/full-coverage/'+n+'.json')
    assert d['status'] == 'passed' and type(d['actual_exit_code']) is int and d['actual_exit_code'] == 0
    assert sha(d['log']) == d['log_sha256']

progress_name = 'book/coverage/progress.json'
readme_name = 'reports/full-coverage/README.md'
backups = {}
for name, backup in [(progress_name, 'reports/full-coverage/progress-checkpoint28-before-preparation-original-v1.json'),
                     (readme_name, 'reports/full-coverage/readme-checkpoint28-before-preparation-original-v1.md')]:
    p = ROOT/backup
    assert not p.exists()
    with p.open('xb') as f:
        f.write((ROOT/name).read_bytes())
    assert sha(backup) == sha(name)
    backups[name] = ref(backup)
progress = read(progress_name)
progress['previous_checkpoint27_delivery'] = {
    'entire_original_progress': backups[progress_name],
    'entire_original_readme': backups[readme_name],
    'content_commit': '8607bd45ce4a4c81697c5ac92aa1e554ea5c16b6',
    'metadata_commit': '8fa808699674d13e4297d226ef1530a7ec744ad0',
    'completed_content_and_metadata_delivery': ref('book/coverage/checks/future27-core/completed27-content-and-metadata-delivery-closure-v1.json')}
progress['inventory_sha256'] = coverage['inventory_sha256']
progress['verified_checkpoint'] = {'proof_files': 1186, 'theorems': 9896, 'status': 'passed', 'coverage_complete': False,
    'report': audit_name, 'actual_audit_workdir': str(ROOT/'reports/full-coverage/checkpoint-28/verification/lean')}
progress['current_frozen_audit'] = {'snapshot': 'reports/full-coverage/checkpoint-28', 'proof_files': 1186,
    'status': 'passed_actual_build_kernel_and_axiom_audit'}
progress['current_documented_material_corrections'] = 60
progress['working_coverage_report'] = 'reports/full-coverage/root-source60-final-owner-integration28-v1.json'
progress['publication_status'] = 'prepared_source_exact_checkpoint_28_awaiting_delivery'
progress['live_delivery_status'] = 'checkpoint28_pending_actual_pages_and_live_checks'
progress['live_delivery_evidence'] = None
progress['current_published_ledger_candidate'] = 'reports/full-coverage/publication-checks/ledger-checkpoint-28.json'
progress['working_next_checkpoint_preparation'] = {'status': 'checkpoint28_actual_frozen_audit_passed_delivery_pending_full_coverage_work_continues',
    'coverage_complete': False, 'inventory': 'book/coverage/inventory-after-correction60.json',
    'expected_proof_files': 1186, 'expected_public_theorems': 9896,
    'exercise_counts': {'complete': 523, 'partial': 14, 'pending': 19},
    'material_review_units': {'reviewed': 4621, 'pending': 8153},
    'integration_execution': 'reports/full-coverage/owner28-reviewed-candidate-integration-execution-v1.json',
    'global_integrity': progress['working_coverage_report']}
(ROOT/progress_name).write_text(json.dumps(progress, indent=2)+'\n')
(ROOT/readme_name).write_text('''# Continuing full mathematical coverage

Checkpoint 28 passed the local Lean 4.34.1 build, kernel and axiom audit:
9,896 public theorems and lemmas in 1,186 selected files. The
[original audit](lean-checkpoint-28/verification-original.json) and
[measured execution](verify-checkpoint28-execution-v1.json) preserve actual
commands, results and times. Eleven additions received fresh kernel replays;
1,175 earlier modules retained successful replays after exact source,
transitive import and dependency fingerprints matched. The build and
all-theorem axiom audit are fresh.

Coverage remains partial: 523 of 556 exercises are complete, 14 partial and
19 pending. Of 12,774 overlapping material units, 4,621 are reviewed and
8,153 pending. [The frozen ledger](lean-checkpoint-28/ledger-audit.json)
checks literal fingerprints and selected declarations. Independent source
reviews establish correspondence; Lean verifies the encoded statements.

The additions cover 21 whole foundation units and 26 whole module units,
including four complete exercises. They address residual identification,
integer allocation, derivatives and Jacobians, affine interval bounds,
CROWN radii, sensor commissioning and double-integrator walls. Remaining
MPC, barrier, stochastic and other material obligations stay pending.

Corrections 56–60 clarify MPC state domains and row constraints, probability
dependence, zero-weight box corners and the sensor threshold rounding.
[Static checks](integration-28.json) passed on 29 pages and 556 exercises.
[Browser checks](browser-checkpoint-28.json) contain 20 fresh viewport
checks on four changed pages and 125 exact retained checks. Of 48 application
captures, eight fresh regions and 40 retained regions were inspected; ten
capture targets were explicitly skipped. Some narrow-screen formulas extend
past static captures. [Separate actual mouse-wheel checks](source60-four-page-math-scroll28-v3.json)
establish access to both ends of all eight overflowing containers on the
four changed pages at 390px. The original static reviews retain their exact
scope and times; whole-page visual coverage is not claimed.

[The selection](checkpoint-28-selection.json) retains all 1,175 earlier
sources. [The manifest](checkpoint-28-manifest.json) fingerprints frozen
inputs. Exact content bindings retain all 48,662 prior frozen paths and bytes.
Original mathematical bodies, hypotheses, reviews, failed and passing commands,
raw outputs and times remain unchanged. Checkpoint 27's completed content and
metadata GitHub Pages delivery is preserved in the progress history.
Checkpoint 28 is prepared; its push, actual Pages workflow and live hashes
remain pending. Full mathematical coverage work continues.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce into new output paths:

```sh
python3 book/validate28_v1.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction28.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction28.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction28
```

The local frozen checkout is `reports/full-coverage/checkpoint-28`.
Publication places selected inputs at their original paths. The full coverage
objective remains unfinished.
''')
result = {'status': 'actual_checkpoint28_documented_delivery_pending', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'original_documents': backups, 'current_documents': {n: ref(n) for n in [progress_name, readme_name]},
    'actual_audit': ref(audit_name), 'coverage_complete': False}
out = ROOT/'reports/full-coverage/checkpoint28-document-preparation-v1.json'
assert not out.exists()
with out.open('x') as f:
    f.write(json.dumps(result, indent=2)+'\n')
print(json.dumps(result))
