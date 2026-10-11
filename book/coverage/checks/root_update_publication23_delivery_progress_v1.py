"""Record completed checkpoint23 delivery without changing mathematical reviews."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
PUB = ROOT / 'reports/book/publication-repo'
SELF = 'book/coverage/checks/root_update_publication23_delivery_progress_v1.py'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text())
def write(path, data):
    assert not path.exists(), path
    path.write_text(json.dumps(data, indent=2) + '\n')

live = read(REPORTS / 'live-checkpoint-23-attempt1.json')
commit = live['commit']
assert live['status'] == 'passed_all31_asset_sha256' and len(live['assets']) == 31
assert subprocess.run(['git','rev-parse','HEAD'], cwd=PUB, capture_output=True, check=True).stdout.decode().strip() == commit
assert read(REPORTS / 'pages-checkpoint-23-attempt1.json')['status'] == 'passed'
workflow = read(REPORTS / 'publication23-pages-view-execution-v1.log')
assert workflow['headSha'] == commit and workflow['status'] == 'completed' and workflow['conclusion'] == 'success'
assert all(j['conclusion'] == 'success' for j in workflow['jobs'])
for stem in ['publication23-content-commit-execution-v1','publication23-content-push-execution-v1',
             'publication23-pages-watch-execution-v1','publication23-pages-view-execution-v1',
             'publication23-pages-artifact-execution-v1','live23-attempt1-execution-v1']:
    row = read(REPORTS / (stem + '.json'))
    assert row['actual_exit_code'] == 0 and sha(ROOT / row['log']) == row['log_sha256']
manifest = read(REPORTS / 'checkpoint-23-manifest.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage' and len(manifest['proof_files']) == 1131
ledger = read(REPORTS / 'frozen-ledger-checkpoint23-v1.json')
assert not ledger['errors'] and ledger['mathematical_coverage_complete'] is False
assert ledger['counts']['statuses']['exercise:complete_math'] == 514
assert ledger['counts']['statuses']['exercise:partial'] == 18
assert ledger['counts']['statuses']['exercise:pending'] == 24
assert ledger['counts']['material_review_statuses'] == {'reviewed':4456,'pending':8318}
inventory = ROOT / 'book/coverage/inventory.json'
assert sha(inventory) == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert len(read(ROOT / 'book/coverage/material-corrections.json')['corrections']) == 51
progress_path = ROOT / 'book/coverage/progress.json'
readme_path = REPORTS / 'README.md'
progress = read(progress_path)
assert progress['verified_checkpoint']['proof_files'] == 1113
assert progress['last_published_content_commit'] == 'a775ca72d65f62fb480563eb8c63d6cb98725ad6'
backups = {}
for source, name in [(progress_path,'progress-checkpoint23-before-delivery-update-original-v1.json'),
                     (readme_path,'README-checkpoint23-before-delivery-update-original-v1.md')]:
    target = REPORTS / name
    assert not target.exists()
    shutil.copyfile(source, target)
    assert sha(source) == sha(target)
    backups[source.relative_to(ROOT).as_posix()] = {'file':target.relative_to(ROOT).as_posix(),'sha256':sha(target)}
progress.update(last_published_commit=commit, last_published_content_commit=commit,
    inventory_sha256=sha(inventory), current_documented_material_corrections=51,
    live_delivery_status=live['status'], live_delivery_evidence='reports/full-coverage/live-checkpoint-23-attempt1.json',
    working_coverage_report='reports/full-coverage/root-source51-final-owner-integration23-v1.json',
    publication_status='checkpoint23_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial',
    current_published_ledger_candidate='reports/full-coverage/publication-checks/ledger-checkpoint-23.json',
    verified_checkpoint={'proof_files':1131,'theorems':9193,'status':'passed','coverage_complete':False,
        'report':'reports/full-coverage/lean-checkpoint-23/verification-original.json',
        'actual_audit_workdir':str(REPORTS / 'checkpoint-23/verification/lean')},
    current_frozen_audit={'snapshot':'reports/full-coverage/checkpoint-23','proof_files':1131,
        'status':'passed_actual_build_kernel_and_axiom_audit','source_correction_index':51},
    working_next_checkpoint_preparation={
        'status':'checkpoint23_passed_actual_frozen_audit_and_live_delivery_checkpoint24_isolated_candidates_in_progress',
        'coverage_complete':False,'inventory':'book/coverage/inventory-after-correction51.json',
        'expected_proof_files':1131,'expected_public_theorems':9193,
        'exercise_counts':{'complete':514,'partial':18,'pending':24},
        'material_review_units':{'reviewed':4456,'pending':8318},
        'integration_execution':'reports/full-coverage/owner23-integration-apply-execution-v1.json',
        'global_integrity':'reports/full-coverage/root-source51-final-owner-integration23-v1.json'})
progress_path.write_text(json.dumps(progress,indent=2)+'\n')
before = readme_path.read_text()
old = ('Checkpoint 23 is prepared for GitHub publication. Its actual commit, Pages build\n'
       'and live delivery will be recorded only after those operations finish.\n')
assert before.count(old) == 1
new = (f'Checkpoint 23 is [pushed to GitHub](https://github.com/PloxKevin/ploxkevin.github.io/commit/{commit}).\n'
       'The [actual Pages workflow](https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/38105180456)\n'
       'completed successfully, and [live delivery](live-checkpoint-23-attempt1.json)\n'
       'matched all 31 book asset hashes and the built commit exactly.\n')
readme_path.write_text(before.replace(old,new,1))
record = {'status':'passed_actual_checkpoint23_delivery_progress_update',
    'updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':SELF,'sha256':sha(ROOT/SELF)},
    'originals':backups,'updated_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in [progress_path,readme_path]},
    'content_commit':commit,'pages_run':38105180456,
    'evidence_sha256':{(REPORTS/name).relative_to(ROOT).as_posix():sha(REPORTS/name) for name in
        ['live-checkpoint-23-attempt1.json','pages-checkpoint-23-attempt1.json','publication23-pages-view-execution-v1.log',
         'lean-checkpoint-23/verification-original.json','frozen-ledger-checkpoint23-v1.json']},
    'coverage_complete':False,'scope':'Actual delivery metadata only; original proof and semantic review bodies and times unchanged.'}
write(REPORTS / 'progress-checkpoint23-delivery-update-v1.json',record)
print(json.dumps({'status':'passed','content_commit':commit,'proof_files':1131,'theorems':9193,'coverage_complete':False}))
