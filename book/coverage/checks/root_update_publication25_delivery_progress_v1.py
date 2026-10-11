"""Record completed25 delivery from actual workflow and live evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def actual(stem):
    d=read(REPORTS/(stem+'.json'))
    codes=[d[k]for k in ('actual_exit_code','exit_code')if k in d]
    assert codes and all(type(code)is int and code==0 for code in codes)
    assert sha(ROOT/d['log'])==d['log_sha256']
    return d

out=REPORTS/'progress-checkpoint25-delivery-update-v1.json'
assert not out.exists()
live=read(REPORTS/'live-checkpoint-25-attempt1.json')
commit=live['commit']
assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31
assert live['remote_main']==commit
assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()==commit
pages=read(REPORTS/'pages-checkpoint-25-attempt1.json')
assert pages['status']=='passed' and pages['commit']==pages['expected_commit']==commit
records={s:actual(s) for s in ['publication25-content-commit-execution-v1','publication25-content-push-execution-v1',
    'publication25-pages-watch-execution-v1','publication25-pages-view-execution-v1',
    'publication25-pages-artifact-execution-v1','live25-attempt1-execution-v1']}
workflow=read(REPORTS/'publication25-pages-view-execution-v1.log')
assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
assert workflow['jobs'] and all(j['conclusion']=='success' for j in workflow['jobs'])
command=records['publication25-pages-view-execution-v1']['actual_command']
assert command[:3]==['gh','run','view'] and command[3].isdigit()
run_id=int(command[3])
manifest=read(REPORTS/'checkpoint-25-manifest.json')
audit=read(REPORTS/'lean-checkpoint-25/verification-original.json')
ledger=read(REPORTS/'frozen-ledger-checkpoint25-v1.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert len(manifest['proof_files'])==audit['proof_file_count']==1156 and audit['theorem_count']==9369
assert audit['status']=='passed' and all(type(c['exit_code'])is int and c['exit_code']==0 for c in audit['checks'])
assert manifest['successful_verification']['report_sha256']==sha(REPORTS/'lean-checkpoint-25/verification-original.json')
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
assert len(assets)==31 and len({row['source']for row in live['assets']})==31
assert {row['source']:row['expected_sha256']for row in live['assets']}==assets
for row in live['assets']:
    assert row['http_status']==200 and row['matches']is True
    assert row['actual_sha256']==row['expected_sha256']==sha(ROOT/row['source'])
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['counts']['statuses']['exercise:complete_math']==514
assert ledger['counts']['statuses']['exercise:partial']==19 and ledger['counts']['statuses']['exercise:pending']==23
assert ledger['counts']['material_review_statuses']=={'reviewed':4500,'pending':8274}
inventory=ROOT/'book/coverage/inventory.json'
assert sha(inventory)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert len(read(ROOT/'book/coverage/material-corrections.json')['corrections'])==52
progress_path=ROOT/'book/coverage/progress.json'
readme_path=REPORTS/'README.md'
progress=read(progress_path)
assert progress['verified_checkpoint']['proof_files']==1156 and progress['verified_checkpoint']['theorems']==9369
assert progress['publication_status']=='checkpoint25_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
assert progress['last_published_content_commit']=='13d6823f7378a9d2b9737242763cf19b9b321b28'
before=readme_path.read_text()
old=('Checkpoint25 has passed the local audit and awaits an actual GitHub Pages build and\n'
     'live asset checks. Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)\n')
assert before.count(old)==1
assert all(not(REPORTS/name).exists()for name in
    ['progress-checkpoint25-before-delivery-update-original-v1.json','README-checkpoint25-before-delivery-update-original-v1.md'])
backups={}
for source,name in [(progress_path,'progress-checkpoint25-before-delivery-update-original-v1.json'),
                    (readme_path,'README-checkpoint25-before-delivery-update-original-v1.md')]:
    target=REPORTS/name
    assert not target.exists()
    shutil.copyfile(source,target)
    assert sha(source)==sha(target)
    backups[source.relative_to(ROOT).as_posix()]=ref(target)
progress.update(last_published_commit=commit,last_published_content_commit=commit,
    live_delivery_status=live['status'],live_delivery_evidence='reports/full-coverage/live-checkpoint-25-attempt1.json',
    publication_status='checkpoint25_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial')
progress['working_next_checkpoint_preparation'].update(
    status='checkpoint25_passed_actual_frozen_audit_and_live_delivery_checkpoint26_isolated_candidates_in_progress')
progress_path.write_text(json.dumps(progress,indent=2)+'\n')
new=(f'Checkpoint 25 is [pushed to GitHub](https://github.com/PloxKevin/ploxkevin.github.io/commit/{commit}).\n'
     f'The [actual Pages workflow](https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/{run_id})\n'
     'completed successfully, and [live delivery](live-checkpoint-25-attempt1.json)\n'
     'matched all 31 book asset hashes and the built commit exactly.\n'
     'Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)\n')
readme_path.write_text(before.replace(old,new,1))
record={'status':'passed_actual_checkpoint25_delivery_progress_update',
    'updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(Path(__file__)),
    'originals':backups,'updated_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in [progress_path,readme_path]},
    'content_commit':commit,'pages_run':run_id,'coverage_complete':False,
    'evidence_sha256':{(REPORTS/n).relative_to(ROOT).as_posix():sha(REPORTS/n) for n in
        ['live-checkpoint-25-attempt1.json','pages-checkpoint-25-attempt1.json','publication25-pages-view-execution-v1.log',
         'lean-checkpoint-25/verification-original.json','frozen-ledger-checkpoint25-v1.json']},
    'scope':'Actual delivery metadata only; original proof and semantic review bodies and times unchanged.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'passed','content_commit':commit,'pages_run':run_id,'proof_files':1156,'theorems':9369,'coverage_complete':False}))
