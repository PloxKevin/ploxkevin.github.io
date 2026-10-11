"""Record completed26 delivery from actual workflow and all31 live hashes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
def safe(n):
    assert isinstance(n,str) and n and str(Path(n))==n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def actual(stem):
    d=read(REPORTS/(stem+'.json'))
    codes=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert codes and all(type(code) is int and code==0 for code in codes)
    assert sha(safe(d['log']))==d['log_sha256']
    assert d['actual_workdir'] in (str(ROOT),str(PUB))
    return d

out=REPORTS/'progress-checkpoint26-delivery-update-v1.json'
assert not out.exists()
live=read(REPORTS/'live-checkpoint-26-attempt1.json');commit=live['commit']
assert live['status']=='passed_all31_asset_sha256' and len(live['assets'])==31
assert live['remote_main']==commit
assert subprocess.run(['git','rev-parse','HEAD'],cwd=PUB,check=True,capture_output=True).stdout.decode().strip()==commit
pages=read(REPORTS/'pages-checkpoint-26-attempt1.json')
assert pages['status']=='passed' and pages['commit']==pages['expected_commit']==commit
stems=['publication26-content-commit-execution-v1','publication26-content-push-execution-v1',
    'publication26-pages-watch-execution-v1','publication26-pages-view-execution-v1',
    'publication26-pages-artifact-execution-v1','live26-attempt1-execution-v1']
records={s:actual(s) for s in stems}
workflow=read(REPORTS/'publication26-pages-view-execution-v1.log')
assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
assert workflow['jobs'] and all(j['conclusion']=='success' for j in workflow['jobs'])
command=records['publication26-pages-view-execution-v1']['actual_command']
assert command[:3]==['gh','run','view'] and command[3].isdigit();run_id=int(command[3])
manifest=read(REPORTS/'checkpoint-26-manifest.json')
audit=read(REPORTS/'lean-checkpoint-26/verification-original.json')
ledger=read(REPORTS/'frozen-ledger-checkpoint26-v1.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert len(manifest['proof_files'])==audit['proof_file_count']==1167 and audit['theorem_count']==9503
assert audit['status']=='passed' and all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9503
assert {d['name'] for d in audit['declarations']}==set(audit['axiom_dependencies'])
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(xs)<=set(audit['allowed_standard_axioms']) for xs in audit['axiom_dependencies'].values())
assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==11
assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1156
assert manifest['successful_verification']['report_sha256']==sha(REPORTS/'lean-checkpoint-26/verification-original.json')
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and len({row['source'] for row in live['assets']})==31
assert {row['source']:row['expected_sha256'] for row in live['assets']}==assets
for row in live['assets']:
    assert row['http_status']==200 and row['matches'] is True
    assert row['actual_sha256']==row['expected_sha256']==sha(safe(row['source']))==sha(PUB/row['source'])
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
counts=ledger['counts'];states=counts['statuses'];materials=counts['material_review_statuses']
assert counts['exercises']==556 and counts['material_source_units']==12774
excounts={label:states.get('exercise:'+key,0) for label,key in [('complete','complete_math'),('partial','partial'),('pending','pending')]}
assert sum(excounts.values())==556 and sum(materials.values())==12774
assert sha(ROOT/'book/coverage/inventory.json')==sha(ROOT/'book/coverage/inventory-after-correction53.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
assert len(read(ROOT/'book/coverage/material-corrections.json')['corrections'])==53
progress_path=ROOT/'book/coverage/progress.json';readme_path=REPORTS/'README.md'
progress=read(progress_path)
assert progress['verified_checkpoint']['proof_files']==1167 and progress['verified_checkpoint']['theorems']==9503
assert progress['verified_checkpoint']['coverage_complete'] is False
assert progress['publication_status']=='checkpoint26_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
assert progress['last_published_content_commit']==progress['previous_checkpoint25_delivery']['content_commit']
assert progress['working_next_checkpoint_preparation']['exercise_counts']==excounts
assert progress['working_next_checkpoint_preparation']['material_review_units']==materials
before=readme_path.read_text()
old="in the progress history. Checkpoint26 awaits its own actual push, Pages build and live checks.\n"
assert before.count(old)==1
backup_names=['progress-checkpoint26-before-delivery-update-original-v1.json','README-checkpoint26-before-delivery-update-original-v1.md']
assert all(not (REPORTS/name).exists() for name in backup_names)
backups={}
for source,name in zip([progress_path,readme_path],backup_names):
    target=REPORTS/name;shutil.copyfile(source,target);assert sha(source)==sha(target)
    backups[source.relative_to(ROOT).as_posix()]=ref(target)
progress.update(last_published_commit=commit,last_published_content_commit=commit,
    live_delivery_status=live['status'],live_delivery_evidence='reports/full-coverage/live-checkpoint-26-attempt1.json',
    publication_status='checkpoint26_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial')
progress['working_next_checkpoint_preparation']['status']='checkpoint26_passed_actual_frozen_audit_and_live_delivery_full_coverage_work_continues'
progress_path.write_text(json.dumps(progress,indent=2)+'\n')
new=(f'in the progress history. Checkpoint 26 is [pushed to GitHub](https://github.com/PloxKevin/ploxkevin.github.io/commit/{commit}).\n'
     f'The [actual Pages workflow](https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/{run_id})\n'
     'completed successfully, and [live delivery](live-checkpoint-26-attempt1.json)\n'
     'matched all 31 book asset hashes and the built commit exactly. Full coverage work continues.\n')
readme_path.write_text(before.replace(old,new,1))
evidence_names=['live-checkpoint-26-attempt1.json','pages-checkpoint-26-attempt1.json','publication26-pages-view-execution-v1.log',
    'lean-checkpoint-26/verification-original.json','frozen-ledger-checkpoint26-v1.json']
for stem in stems:evidence_names.extend([stem+'.json',stem+'.log'])
record={'status':'passed_actual_checkpoint26_delivery_progress_update',
    'updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(Path(__file__)),
    'originals':backups,'updated_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in [progress_path,readme_path]},
    'content_commit':commit,'pages_run':run_id,'exercise_counts':excounts,'material_review_units':materials,'coverage_complete':False,
    'evidence_sha256':{(REPORTS/n).relative_to(ROOT).as_posix():sha(REPORTS/n) for n in evidence_names},
    'scope':'Actual delivery metadata only; original proof and semantic review bodies and times unchanged.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'passed','content_commit':commit,'pages_run':run_id,'proof_files':1167,'theorems':9503,'coverage_complete':False}))
