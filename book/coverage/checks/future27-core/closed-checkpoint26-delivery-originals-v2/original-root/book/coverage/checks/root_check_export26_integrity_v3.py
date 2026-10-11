from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3];SNAP=ROOT/'reports/full-coverage/checkpoint-26';OUT=ROOT/'reports/full-coverage/lean-checkpoint-26'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
result=OUT/'export-output-integrity-v1.json';assert not result.exists()
original_path=SNAP/'reports/lean-verification/verification.json';original=read(original_path);relocated=read(OUT/'verification.json')
assert sha(original_path)==sha(OUT/'verification-original.json')
assert original['status']=='passed' and original['proof_file_count']==1167 and original['theorem_count']==9503
assert len(original['proof_sha256'])==1167
assert len(original['declarations'])==len(original['axiom_dependencies'])==9503
assert {d['name'] for d in original['declarations']}==set(original['axiom_dependencies'])
assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in original['checks'])
assert set(original['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(xs)<=set(original['allowed_standard_axioms']) for xs in original['axiom_dependencies'].values())
expected=copy.deepcopy(original)
for c in expected['checks']:
 for d,key in [(c,'output_file'),(c.get('reused_from',{}),'report')]:
  name=d.get(key)
  if isinstance(name,str) and name.startswith('reports/lean-verification/'):
   d[key]=name.replace('reports/lean-verification/','reports/full-coverage/lean-checkpoint-26/',1)
origin=relocated.pop('audit_origin');assert relocated==expected
assert origin['original_report']=='reports/full-coverage/lean-checkpoint-26/verification-original.json'
assert origin['original_report_sha256']==sha(original_path) and origin['actual_workdir']==str(SNAP/'verification/lean')
paths={}
for c in original['checks']:
 name=c['output_file'];target=OUT/Path(name).relative_to('reports/lean-verification');assert sha(SNAP/name)==sha(target)
 if 'log_sha256' in c:assert c['log_sha256']==sha(target)
 paths[str(target.relative_to(ROOT))]=sha(target)
 reused=c.get('reused_from',{})
 if reused:
  name=reused['report'];target=OUT/Path(name).relative_to('reports/lean-verification');assert sha(SNAP/name)==sha(target)==reused['report_sha256']
  paths[str(target.relative_to(ROOT))]=sha(target)
for field in ['source_sha256','proof_sha256','project_sha256']:
 for name,digest in original[field].items():assert sha(SNAP/name)==digest
fresh=sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in original['checks']);reused=sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in original['checks'])
assert fresh==11 and reused==1156
result.write_text(json.dumps({'status':'passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),'scope':'Exact compiler/kernel/axiom output bytes and unchanged original execution fields; only current exported output/report locations differ.','actual_check_count':len(original['checks']),'output_count':len(paths),'fresh_kernel_replays':fresh,'exact_original_kernel_replays_reused':reused,'original_report_sha256':sha(original_path),'paths_sha256':paths,'coverage_complete':False},indent=2)+'\n')
print(json.dumps({'status':'passed','checks':len(original['checks']),'outputs':len(paths),'fresh':fresh,'reused':reused}))
