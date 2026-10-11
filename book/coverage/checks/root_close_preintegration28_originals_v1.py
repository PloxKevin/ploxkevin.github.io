"""Retain exact failed and passing Root records without reinterpreting executions."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/future28-core/original-root28-preintegration-native-v1'
records=[
 'reports/full-coverage/prepare-owner28-binding-execution-v1.json',
 'reports/full-coverage/prepare-owner28-binding-execution-v2.json',
 'reports/full-coverage/owner28-binding-preflight-execution-v1.json',
 'reports/full-coverage/owner28-candidate-integrity-diagnostic-execution-v1.json',
 'reports/full-coverage/browser28-evidence-merge-execution-v1.json',
 *['reports/full-coverage/source60-math-scroll28-execution-v'+str(i)+'.json' for i in [1,2,3]]]
inputs=records+[
 'reports/full-coverage/owner28-isolated-candidate-integrity-diagnostic-v1.json',
 'reports/full-coverage/source60-four-page-math-scroll28-v2.json',
 'reports/full-coverage/source60-four-page-math-scroll28-v3.json',
 'book/coverage/checks/future28-core/current60-owner28-binding-v1.json',
 *['book/coverage/checks/root_integrate_owner28_candidates_v'+str(i)+'.py' for i in range(1,7)],
 *['book/coverage/checks/root_prepare_owner28_binding_v'+str(i)+'.py' for i in range(1,5)],
 *['book/coverage/checks/root_check_math_scroll28_v'+str(i)+'.mjs' for i in [1,2,3]],
 'book/coverage/checks/root_diagnose_owner28_candidate_integrity_v1.py',
 'book/coverage/checks/root_prepare_browser28_v1.py']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n in records:
 d=json.loads((ROOT/n).read_bytes());assert type(d['actual_exit_code']) is int
 assert sha(ROOT/d['log'])==d['log_sha256'];inputs.append(d['log'])
 assert d['helper_sha256_before']==d['helper_sha256_after']
 for h,v in d['helper_sha256_after'].items():assert sha(ROOT/h)==v;inputs.append(h)
inputs=sorted(set(inputs));out=ROOT/BASE;assert not out.exists();aliases={}
for n in inputs:
 p=ROOT/n;assert p.is_file() and p.resolve().is_relative_to(ROOT)
 h=sha(p);suffix='.txt' if p.suffix=='.mjs' else p.suffix
 target=out/'by-sha256'/h/(p.stem+suffix);target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert sha(target)==h
 else:
  with target.open('xb') as f:f.write(p.read_bytes())
 assert sha(target)==h;aliases[n]={'file':target.relative_to(ROOT).as_posix(),'sha256':h}
result={'status':'exact_root_preintegration28_native_failures_successes_and_original_helpers_closed',
 'closed_at_utc':datetime.now(timezone.utc).isoformat(),'aliases':aliases,'original_count':len(inputs),
 'native_records':{n:{'actual_exit_code':json.loads((ROOT/n).read_bytes())['actual_exit_code'],'original_ref':aliases[n]} for n in records},
 'scope':'Exact byte aliases only. Failed records stay failed, prior timestamps and running/failed browser diagnostic bodies remain untouched. No semantic approval, owner installation, aggregate audit or publication inferred.'}
p=out/'original-closed-byte-aliases-v1.json'
with p.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'original_count':len(inputs),'catalog':{'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}}))
