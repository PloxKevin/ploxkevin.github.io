from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
CHECK=Path('/tmp/review-root29-delivery-helper-independent-foundations-v2.py')
OUT=Path('/tmp/root29-delivery-helper-independent-foundations-actual-v2.json')
LOG=Path('/tmp/root29-delivery-helper-independent-foundations-actual-v2.log')
assert not OUT.exists() and not LOG.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((ROOT/'reports/full-coverage/checkpoint-28-selection.json').read_bytes())['proof_files']
expected={n:r['sha256'] for n,r in base.items()}
for name in ['book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json','book/coverage/checks/future29-core/current65-monitoring29-canonical-pair-v1/actual-reviewed29-canonical-paired-readiness-v1.json']:
 d=json.loads((ROOT/name).read_bytes())
 for r in d['sources']:
  n,h=r['canonical_source'],r['original_tmp_source']['sha256'];assert n not in expected;expected[n]=h
assert len(expected)==1197
protected={**expected,**{n:sha(ROOT/n) for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/progress.json','reports/full-coverage/README.md','reports/full-coverage/root-source65-final-owner-integration29-v1.json',*['book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']]]}}
protected.update({str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'SafeLearning').iterdir() if p.suffix in ['.html','.css','.js']})
assert len([n for n in protected if n.startswith('SafeLearning/')])==31
assert all(sha(ROOT/n)==h for n,h in protected.items())
assert protected['book/coverage/inventory.json']=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert protected['book/coverage/material-corrections.json']=='5c3a871bbc5782a02c5b19bfa33a8fa6e4dc311a9e72c525d76fcc526f37eafd'
started=datetime.now(timezone.utc).isoformat();t=time.monotonic();before={str(CHECK):sha(CHECK)}
r=subprocess.run(['python3',str(CHECK)],cwd=ROOT,capture_output=True)
LOG.write_bytes(r.stdout+r.stderr);after={str(CHECK):sha(CHECK)}
errors=[n for n,h in protected.items() if sha(ROOT/n)!=h]
d={'status':'passed' if r.returncode==0 and not errors and before==after else 'failed','actual_command':['python3',str(CHECK)],'actual_workdir':str(ROOT),'actual_exit_code':r.returncode,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(LOG),'log_sha256':sha(LOG),'protected_inputs_sha256_before':protected,'protected_inputs_sha256_after':{n:sha(ROOT/n) for n in protected},'protection_errors':errors,'scope':'Measured full code and authentic immutable28 native-schema review only. Findings are pending repairs; no producer/readiness/PUB/Git/Lean execution or future29 success.'}
OUT.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k] for k in ['status','actual_exit_code','elapsed_seconds','protection_errors']}));raise SystemExit(0 if d['status']=='passed' else 1)
