from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time,copy
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/prepare-core29-current65-candidate-v2.py');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');O=Path('/tmp/core29-current65-candidate-preparation-actual-v2.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def ref(p):return {'file':str(p),'sha256':sha(p)}
assert not O.exists() and not L.exists();ctx=json.loads(C.read_bytes());held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
for f,h in held.items():assert sha(path(f))==h,f
before={str(H):sha(H),str(Path(__file__)):sha(__file__)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(H)]
with L.open('xb') as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
errors=[f for f,h in held.items() if not path(f).is_file() or sha(path(f))!=h]
result={'status':'passed_actual_isolated_core29_current65_candidate_preparation' if p.returncode==0 and not errors else 'failed_actual_isolated_core29_current65_candidate_preparation','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':{f:sha(f) for f in before},'log':str(L),'log_sha256':sha(L),'actual_source65_installed28_context':ref(C),'protection_errors':errors,'live_owner_or_source_or_publication_written':False,'canonical_pair_claimed':False}
with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
if p.returncode==0 and not errors:
 orig=Path('/tmp/core29-current65-approved-candidate-v2/core29-current65-three-source-pending-pair-offer-v1.json');d=json.loads(orig.read_bytes());d['original_preparation_offer']=ref(orig);d['actual_finalizer']=ref(O);d['actual_candidate_preparation']=ref(O)
 for f in [O,L,Path(__file__)]:d['required_evidence_artifacts_sha256'][str(f)]=sha(f)
 final=orig.with_name('core29-current65-three-source-pending-pair-offer-v2.json')
 with final.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
 result['completed_offer']=ref(final)
print(json.dumps(result));raise SystemExit(p.returncode or bool(errors))
