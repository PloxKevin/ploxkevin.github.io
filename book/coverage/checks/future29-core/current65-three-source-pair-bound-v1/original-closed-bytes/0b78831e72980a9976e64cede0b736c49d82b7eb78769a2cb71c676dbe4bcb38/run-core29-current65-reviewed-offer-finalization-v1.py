from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/finalize-core29-current65-reviewed-offer-v1.py');O=Path('/tmp/core29-current65-reviewed-offer-finalization-actual-v1.json');L=O.with_suffix('.log');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):p=Path(n);return p if p.is_absolute() else R/p
assert not O.exists() and not L.exists();ctx=json.loads(C.read_bytes());held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
for n,h in held.items():assert sha(path(n))==h
before={str(H):sha(H),str(Path(__file__)):sha(__file__)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(H)]
with L.open('xb') as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
errors=[n for n,h in held.items() if sha(path(n))!=h];d={'status':'passed_actual_core29_reviewed_offer_finalization' if p.returncode==0 and not errors else 'failed_actual_core29_reviewed_offer_finalization','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':{n:sha(n) for n in before},'log':str(L),'log_sha256':sha(L),'protection_errors':errors,'live_owner_written':False}
with O.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
if p.returncode==0 and not errors:
 B=R/'book/coverage/checks/future29-core/current65-three-source-pair-bound-v1';F=B/'core29-current65-three-source-reviewed-offer-v1.json';of=json.loads(F.read_bytes());of['original_completed_final_offer']={'file':str(F.relative_to(R)),'sha256':sha(F)};of['required_evidence_artifacts_sha256'][str(F.relative_to(R))]=sha(F)
 for pth in [O,L,Path(__file__)]:
  h=sha(pth);q=B/'original-closed-bytes'/h/pth.name;q.parent.mkdir(parents=True,exist_ok=True)
  with q.open('xb') as f:f.write(pth.read_bytes())
  r={'file':str(q.relative_to(R)),'sha256':h};of['required_evidence_artifacts_sha256'][r['file']]=h;of['original_closed_byte_aliases'][str(pth)]=r
 of['actual_final_offer_preparation']=of['original_closed_byte_aliases'][str(O)];fin=B/'core29-current65-three-source-reviewed-offer-v2.json'
 with fin.open('x') as f:f.write(json.dumps(of,indent=2,ensure_ascii=False)+'\n')
 d['completed_offer']={'file':str(fin.relative_to(R)),'sha256':sha(fin)}
print(json.dumps(d));raise SystemExit(p.returncode or bool(errors))
