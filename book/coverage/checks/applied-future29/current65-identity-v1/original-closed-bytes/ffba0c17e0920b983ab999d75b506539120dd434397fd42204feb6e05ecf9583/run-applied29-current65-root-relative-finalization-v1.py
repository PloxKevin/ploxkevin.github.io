from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/finalize-applied29-current65-root-relative-identity-v1.py');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');O=Path('/tmp/applied29-current65-root-relative-finalization-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def ref(p):return {'file':str(p),'sha256':sha(p)}
assert not O.exists() and not L.exists();assert sha(H)=='83a623198b304ec708e16b0a281a3939b62e847dbbde8f4b6086e385561c2695';ctx=json.loads(C.read_bytes());held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
for n,h in held.items():assert sha(path(n))==h,n
before={str(H):sha(H),str(Path(__file__)):sha(__file__)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(H),'--peer','book/coverage/checks/future29-applied/applied65-identity-independent-modules-v1/applied29-current65-identity-independent-modules29-closed-peer-v2.json','--peer-sha256','c51397adad3813449c1cb9efa7d7ac018ada23917644b8d87779f9c3b3fd624c','--apply']
with L.open('xb') as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
errors=[n for n,h in held.items() if sha(path(n))!=h]
d={'status':'passed_actual_exact_applied29_current65_root_relative_identity_finalization' if p.returncode==0 and not errors else 'failed_actual_exact_applied29_current65_root_relative_identity_finalization','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':{n:sha(n) for n in before},'log':str(L),'log_sha256':sha(L),'actual_source65_installed28_context':ref(C),'protection_errors':errors,'new_proof_or_semantic_review_claimed':False,'live_owner_or_source_or_publication_written':False}
with O.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
if p.returncode==0 and not errors:
 out=R/'book/coverage/checks/applied-future29/current65-identity-v1';orig=out/'applied29-current65-identity-offer-root-relative-v1.json';offer=json.loads(orig.read_bytes());offer['original_root_relative_preparation_offer']={'file':str(orig.relative_to(R)),'sha256':sha(orig)};offer['required_evidence_artifacts_sha256'][str(orig.relative_to(R))]=sha(orig)
 for source in [O,L,Path(__file__)]:
  h=sha(source);target=out/'original-closed-bytes'/h/source.name;target.parent.mkdir(parents=True,exist_ok=True)
  with target.open('xb') as f:f.write(source.read_bytes())
  q={'file':str(target.relative_to(R)),'sha256':h};offer['required_evidence_artifacts_sha256'][q['file']]=h;offer['original_closed_byte_aliases'][str(source)]=q
 offer['actual_root_relative_finalization']=offer['original_closed_byte_aliases'][str(O)];final=out/'applied29-current65-identity-offer-root-relative-v2.json'
 with final.open('x') as f:f.write(json.dumps(offer,indent=2,ensure_ascii=False)+'\n')
 d['completed_offer']={'file':str(final.relative_to(R)),'sha256':sha(final)}
print(json.dumps(d));raise SystemExit(p.returncode or bool(errors))
