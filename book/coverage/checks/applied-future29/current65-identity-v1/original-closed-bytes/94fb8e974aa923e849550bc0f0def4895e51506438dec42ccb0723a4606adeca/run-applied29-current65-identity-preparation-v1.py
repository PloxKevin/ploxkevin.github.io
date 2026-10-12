from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,sys,time,copy
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELP=Path('/tmp/prepare-applied29-current65-identity-overlay-v1.py')
REC=Path('/tmp/applied29-current65-identity-candidate-preparation-actual-v1.json')
LOG=REC.with_suffix('.log')
CTX=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
assert not REC.exists() and not LOG.exists()
context=json.loads(CTX.read_bytes());protected={}
for m in (context['pins_sha256'],context['held_current_source_sha256'],context['owners_sha256']):
    for n,h in m.items():assert n not in protected or protected[n]==h;protected[n]=h
before={str(HELP):sha(HELP),str(Path(__file__)):sha(Path(__file__))}
for n,h in protected.items():assert sha(path(n))==h,n
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
cmd=['python3',str(HELP)]
with LOG.open('xb') as f:result=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
errors=[n for n,h in protected.items() if not path(n).is_file() or sha(path(n))!=h]
out={'status':'passed_actual_isolated_applied29_current65_identity_preparation' if result.returncode==0 and not errors else 'failed_actual_isolated_applied29_current65_identity_preparation',
     'actual_exit_code':result.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),
     'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
     'helper_sha256_before':before,'helper_sha256_after':{n:sha(n)for n in before},'log':str(LOG),'log_sha256':sha(LOG),
     'actual_source65_installed28_context':ref(CTX),'protection_errors':errors,
     'live_owner_or_source_or_publication_written':False}
with REC.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
if result.returncode==0 and not errors:
    draft=Path('/tmp/applied29-current65-identity-v1/applied29-current65-identity-offer-draft-v1.json')
    completed=copy.deepcopy(json.loads(draft.read_bytes()))
    completed['original_preparation_offer']=ref(draft)
    completed['actual_isolated_candidate_preparation']=ref(REC)
    completed['actual_finalizer']=ref(REC)
    completed['actual_preparation_runner']=ref(Path(__file__))
    completed['completed_receipt_attached_at_utc']=datetime.now(timezone.utc).isoformat()
    for p in (REC,LOG,Path(__file__)):
        n=str(p);h=sha(p);assert n not in completed['required_evidence_artifacts_sha256'] or completed['required_evidence_artifacts_sha256'][n]==h
        completed['required_evidence_artifacts_sha256'][n]=h
    final=draft.with_name('applied29-current65-identity-offer-draft-v2.json')
    with final.open('x') as f:f.write(json.dumps(completed,indent=2,ensure_ascii=False)+'\n')
    out['completed_offer']=ref(final)
print(json.dumps(out));sys.exit(result.returncode or bool(errors))
