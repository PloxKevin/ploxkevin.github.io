from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased')
H=Path('/tmp/review-freeze30-source-only2-independent-modules-v1.py')
O=Path('/tmp/freeze30-source-only2-independent-modules-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not O.exists() and not L.exists()
pins={n:sha(R/n) for n in ['book/coverage/freeze_checkpoint30_source_only_v2.py','book/coverage/freeze_checkpoint30_source_only_v1.py','book/coverage/lean_names.py','verification/lean/verify.py','reports/full-coverage/checkpoint-30-selection.json','reports/full-coverage/lean-checkpoint-30/verification-original.json']}
before={str(H):sha(H)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();command=['python3',str(H)]
p=subprocess.run(command,cwd=R,capture_output=True);L.write_bytes(p.stdout+p.stderr)
after={n:sha(n) for n in before};errors=[n for n,h in pins.items() if sha(R/n)!=h]
d={'status':'passed' if p.returncode==0 and before==after and not errors else 'failed','actual_command':command,'actual_workdir':str(R),'actual_exit_code':p.returncode,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(L),'log_sha256':sha(L),'raw_log':str(L),'raw_log_sha256':sha(L),'protected_inputs_sha256_before':pins,'protected_inputs_sha256_after':{n:sha(R/n) for n in pins},'protection_errors':errors,'compiler_started':False,'producer_invoked':False,'source_owner_and_publication_mutations':False,'old79_mutable_context_guard_invoked':False,'scope':'Independent full freezer2 code and immutable initial audit/selection schema reader only; no actual future final-CSS audit/freeze approval or producer invocation.'}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k] for k in ['status','actual_exit_code','elapsed_seconds','protection_errors']}));raise SystemExit(0 if d['status']=='passed' else 1)
