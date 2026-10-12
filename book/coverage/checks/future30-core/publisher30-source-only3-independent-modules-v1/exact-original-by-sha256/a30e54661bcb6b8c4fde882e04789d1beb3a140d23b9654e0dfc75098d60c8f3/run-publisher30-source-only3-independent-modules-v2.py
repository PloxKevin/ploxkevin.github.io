from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-publisher30-source-only3-independent-modules-v2.py')
O=Path('/tmp/publisher30-source-only3-independent-modules-actual-v2.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not O.exists() and not L.exists()
pins={n:sha(R/n) for n in ['book/coverage/prepare_publication30_source_only_v3.py','book/coverage/prepare_publication30_source_only_v2.py','book/coverage/freeze_checkpoint30_source_only_v2.py','reports/full-coverage/checkpoint-30-manifest.json','reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json']}
before={str(H):sha(H)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();command=['python3',str(H)]
p=subprocess.run(command,cwd=R,capture_output=True);L.write_bytes(p.stdout+p.stderr)
after={n:sha(n) for n in before};errors=[n for n,h in pins.items() if sha(R/n)!=h]
d={'status':'passed' if p.returncode==0 and before==after and not errors else 'failed','actual_command':command,'actual_workdir':str(R),'actual_exit_code':p.returncode,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(L),'log_sha256':sha(L),'raw_log':str(L),'raw_log_sha256':sha(L),'protected_inputs_sha256_before':pins,'protected_inputs_sha256_after':{n:sha(R/n) for n in pins},'protection_errors':errors,'compiler_started':False,'producer_invoked':False,'source_owner_and_publication_mutations':False,'old79_mutable_context_guard_invoked':False,'scope':'Independent full publisher3 code, exact v2 Git-boundary correction, immutable actual final-CSS/source-only manifest schema and frozen hash reader; readonly publication baseline HEAD/status. No producer/Git write/future delivery approval.'}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k] for k in ['status','actual_exit_code','elapsed_seconds','protection_errors']}));raise SystemExit(0 if d['status']=='passed' else 1)
