from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased')
checker=Path('/tmp/check-foundations27-reviewed-offer-closure-preflight-v1.py')
record=Path('/tmp/foundations27-reviewed-offer-closure-preflight-actual-v1.json')
log=record.with_suffix('.log')
assert not record.exists() and not log.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=root/'book/coverage/checks/root_close_foundations27_reviewed_offer_v1.py'
before=sha(helper);checker_before=sha(checker)
start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
command=['python3',str(checker)]
with log.open('xb') as f:r=subprocess.run(command,cwd=root,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat()
d={'status':'passed_author_read_only_native_preflight' if r.returncode==0 else 'failed_author_read_only_native_preflight','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(root),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':sha(helper),'checker_sha256_before':checker_before,'checker_sha256_after':sha(checker),'raw_log':str(log),'raw_log_sha256':sha(log),'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'scope':'Author read-only code/native preflight only; no independent approval, producer execution, canonical copies or live changes.'}
with record.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(r.returncode)
