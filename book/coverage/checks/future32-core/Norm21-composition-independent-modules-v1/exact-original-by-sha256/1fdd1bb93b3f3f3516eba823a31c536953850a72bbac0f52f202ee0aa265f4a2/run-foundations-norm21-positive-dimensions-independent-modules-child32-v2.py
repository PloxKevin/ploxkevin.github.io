from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-foundations-norm21-positive-dimensions-independent-modules-child32-v2.py');W=Path(__file__);C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');RUN=Path('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py');N=Path('/tmp/modules-child-norm21-positive-dimensions-independent32-actual-v2.json');L=N.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not N.exists() and not L.exists();before={str(p):sha(p) for p in [H,W,C,RUN]};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['python3',str(H)]
with L.open('xb') as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
after={str(p):sha(p) for p in [H,W,C,RUN]};out={'status':'passed' if p.returncode==0 and before==after else 'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(L),'log_sha256':sha(L),'protection_errors':[] if before==after else ['reader,wrapper,context or runner changed'],'scope':'Independent narrow one-phrase positive dimensions literal/support and fresh BOTH ROOT/OUT TMP full29 parser. Whole21 mathematics, source ordinal, source application and canonical/publication remain separate.'}
with N.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out));raise SystemExit(p.returncode)
