from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-modules-NN143-full-composition-static-bootstrap32-v1.py');W=Path(__file__);N=Path('/tmp/modules-NN143-full-composition-static-bootstrap32-actual-v1.json');L=N.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not N.exists()and not L.exists();before={str(p):sha(p)for p in[H,W]};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['python3',str(H)]
with L.open('xb')as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
after={str(p):sha(p)for p in[H,W]};out={'status':'passed'if p.returncode==0 and before==after else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(L),'log_sha256':sha(L),'protection_errors':[]if before==after else['reader or wrapper changed'],'scope':'Independent full exact proposed three-part Exercise14.3 composition under a dedicated static input guard. Prior62 complete independent component bodies are reused by exact prefix; all3 new Origin bodies are directly read and independently covered by7b311. Current raw32 changes are recorded as provenance only; no old0396 current context release, compiler, parser, Source, owner or publication mutation.'}
with N.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out));raise SystemExit(p.returncode)
