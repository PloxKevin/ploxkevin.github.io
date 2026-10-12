from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-delivery31-metadata4-actual-inputs-independent-modules-v1.py');W=Path(__file__);N=Path('/tmp/delivery31-metadata4-actual-inputs-independent-modules-actual-v1.json');L=N.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not N.exists()and not L.exists();before={str(p):sha(p)for p in[H,W]};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['python3',str(H)]
with L.open('xb')as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
after={str(p):sha(p)for p in[H,W]};out={'status':'passed'if p.returncode==0 and before==after else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(L),'log_sha256':sha(L),'protection_errors':[]if before==after else['reader or wrapper changed'],'scope':'Independent metadata prep4 authentic content31/4786 actual committed blobs/immutable commit-push receipts/Pages3jobs/all31live attempt2 and preserved attempt1 failure inputs. No metadata producer/Git index/PUB/source/raw-owner mutation.'}
with N.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out));raise SystemExit(p.returncode)
