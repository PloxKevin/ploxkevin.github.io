from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-publisher31-supplements3-independent-modules-v3.py');N=Path('/tmp/publisher31-supplements3-independent-modules-actual-v3.json');L=N.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not N.exists()and not L.exists();before=sha(H);cmd=['python3',str(H)];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with L.open('xb')as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick;after=sha(H)
out={'status':'passed'if p.returncode==0 and before==after else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':elapsed,'helper_sha256_before':{str(H):before},'helper_sha256_after':{str(H):after},'log':str(L),'log_sha256':sha(L),'protection_errors':[]if before==after else['reader helper changed'],'scope':'Actual independent full publisher31/supplements3 code and existing real input closure reader under0396. Pure read-only Git observations; no producer/config/PUB/index/source mutations.'}
with N.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out));raise SystemExit(p.returncode)
