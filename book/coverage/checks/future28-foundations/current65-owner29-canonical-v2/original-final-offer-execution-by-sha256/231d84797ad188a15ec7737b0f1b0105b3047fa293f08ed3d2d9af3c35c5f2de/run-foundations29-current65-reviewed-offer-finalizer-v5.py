from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/finalize-foundations29-current65-reviewed-offer-v5.py');N=Path('/tmp/foundations29-current65-reviewed-offer-finalizer-actual-v5.json');L=N.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not N.exists() and not L.exists();hs=sha(H);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(H)]
with L.open('xb') as log:r=subprocess.run(cmd,cwd=R,stdout=log,stderr=subprocess.STDOUT)
out={'status':'passed' if r.returncode==0 else 'failed','actual_command':cmd,'command':cmd,'workdir':str(R),'cwd':str(R),'helper':{'file':str(H),'sha256':hs},'helper_sha256_before':hs,'helper_sha256_after':sha(H),'actual_exit_code':r.returncode,'exit_code':r.returncode,'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'log':{'file':str(L),'sha256':sha(L)}}
N.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));raise SystemExit(r.returncode)
