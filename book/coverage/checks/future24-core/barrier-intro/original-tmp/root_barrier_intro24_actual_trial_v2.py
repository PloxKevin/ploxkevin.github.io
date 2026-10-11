from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
root=Path('/home/oxrexkevin/SafetyBased')
source=Path('/tmp/CompleteBarrierIntroMaterial24-v2.lean')
snapshot=Path('/tmp/root-barrier-intro-material24-trial2.lean')
log=Path('/tmp/root-barrier-intro-material24-trial2.log')
record=Path('/tmp/root-barrier-intro-material24-trial2.json')
assert not any(p.exists() for p in (snapshot,log,record))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
snapshot.write_bytes(source.read_bytes());before=sha(snapshot)
command=['lake','env','lean',str(snapshot)]
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(command,cwd=root/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
after=sha(snapshot)
data={'status':'passed' if r.returncode==0 and before==after else 'failed','source':str(snapshot),'source_sha256_before':before,'source_sha256_after':after,'source_unchanged':before==after,'command':command,'actual_workdir':str(root/'verification/lean'),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'actual_exit_code':r.returncode,'log':str(log),'log_sha256':sha(log),'scope':'TMP-only future24 standalone execution. No canonical source, named target, owner row or checkpoint23 change.'}
record.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data));raise SystemExit(r.returncode)
