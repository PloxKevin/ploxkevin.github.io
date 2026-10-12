from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/prepare-foundations-basics-bibliography8-classification28-v1.py');A=Path('/tmp/foundations-basics-bibliography8-classification28-actual-v1.json');L=A.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
before=sha(H);cmd=['python3',str(H)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
assert not A.exists() and not L.exists()
with L.open('xb') as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
after=sha(H);o={'status':'passed' if p.returncode==0 and before==after else 'failed','actual_exit_code':p.returncode,'command':cmd,'cwd':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper':{'file':str(H),'sha256_before':before,'sha256_after':after},'runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':{'file':str(L),'sha256':sha(L)},'producer_or_compiler_or_source_owner_writer_executed':False}
with A.open('x') as f:f.write(json.dumps(o,indent=2)+'\n')
print(json.dumps({k:v for k,v in o.items() if k not in ['helper','runner','command']}));raise SystemExit(0 if o['status']=='passed' else 1)
