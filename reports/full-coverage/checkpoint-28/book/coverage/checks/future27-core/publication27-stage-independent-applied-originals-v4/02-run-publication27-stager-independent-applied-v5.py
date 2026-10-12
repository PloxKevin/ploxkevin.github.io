from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CHECK=Path('/tmp/check-publication27-stager-independent-applied-v4.py');HELPER=Path('/tmp/root_stage_publication27_v4.py');RECORD=Path('/tmp/publication27-stager-independent-applied-actual-v4.json');LOG=RECORD.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
files=[ROOT/'book/coverage/inventory.json',ROOT/'book/coverage/material-corrections.json']+[ROOT/('book/coverage/'+n+'.json') for n in ['core','foundations','applied','modules','applied-promotions']]
before={str(p):sha(p) for p in files};hbefore={str(p):sha(p) for p in [CHECK,HELPER]};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(['python3',str(CHECK)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
after={str(p):sha(p) for p in files};hafter={str(p):sha(p) for p in [CHECK,HELPER]};errors=[]
if before!=after:errors.append('installed27/source55 changed during fixture review')
if hbefore!=hafter:errors.append('helper/checker bytes changed during fixture review')
r={'scope':'Actual independent full-code/native prepare() fixtures in synthetic TMP root/PUB; no production stager/PUB/Git run','actual_command':['python3',str(CHECK)],'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'actual_exit_code':p.returncode,'helper_sha256_before':hbefore,'helper_sha256_after':hafter,'protected_sha256_before':before,'protected_sha256_after':after,'protection_errors':errors,'log':str(LOG),'log_sha256':sha(LOG)}
with RECORD.open('x') as f:f.write(json.dumps(r,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'record':str(RECORD),'sha256':sha(RECORD),'log_sha256':sha(LOG),'protection_errors':errors}))
raise SystemExit(p.returncode if not errors else 1)
