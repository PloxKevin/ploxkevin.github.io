from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CHECK=Path('/tmp/check-foundations-allocation19-eight-full-literals-independent-applied28-v1.py');REQUEST=Path('/tmp/foundations-allocation19-full-review28-v1/foundations-allocation19-full-review28-v2.json');RECORD=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-actual28-v1.json');LOG=RECORD.with_suffix('.log')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert not RECORD.exists() and not LOG.exists()
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-27-selection.json').read_bytes());inventory=json.loads((ROOT/'book/coverage/inventory.json').read_bytes())
files=[ROOT/n for n in selection['proof_files']]+[ROOT/n for n in inventory['source_sha256']]+[ROOT/('book/coverage/'+n+'.json') for n in ['core','foundations','applied','modules','applied-promotions','inventory','material-corrections']]
before={str(p):sha(p) for p in files};helpers={str(p):sha(p) for p in [CHECK,REQUEST]};started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(['python3',str(CHECK)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after={str(p):sha(p) for p in files};helperafter={str(p):sha(p) for p in [CHECK,REQUEST]};errors=[]
if before!=after:errors.append('current selected1175/source55/five protected bodies changed during read-only review')
if helpers!=helperafter:errors.append('review checker/request bytes changed')
body={'scope':'Actual independent full19 bodies/eight entire physical literal semantic correspondence and read-only source/native provenance checker','actual_command':['python3',str(CHECK)],'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'actual_exit_code':p.returncode,'helper_sha256_before':helpers,'helper_sha256_after':helperafter,'protected_sha256_before':before,'protected_sha256_after':after,'protection_errors':errors,'log':str(LOG),'log_sha256':sha(LOG)}
with RECORD.open('x') as f:f.write(json.dumps(body,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'record':str(RECORD),'sha256':sha(RECORD),'log_sha256':sha(LOG),'protection_errors':errors}))
raise SystemExit(p.returncode if not errors else 1)
