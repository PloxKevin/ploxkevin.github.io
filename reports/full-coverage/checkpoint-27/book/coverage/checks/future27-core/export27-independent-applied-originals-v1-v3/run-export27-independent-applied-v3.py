from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time
ROOT=Path('/home/oxrexkevin/SafetyBased')
CHECK=Path('/tmp/check-export27-independent-applied-v3.py')
RECORD=Path('/tmp/export27-independent-applied-actual-v3.json')
LOG=RECORD.with_suffix('.log')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
helpers=[CHECK,ROOT/'book/coverage/export_audit.py',ROOT/'book/coverage/export_audit27_v1.py',ROOT/'book/coverage/export_audit27_v2.py',ROOT/'book/coverage/export_audit27_v3.py']
guards=[ROOT/'book/coverage/inventory.json',ROOT/'book/coverage/material-corrections.json']+[ROOT/('book/coverage/'+n+'.json') for n in ['core','foundations','applied','applied-promotions','modules']]
before={str(p):sha(p) for p in guards};helper_before={str(p):sha(p) for p in helpers}
start=datetime.now(timezone.utc).isoformat(); tick=time.monotonic()
with LOG.open('xb') as f: proc=subprocess.run(['python3',str(CHECK)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
after={str(p):sha(p) for p in guards};helper_after={str(p):sha(p) for p in helpers}
errors=[]
if before!=after: errors.append('current inventory/registry/installed-owner bytes changed during checker interval')
if helper_before!=helper_after: errors.append('checker/helper bytes changed during checker interval')
record={'scope':'Actual independent read-only helper/native fixture checker, not integration/validator or producer execution','actual_command':['python3',str(CHECK)],'actual_workdir':str(ROOT),'started_at_utc':start,'completed_at_utc':end,'elapsed_seconds':elapsed,'actual_exit_code':proc.returncode,'helper_sha256_before':helper_before,'helper_sha256_after':helper_after,'protected_sha256_before':before,'protected_sha256_after':after,'protection_errors':errors,'log':str(LOG),'log_sha256':sha(LOG)}
with RECORD.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'actual_exit_code':proc.returncode,'record':str(RECORD),'sha256':sha(RECORD),'log':str(LOG),'log_sha256':sha(LOG),'protection_errors':errors}))
raise SystemExit(proc.returncode if not errors else 1)
