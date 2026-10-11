from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CHECK=Path('/tmp/check-foundations-literal-partial7-independent-applied28-v1.py');HELPER=Path('/tmp/CompleteFoundationsLiteralPartialPitfall28-draft-v3.lean');RECORD=Path('/tmp/foundations-literal-partial7-independent-applied-actual28-v1.json');LOG=RECORD.with_suffix('.log')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-27-manifest.json').read_bytes())
files=[ROOT/'book/coverage/inventory.json',ROOT/'book/coverage/material-corrections.json']+[ROOT/('book/coverage/'+n+'.json') for n in ['core','foundations','applied','modules','applied-promotions']]+[ROOT/n for n in manifest['frozen_inputs_sha256'] if n.startswith('SafeLearning/')]
before={str(p):sha(p) for p in files};hbefore={str(p):sha(p) for p in [CHECK,HELPER]};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(['python3',str(CHECK)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
after={str(p):sha(p) for p in files};hafter={str(p):sha(p) for p in [CHECK,HELPER]};errors=[]
if before!=after:errors.append('installed27/source55 current38 inputs changed during read-only review')
if hbefore!=hafter:errors.append('helper/checker bytes changed during review')
body={'scope':'Actual read-only independent full-source literal186 seven-body semantic/binding review; no compiler/producer/ledger change','actual_command':['python3',str(CHECK)],'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'actual_exit_code':p.returncode,'helper_sha256_before':hbefore,'helper_sha256_after':hafter,'protected_sha256_before':before,'protected_sha256_after':after,'protection_errors':errors,'log':str(LOG),'log_sha256':sha(LOG)}
with RECORD.open('x') as f:f.write(json.dumps(body,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'record':str(RECORD),'sha256':sha(RECORD),'log_sha256':sha(LOG),'protection_errors':errors}))
raise SystemExit(p.returncode if not errors else 1)
