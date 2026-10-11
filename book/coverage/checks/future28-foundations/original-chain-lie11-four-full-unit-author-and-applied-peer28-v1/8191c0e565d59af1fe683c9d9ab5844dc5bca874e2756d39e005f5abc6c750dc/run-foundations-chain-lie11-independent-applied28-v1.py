from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CHECK=Path('/tmp/check-foundations-chain-lie11-independent-applied28-v1.py');HELPER=Path('/tmp/CompleteFoundationsLiteralChainLie28-draft-v2.lean');REC=Path('/tmp/foundations-chain-lie11-independent-applied-actual28-v1.json');LOG=REC.with_suffix('.log')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not REC.exists() and not LOG.exists()
m=json.loads((ROOT/'reports/full-coverage/checkpoint-27-manifest.json').read_bytes());s=json.loads((ROOT/'reports/full-coverage/checkpoint-27-selection.json').read_bytes())
files={ROOT/n for n in s['proof_files']}|{ROOT/n for n in m['frozen_inputs_sha256'] if n.startswith('SafeLearning/')}|{ROOT/('book/coverage/'+n+'.json') for n in ['inventory','material-corrections','core','foundations','applied','modules','applied-promotions']}
before={str(p):sha(p) for p in sorted(files)};hb={str(p):sha(p) for p in [CHECK,HELPER]};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(['python3',str(CHECK)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick;after={str(p):sha(p) for p in sorted(files)};ha={str(p):sha(p) for p in [CHECK,HELPER]};errors=[]
if before!=after:errors.append('selected1175/current55 31/five installed27 or inventory/corrections changed')
if hb!=ha:errors.append('independent checker/helper bytes changed')
b={'scope':'Actual independent full-chain/Lie11 source/current four whole literal/native history binding reader; no compiler or mutation','actual_command':['python3',str(CHECK)],'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'actual_exit_code':r.returncode,'helper_sha256_before':hb,'helper_sha256_after':ha,'protected_sha256_before':before,'protected_sha256_after':after,'protection_errors':errors,'log':str(LOG),'log_sha256':sha(LOG)}
with REC.open('x') as f:f.write(json.dumps(b,indent=2)+'\n')
print(json.dumps({'actual_exit_code':r.returncode,'record':str(REC),'sha256':sha(REC),'log_sha256':sha(LOG),'protection_errors':errors}))
raise SystemExit(r.returncode if not errors else 1)
