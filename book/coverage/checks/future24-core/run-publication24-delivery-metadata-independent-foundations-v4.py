"""Actual measured independent Python checker, not a Root delivery execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).parent
SELF=Path(__file__).relative_to(ROOT).as_posix()
CHECKER=HERE/'check-publication24-delivery-metadata-independent-foundations-v4.py'
OUT=HERE/'publication24-delivery-metadata-independent-foundations-actual-v4.json'
LOG=OUT.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists() and not LOG.exists()
command=['python3',str(CHECKER.relative_to(ROOT))]
before=sha(CHECKER);started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,
   'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,
   'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,
   'checker_sha256_before':before,'checker_sha256_after':sha(CHECKER),
   'log':LOG.relative_to(ROOT).as_posix(),'log_sha256':sha(LOG),
   'runner':{'file':SELF,'sha256':sha(Path(__file__))},
   'scope':'Actual independent code checker with explicitly synthetic isolated fixtures; no production Root helper, Git, gh, Pages or Lean command executed.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d))
raise SystemExit(r.returncode)
