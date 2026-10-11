from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=Path('/tmp/check-checkpoint24-selector-retainer-independent-applied-v3.py')
OUT=Path('/tmp/checkpoint24-selector-retainer-independent-applied-actual-v3.json')
LOG=OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
before=sha(HELPER);started=datetime.now(timezone.utc);t=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(['python3',str(HELPER)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
ended=datetime.now(timezone.utc)
d={'kind':'independent_python_code_and_isolated_fixture_review','actual_exit_code':p.returncode,
 'command':['python3',str(HELPER)],'actual_workdir':str(ROOT),'helper_sha256_before':before,'helper_sha256_after':sha(HELPER),
 'log':str(LOG),'log_sha256':sha(LOG),'started_at_utc':started.isoformat(),'finished_at_utc':ended.isoformat(),
 'elapsed_seconds':time.monotonic()-t,'scope':'Actual Python checker execution only; fixtures are synthetic code tests, no production selector/compiler/integration run.'}
with OUT.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'actual_record':str(OUT),'actual_record_sha256':sha(OUT),'raw_log':str(LOG),'raw_log_sha256':sha(LOG)}))
raise SystemExit(p.returncode)
