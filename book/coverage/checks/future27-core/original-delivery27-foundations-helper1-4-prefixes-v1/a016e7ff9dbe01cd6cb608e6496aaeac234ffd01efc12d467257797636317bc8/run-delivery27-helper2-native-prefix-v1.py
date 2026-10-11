from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_close_publication27_delivery_v2.py');CHECKER=Path('/tmp/check-delivery27-helper2-native-prefix-v1.py')
ACTUAL=Path('/tmp/delivery27-helper2-native-prefix-actual-v1.json');LOG=ACTUAL.with_suffix('.log');assert not ACTUAL.exists() and not LOG.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
command=['python3',str(CHECKER)];before={str(p):sha(p) for p in (HELPER,CHECKER)};start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':{str(p):sha(p) for p in (HELPER,CHECKER)},'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))}}
with ACTUAL.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
assert d['helper_sha256_before']==d['helper_sha256_after'];print(json.dumps(d));print(LOG.read_text());raise SystemExit(r.returncode)
