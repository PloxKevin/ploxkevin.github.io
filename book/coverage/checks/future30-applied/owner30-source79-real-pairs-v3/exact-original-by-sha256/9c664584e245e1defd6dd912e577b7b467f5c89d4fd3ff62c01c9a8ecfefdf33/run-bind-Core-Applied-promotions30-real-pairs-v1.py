from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp/applied30b-owner30-paired-v1')
HELPER=TMP/'bind-Core-Applied-promotions30-real-pairs-v1.py';NATIVE=TMP/'Core-Applied-promotions30-real-pair-binding-actual-v1.json';LOG=NATIVE.with_suffix('.log')
assert not NATIVE.exists() and not LOG.exists();before=hashlib.sha256(HELPER.read_bytes()).hexdigest();cmd=['python3',str(HELPER)]
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),
 'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
 'helper_sha256_before':{str(HELPER):before},'helper_sha256_after':{str(HELPER):hashlib.sha256(HELPER.read_bytes()).hexdigest()},
 'log':str(LOG),'log_sha256':hashlib.sha256(LOG.read_bytes()).hexdigest(),
 'recorder':{'file':str(Path(__file__)),'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
 'scope':'Genuine actual90 canonical pair bindings and exact original raw29 forward/inverse for isolated Core/Applied/promos30 candidates; no compiler or live owner/source/canonical/publication writes.'}
with NATIVE.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d));raise SystemExit(r.returncode)
