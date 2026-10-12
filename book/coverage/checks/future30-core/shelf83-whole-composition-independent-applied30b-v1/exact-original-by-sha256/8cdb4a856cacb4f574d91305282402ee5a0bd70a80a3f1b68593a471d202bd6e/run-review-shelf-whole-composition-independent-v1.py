from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time
ROOT=Path('/home/oxrexkevin/SafetyBased')
READER=Path('/tmp/applied30b-shelf-composition-v1/review-shelf-whole-composition-independent-v1.py')
NATIVE=Path('/tmp/applied30b-shelf-composition-v1/independent-shelf-whole-composition-reader-actual-v1.json')
LOG=NATIVE.with_suffix('.log')
assert not NATIVE.exists() and not LOG.exists()
helper_before=hashlib.sha256(READER.read_bytes()).hexdigest()
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as out:
    run=subprocess.run(['python3',str(READER)],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
record={'status':'passed' if run.returncode==0 else 'failed','actual_exit_code':run.returncode,
        'actual_command':['python3',str(READER)],'actual_workdir':str(ROOT),
        'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
        'elapsed_seconds':time.monotonic()-tick,
        'helper_sha256_before':{str(READER):helper_before},
        'helper_sha256_after':{str(READER):hashlib.sha256(READER.read_bytes()).hexdigest()},
        'log':str(LOG),'log_sha256':hashlib.sha256(LOG.read_bytes()).hexdigest(),
        'recorder':{'file':str(Path(__file__)),'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
        'scope':'Genuine independent full mathematical/literal Shelf83 composition review closure; original bodies and times preserved, no compiler or producer execution.'}
with NATIVE.open('x') as out:
    json.dump(record,out,indent=2);out.write('\n')
print(json.dumps(record))
raise SystemExit(run.returncode)
