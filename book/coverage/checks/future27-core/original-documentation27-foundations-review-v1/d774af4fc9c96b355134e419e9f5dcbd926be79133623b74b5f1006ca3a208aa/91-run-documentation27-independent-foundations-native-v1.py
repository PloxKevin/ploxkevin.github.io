from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,hashlib,json
helper=Path('/tmp/check-documentation27-independent-foundations-native-v1.py')
log=Path('/tmp/documentation27-independent-foundations-native-actual-v1.log')
out=Path('/tmp/documentation27-independent-foundations-native-actual-v1.json')
assert not log.exists() and not out.exists()
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=digest(helper);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
command=['python3',str(helper)]
with log.open('xb') as f:result=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed_fixture_runner_only' if result.returncode==0 else 'failed_fixture_runner','actual_exit_code':result.returncode,'actual_command':command,'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':digest(helper),'log':str(log),'log_sha256':digest(log),'scope':'Isolated native-schema pre-write fixtures only. No production writer/compiler/repository mutation and no checkpoint27 verification claim.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
raise SystemExit(result.returncode)
