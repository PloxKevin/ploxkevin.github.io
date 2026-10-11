from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,hashlib,json,sys
checker=Path('/tmp/check-documentation27-independent-foundations-genuine-native-v2.py')
target=Path(sys.argv[1]);version=sys.argv[2]
log=Path('/tmp/documentation27-independent-foundations-genuine-native-actual-'+version+'.log')
out=Path('/tmp/documentation27-independent-foundations-genuine-native-actual-'+version+'.json')
assert not log.exists() and not out.exists()
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p):digest(p) for p in [checker,target]};start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
command=['python3',str(checker),str(target),version]
with log.open('xb') as f:result=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed_genuine_native_prewrite_fixture_runner_only' if result.returncode==0 else 'failed_genuine_native_prewrite_fixture_runner','actual_exit_code':result.returncode,'actual_command':command,'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':{str(p):digest(p) for p in [checker,target]},'log':str(log),'log_sha256':digest(log),'scope':'Actual read-only full pre-write and genuine native guard fixtures only. No production writer/compiler/repository mutation and no independent approval inferred.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
raise SystemExit(result.returncode)
