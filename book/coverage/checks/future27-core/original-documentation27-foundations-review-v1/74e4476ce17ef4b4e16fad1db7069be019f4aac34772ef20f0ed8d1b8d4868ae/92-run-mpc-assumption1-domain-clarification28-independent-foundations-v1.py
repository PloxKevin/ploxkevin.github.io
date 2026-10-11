from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,hashlib,json
helper=Path('/tmp/check-mpc-assumption1-domain-clarification28-independent-foundations-v1.py')
log=Path('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-actual-v1.log')
out=Path('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-actual-v1.json')
assert not log.exists() and not out.exists()
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=digest(helper);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
command=['python3',str(helper)]
with log.open('xb') as f:result=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed_actual_independent_primary_literal_parser_semantic_reader' if result.returncode==0 else 'failed_actual_independent_reader','actual_exit_code':result.returncode,'actual_command':command,'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':digest(helper),'raw_log':str(log),'raw_log_sha256':digest(log),'scope':'Fresh full29 read-only parser and independent semantic/literal review evidence only. No compiler/source/coverage/metadata/Git mutation.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
raise SystemExit(result.returncode)
