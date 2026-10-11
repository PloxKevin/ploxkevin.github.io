from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/check-core28-current60-identity-independent-foundations-v1.py');OUT=Path('/tmp/core28-current60-identity-independent-foundations-actual-v1.json');LOG=OUT.with_suffix('.log')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists()and not LOG.exists()
pins=json.loads((R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json').read_bytes())['protected_inputs_sha256']
before={n:h(R/n)for n in pins};assert before==pins
hp=h(HELPER);command=['python3',str(HELPER)];started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with LOG.open('xb')as f:proc=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t;after={n:h(R/n)for n in pins};errors=[n for n,s in pins.items()if after[n]!=s]
d={'status':'passed'if proc.returncode==0 and not errors else'failed','actual_exit_code':proc.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':elapsed,'checker':{'file':str(HELPER),'sha256':hp},'checker_sha256_before':hp,'checker_sha256_after':h(HELPER),'runner':{'file':str(Path(__file__)),'sha256':h(Path(__file__))},'raw_log':str(LOG),'raw_log_sha256':h(LOG),'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'compiler_or_canonical_owner_source_mutated':False}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'actual_record':str(OUT),'sha256':h(OUT),'actual_exit_code':proc.returncode,'elapsed_seconds':elapsed,'raw_log_sha256':h(LOG),'protection_errors':errors}))
raise SystemExit(proc.returncode if proc.returncode else int(bool(errors)))
