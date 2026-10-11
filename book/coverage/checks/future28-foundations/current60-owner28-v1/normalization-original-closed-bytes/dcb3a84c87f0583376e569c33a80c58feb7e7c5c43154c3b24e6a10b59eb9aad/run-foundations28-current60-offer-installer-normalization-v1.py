from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=Path('/tmp/normalize-foundations28-current60-offer-for-installer-v1.py')
OUT=Path('/tmp/foundations28-current60-offer-installer-normalization-actual-v1.json')
LOG=OUT.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists() and not LOG.exists()
ready=json.loads((ROOT/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json').read_bytes())
pins=ready['protected_inputs_sha256'];before={n:sha(ROOT/n) for n in pins};assert before==pins
started=datetime.now(timezone.utc).isoformat();t=time.monotonic();hp=sha(HELPER)
command=['python3',str(HELPER)]
with LOG.open('xb') as f:p=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t
after={n:sha(ROOT/n) for n in pins};errors=[n for n,h in pins.items() if after[n]!=h]
d={'status':'passed' if p.returncode==0 and not errors else 'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':elapsed,'helper':{'file':str(HELPER),'sha256':hp},'helper_sha256_before':hp,'helper_sha256_after':sha(HELPER),'runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'canonical_owner_source_selection_or_publication_mutated':False}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'actual_record':str(OUT),'sha256':sha(OUT),'status':d['status'],'actual_exit_code':p.returncode,'elapsed_seconds':elapsed,'raw_log_sha256':sha(LOG),'protection_errors':errors}))
raise SystemExit(p.returncode if p.returncode else int(bool(errors)))
