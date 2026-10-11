from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/finalize-foundations28-current60-offer-v1.py')
O=Path('/tmp/foundations28-current60-offer-finalization-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists()and not L.exists()
pins=json.loads((R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json').read_bytes())['protected_inputs_sha256']
before={n:sha(R/n)for n in pins};assert before==pins
hp=sha(H);command=['python3',str(H)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb')as f:p=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t;after={n:sha(R/n)for n in pins};errors=[n for n,h in pins.items()if after[n]!=h]
d={'status':'passed'if p.returncode==0 and not errors else'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'helper':{'file':str(H),'sha256':hp},'helper_sha256_before':hp,'helper_sha256_after':sha(H),'runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(L),'raw_log_sha256':sha(L),'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'canonical_owner_source_selection_or_publication_mutated':False}
with O.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'actual_record':str(O),'sha256':sha(O),'actual_exit_code':p.returncode,'status':d['status'],'elapsed_seconds':elapsed,'protection_errors':errors,'raw_log_sha256':sha(L)}))
raise SystemExit(p.returncode or int(bool(errors)))
