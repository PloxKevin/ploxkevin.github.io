from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/prepare-modules-leaky-convexity-source63-proposal28-v1.py');O=Path('/tmp/modules-leaky-convexity-source63-preparation28-actual-v1.json');L=O.with_suffix('.log');assert not O.exists()and not L.exists();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=json.loads((R/'reports/full-coverage/checkpoint-28-selection.json').read_bytes());pins={n:v['sha256']for n,v in s['proof_files'].items()}
for p in (R/'SafeLearning').glob('*'):
 if p.is_file()and p.suffix in {'.html','.css','.js'}:pins[str(p.relative_to(R))]=sha(p)
for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/inventory_claims.py','reports/full-coverage/checkpoint-28-selection.json']+['book/coverage/'+n+'.json'for n in ['core','foundations','applied','applied-promotions','modules']]:pins[n]=sha(R/n)
before={n:sha(R/n)for n in pins};assert before==pins;hp=sha(H);command=['python3',str(H)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb')as f:p=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t;after={n:sha(R/n)for n in pins};errors=[n for n in pins if pins[n]!=after[n]]
d={'status':'passed'if p.returncode==0 and not errors else'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'helper':str(H),'helper_sha256_before':hp,'helper_sha256_after':sha(H),'runner':str(Path(__file__)),'runner_sha256':sha(Path(__file__)),'raw_log':str(L),'raw_log_sha256':sha(L),'protected_selection1186_count':len(s['proof_files']),'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'only_TMP_written':True,'compiler_started':False,'source63_applied':False}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'actual_record':str(O),'sha256':sha(O),'actual_exit_code':p.returncode,'elapsed_seconds':elapsed,'protection_errors':errors,'raw_log_sha256':sha(L)}));raise SystemExit(p.returncode or int(bool(errors)))
