from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json')
H=Path('/tmp/review-Core-Applied-promotions30-final-independent-modules-v2.py')
O=Path('/tmp/Core-Applied-promotions30-final-independent-modules-actual-v2.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not O.exists() and not L.exists()
assert sha(C)=='d06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737'
c=json.loads(C.read_bytes());pins={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
assert all(sha(R/n)==h for n,h in pins.items())
before={str(H):sha(H),str(C):sha(C)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();command=['python3',str(H)]
p=subprocess.run(command,cwd=R,capture_output=True);L.write_bytes(p.stdout+p.stderr)
after={n:sha(n) for n in before};errors=[n for n,h in pins.items() if sha(R/n)!=h]
d={'status':'passed' if p.returncode==0 and before==after and not errors else 'failed','actual_command':command,'actual_workdir':str(R),'actual_exit_code':p.returncode,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':after,'raw_log':str(L),'raw_log_sha256':sha(L),'protected_inputs_sha256_before':pins,'protected_inputs_sha256_after':{n:sha(R/n) for n in pins},'protection_errors':errors,'compiler_started':False,'source_owner_and_publication_mutations':False,'scope':'Independent Core/Applied/promotions30 full forward/inverse and owned scope mapping:actualSource79,Core58/Applied24+10,6 actual pairs,all14 exact material decisions and full CoreExercise21; no producer/compiler/live changes.'}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k] for k in ['status','actual_exit_code','elapsed_seconds','protection_errors']}));raise SystemExit(0 if d['status']=='passed' else 1)
