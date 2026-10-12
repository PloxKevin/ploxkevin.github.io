from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
H=Path('/tmp/review-foundations-logcube13-independent-modules31-v1.py')
O=Path('/tmp/foundations-logcube13-independent-modules31-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not O.exists()and not L.exists()
assert sha(C)=='73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
c=json.loads(C.read_bytes());pins={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
assert all(sha(R/n)==h for n,h in pins.items())
before={str(H):sha(H),str(C):sha(C)};started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(H)]
p=subprocess.run(command,cwd=R,capture_output=True);L.write_bytes(p.stdout+p.stderr)
after={n:sha(n)for n in before};errors=[n for n,h in pins.items()if sha(R/n)!=h]
d={'status':'passed'if p.returncode==0 and before==after and not errors else'failed','actual_command':command,'actual_workdir':str(R),'actual_exit_code':p.returncode,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':after,'raw_log':str(L),'raw_log_sha256':sha(L),'protected_inputs_sha256_before':pins,'protected_inputs_sha256_after':{n:sha(R/n)for n in pins},'protection_errors':errors,'compiler_started':False,'source_owner_and_publication_mutations':False,'scope':'Independent full13 LogCube source, entire current1306 literal and pending row, exact crossover/finite-point limitation and complete selected/used-primary proof chains.'}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k]for k in ['status','actual_exit_code','elapsed_seconds','protection_errors']}));raise SystemExit(0 if d['status']=='passed'else 1)
