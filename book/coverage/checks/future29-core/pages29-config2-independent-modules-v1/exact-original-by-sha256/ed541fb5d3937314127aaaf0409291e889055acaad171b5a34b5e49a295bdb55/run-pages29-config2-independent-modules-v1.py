from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased')
C=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
H=Path('/tmp/review-pages29-config2-independent-modules-v1.py')
O=Path('/tmp/pages29-config2-independent-modules-actual-v1.json'); L=O.with_suffix('.log')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not O.exists() and not L.exists()
assert sha(C)=='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
c=json.loads(C.read_bytes()); pins={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
assert all(sha(R/n)==h for n,h in pins.items())
before={str(H):sha(H),str(C):sha(C),str(R/'book/coverage/checks/root_prepare_pages29_config_v2.py'):sha(R/'book/coverage/checks/root_prepare_pages29_config_v2.py')}
t=time.monotonic(); started=datetime.now(timezone.utc).isoformat(); command=['python3',str(H)]
p=subprocess.run(command,cwd=R,capture_output=True); L.write_bytes(p.stdout+p.stderr)
after={n:sha(n) for n in before}; errors=[n for n,h in pins.items() if sha(R/n)!=h]
d={'status':'passed' if p.returncode==0 and not errors and before==after else 'failed','actual_command':command,'actual_workdir':str(R),'actual_exit_code':p.returncode,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':after,'log':str(L),'log_sha256':sha(L),'protected_inputs_sha256_before':pins,'protected_inputs_sha256_after':{n:sha(R/n) for n in pins},'protection_errors':errors,'scope':'Independent full code/delta and existing authentic audited29 guard check only; no producer, PUB, source, owner or compiler mutation. Original previous config archived exactly for future stable retrieval.'}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k] for k in ['status','actual_exit_code','elapsed_seconds','protection_errors']}));raise SystemExit(0 if d['status']=='passed' else 1)
