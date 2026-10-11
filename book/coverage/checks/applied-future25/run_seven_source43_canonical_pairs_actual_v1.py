from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time
r=Path('/home/oxrexkevin/SafetyBased');b=r/'book/coverage/checks/applied-future25';h=b/'run_seven_source43_canonical_pairs_v1.py';p=b/'seven-source43-canonical-pairs-actual-v1';H=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert not p.with_suffix('.json').exists() and not p.with_suffix('.log').exists()
cmd=['python3',str(h.relative_to(r))];before=H(h);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with p.with_suffix('.log').open('wb') as f:a=subprocess.run(cmd,cwd=r,stdout=f,stderr=subprocess.STDOUT)
x={'status':'passed' if a.returncode==0 else 'failed','actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(r),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':H(h),'log':str(p.with_suffix('.log').relative_to(r)),'log_sha256':H(p.with_suffix('.log')),'actual_runner':str(Path(__file__).relative_to(r)),'actual_runner_sha256':H(Path(__file__)),'scope':'Seven unique future25 canonical standalone/named pairs, with individual genuine native records. No aggregate, selection or live coverage claim.'}
p.with_suffix('.json').write_text(json.dumps(x,indent=2)+'\n');print(p.with_suffix('.log').read_text()[-8000:]);print(str(p.with_suffix('.json').relative_to(r)),H(p.with_suffix('.json')));raise SystemExit(a.returncode)
