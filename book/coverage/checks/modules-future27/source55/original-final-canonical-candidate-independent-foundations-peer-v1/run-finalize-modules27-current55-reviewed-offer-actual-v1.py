from pathlib import Path
from datetime import datetime,timezone
import os,sys,json,hashlib,time,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'book/coverage/checks/finalize_modules27_current55_reviewed_offer_v1.py';J=R/'book/coverage/checks/modules-future27/source55/modules27-current55-reviewed-offer-finalization-actual-v1.json';L=J.with_suffix('.log');assert not J.exists() and not L.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ);env.pop('PYTHONHOME',None);c=[sys.executable,str(P)];h=sha(P);s=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb') as f:p=subprocess.run(c,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
d={'status':'actual_reviewed_isolated_module27_offer_finalization_completed','actual_command':c,'actual_workdir':str(R),'started_at_utc':s,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_exit_code':p.returncode,'helper_sha256_before':h,'helper_sha256_after':sha(P),'actual_helper':{'file':P.relative_to(R).as_posix(),'sha256':sha(P)},'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(L),'raw_log_sha256':sha(L),'scope':'Distinct reviewed isolated offer and exact original aliases only; no installed owner or mathematical body change.'}
with J.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(p.returncode)
