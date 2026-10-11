from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
C=BASE/'check-publication24-stage-independent-foundations-v6.py';O=BASE/'publication24-stage-independent-foundations-actual-v6.json';L=O.with_suffix('.log')
assert not O.exists() and not L.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)]
with L.open('xb') as f:a=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L.relative_to(ROOT)),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only independent code checker, explicitly isolated alias/status fixtures; no Root main, PUB copy or Git execution.'}
with O.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
if a.returncode==0:
 obs=BASE/'publication24-stage-independent-observations-v6.json';review=json.loads(obs.read_text());review['actual_independent_code_checker_execution']={'file':str(O.relative_to(ROOT)),'sha256':H(O)}
 old=BASE/'publication24-stage-independent-review-v3.json';prior=json.loads(old.read_text());closed=dict(prior['closed_evidence_sha256']);closed[str(old.relative_to(ROOT))]=H(old)
 for p in [C,O,L,Path(__file__),obs]:closed[str(p.relative_to(ROOT))]=H(p)
 review['closed_evidence_sha256']=closed
 out=BASE/'publication24-stage-independent-review-v4.json';assert not out.exists()
 with out.open('x') as f:f.write(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'review':str(out.relative_to(ROOT)),'sha256':H(out),'actual_exit_code':a.returncode}))
print(O.read_text());raise SystemExit(a.returncode)
