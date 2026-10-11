from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future25-core';C=BASE/'check-owner25-integration-and-binding-independent-foundations-v1.py';O=BASE/'owner25-integration-and-binding-independent-foundations-actual-v1.json';L=O.with_suffix('.log')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();assert not O.exists()and not L.exists();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)]
with L.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L.relative_to(ROOT)),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Genuine author-independent read-only code/native-schema and isolated synthetic fixtures only; no Root main, dry/apply, production binding or integration.'}
with O.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
if p.returncode==0:
 obs=BASE/'owner25-integration-and-binding-independent-foundations-observations-v1.json';review=json.loads(obs.read_text());review['actual_independent_checker_execution']={'file':str(O.relative_to(ROOT)),'sha256':H(O)};review['closed_evidence_sha256']={str(p.relative_to(ROOT)):H(p)for p in [C,O,L,Path(__file__),obs]}
 out=BASE/'owner25-integration-and-binding-helpers-independent-foundations-code-review-v1.json'
 with out.open('x')as f:f.write(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'peer':str(out.relative_to(ROOT)),'sha256':H(out),'actual_exit_code':0}))
print(json.dumps(d));raise SystemExit(p.returncode)
