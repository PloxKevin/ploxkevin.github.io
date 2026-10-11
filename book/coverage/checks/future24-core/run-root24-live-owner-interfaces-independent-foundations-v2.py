from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
C=BASE/'check-root24-live-owner-interfaces-independent-foundations-v2.py';O=BASE/'root24-live-owner-interfaces-independent-foundations-actual-v2.json';L=O.with_suffix('.log')
assert not O.exists() and not L.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)]
a=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with L.open('xb') as f:f.write(a.stdout)
with O.open('x') as f:f.write(json.dumps({'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L.relative_to(ROOT)),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual read-only independent output checker; no production interface writer, selection, compilation or Pages execution.'},indent=2)+'\n')
if a.returncode==0:
 obs=BASE/'root24-live-owner-interfaces-independent-foundations-observations-v2.json';review=json.loads(obs.read_text())
 review['original_observations']={'file':str(obs.relative_to(ROOT)),'sha256':H(obs)}
 review['actual_independent_checker_execution']={'file':str(O.relative_to(ROOT)),'sha256':H(O)}
 prior=[BASE/'check-root24-live-owner-interfaces-independent-foundations-v1.py',BASE/'run-root24-live-owner-interfaces-independent-foundations-v1.py',BASE/'root24-live-owner-interfaces-independent-foundations-actual-v1.json',BASE/'root24-live-owner-interfaces-independent-foundations-actual-v1.log']
 review['original_checker_failure_retained']={'execution':json.loads(prior[2].read_text()),'reason':'Reader required every assigned changed field to differ; assigned hash fields legitimately remain equal because candidate and installed bytes are exact. Corrected reader checks no unrecorded differences plus exact owner-specific assignment fields. No owner artifact changed.'}
 review['closed_evidence_sha256']={str(x.relative_to(ROOT)):H(x)for x in [C,O,L,Path(__file__),obs]+prior}
 out=BASE/'root24-live-owner-interfaces-independent-foundations-review-v1.json'
 with out.open('x')as f:f.write(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'review':str(out.relative_to(ROOT)),'sha256':H(out),'actual_exit_code':a.returncode}))
print(a.stdout.decode());raise SystemExit(a.returncode)
