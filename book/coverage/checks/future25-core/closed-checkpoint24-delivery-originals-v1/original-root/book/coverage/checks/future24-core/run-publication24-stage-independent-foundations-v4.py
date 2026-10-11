from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
C=BASE/'check-publication24-stage-independent-foundations-v4.py';O=BASE/'publication24-stage-independent-foundations-actual-v4.json';L=O.with_suffix('.log')
assert not O.exists() and not L.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)];a=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with L.open('xb') as f:f.write(a.stdout)
with O.open('x') as f:f.write(json.dumps({'actual_exit_code':a.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L.relative_to(ROOT)),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual author-independent read-only code fixture only; synthetic additions object is explicitly a test, no production/live interface/main or mathematical execution.'},indent=2)+'\n')
if a.returncode==0:
 obs=BASE/'publication24-stage-independent-observations-v3.json';review=json.loads(obs.read_text())
 review['original_observations']={'file':str(obs.relative_to(ROOT)),'sha256':H(obs)}
 review['actual_independent_code_checker_execution']={'file':str(O.relative_to(ROOT)),'sha256':H(O)}
 prior=[BASE/'check-publication24-stage-independent-foundations-v1.py',BASE/'run-publication24-stage-independent-foundations-v1.py',BASE/'publication24-stage-independent-foundations-actual-v1.json',BASE/'publication24-stage-independent-foundations-actual-v1.log']
 review['original_reader_failure_retained']={'execution':json.loads(prior[2].read_text()),'reason':'The isolated reader namespace omitted hashlib used by the extracted actual sha function; NEW v2 supplies hashlib/json. Original helper was never executed or changed.'}
 review['closed_evidence_sha256']={str(x.relative_to(ROOT)):H(x)for x in [C,O,L,Path(__file__),obs]+prior+[BASE/'check-publication24-stage-independent-foundations-v2.py',BASE/'run-publication24-stage-independent-foundations-v2.py',BASE/'publication24-stage-independent-foundations-actual-v2.json',BASE/'publication24-stage-independent-foundations-actual-v2.log',BASE/'publication24-stage-independent-observations-v2.json',BASE/'publication24-stage-independent-review-v1.json']}
 out=BASE/'publication24-stage-independent-review-v2.json'
 with out.open('x')as f:f.write(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'review':str(out.relative_to(ROOT)),'sha256':H(out),'actual_exit_code':a.returncode}))
print(a.stdout.decode());print(O.read_text());raise SystemExit(a.returncode)
