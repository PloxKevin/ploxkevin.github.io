from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future25-core';C=BASE/'check-owner25-live-interface-schema-independent-foundations-v2.py';O=BASE/'owner25-live-interface-schema-independent-foundations-actual-v2.json';L=O.with_suffix('.log')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();assert not O.exists()and not L.exists();h=H(C);start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(C)]
with L.open('xb')as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_checker_sha256_before':h,'actual_checker_sha256_after':H(C),'raw_log':str(L.relative_to(ROOT)),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'scope':'Actual code checker; prospective integration/result/global/output-peer records are explicitly synthetic and kept in memory. No real interface/main/plan/install or compiler execution.'}
with O.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
if p.returncode==0:
 report=BASE/'owner25-live-interface-helper-independent-foundations-code-review-v2.json';x=json.loads(report.read_text());x['actual_independent_code_checker_execution']={'file':str(O.relative_to(ROOT)),'sha256':H(O)};support=BASE/'owner25-live-interface-in-memory-fixture-support-v2.py';prior=ROOT/'book/coverage/checks/future24-core/owner24-live-interface-helper-independent-foundations-code-review-v1.json'
 closed={str(q.relative_to(ROOT)):H(q)for q in [C,O,L,Path(__file__),support,prior]};x['closed_evidence_sha256']=closed
 out=BASE/'owner25-live-interface-helper-independent-foundations-final-code-review-v2.json'
 with out.open('x')as f:f.write(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'review':str(out.relative_to(ROOT)),'sha256':H(out),'actual_exit_code':0}))
print(json.dumps(d));raise SystemExit(p.returncode)
