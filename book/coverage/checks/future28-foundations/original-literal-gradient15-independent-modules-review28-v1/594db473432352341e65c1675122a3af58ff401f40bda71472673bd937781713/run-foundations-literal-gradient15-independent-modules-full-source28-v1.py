from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
CHECKER=Path('/tmp/check-foundations-literal-gradient15-independent-modules-full-source28-v1.py')
ACTUAL=Path('/tmp/foundations-literal-gradient15-independent-modules-full-source28-actual-v1.json')
LOG=ACTUAL.with_suffix('.log')
FINAL=Path('/tmp/foundations-literal-gradient15-independent-modules-full-source-review28-v1.json')
FINDINGS=Path('/tmp/foundations-literal-gradient15-independent-modules-full-source28-findings-v1.json')
assert all(not p.exists() for p in (ACTUAL,LOG,FINAL,FINDINGS))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
before=sha(CHECKER);command=['python3',str(CHECKER)];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
actual={'actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'checker_sha256_before':before,'checker_sha256_after':sha(CHECKER),'actual_runner':ref(Path(__file__)),'raw_log':str(LOG),'raw_log_sha256':sha(LOG)}
ACTUAL.write_text(json.dumps(actual,indent=2)+'\n')
assert actual['checker_sha256_before']==actual['checker_sha256_after']
if r.returncode: print(json.dumps({'actual':ref(ACTUAL),'log':ref(LOG)}));raise SystemExit(r.returncode)
original=json.loads(FINDINGS.read_text());final=dict(original)
final['original_findings']=ref(FINDINGS)
final['entire_original_findings_body_and_time']=original
final['actual_reader_execution']=ref(ACTUAL)
final['actual_reader_raw_log']=ref(LOG)
final['actual_reader_runner']=ref(Path(__file__))
final['closed_evidence_sha256']=dict(original['closed_evidence_sha256'])
for p in (CHECKER,FINDINGS,ACTUAL,LOG,Path(__file__)):final['closed_evidence_sha256'][str(p)]=sha(p)
FINAL.write_text(json.dumps(final,indent=2)+'\n')
print(json.dumps({'peer':ref(FINAL),'actual':ref(ACTUAL),'raw_log':ref(LOG)}))
