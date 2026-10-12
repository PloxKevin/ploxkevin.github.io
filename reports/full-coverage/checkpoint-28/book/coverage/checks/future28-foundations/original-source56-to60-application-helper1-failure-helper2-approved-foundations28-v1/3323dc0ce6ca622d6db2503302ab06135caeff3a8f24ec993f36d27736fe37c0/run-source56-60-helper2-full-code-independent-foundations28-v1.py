from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CHECKER=Path('/tmp/check-source56-60-helper2-full-code-independent-foundations28-v1.py')
ACTUAL=Path('/tmp/source56-60-helper2-full-code-independent-foundations28-actual-v1.json');LOG=ACTUAL.with_suffix('.log')
FINDINGS=Path('/tmp/source56-60-helper2-full-code-independent-foundations28-findings-v1.json');FINAL=Path('/tmp/source56-60-helper2-full-code-independent-foundations28-v1.json')
assert all(not p.exists() for p in (ACTUAL,LOG,FINDINGS,FINAL))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
command=['python3',str(CHECKER)];before=sha(CHECKER);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
actual={'actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'checker_sha256_before':before,'checker_sha256_after':sha(CHECKER),'actual_runner':ref(Path(__file__)),'raw_log':str(LOG),'raw_log_sha256':sha(LOG)}
with ACTUAL.open('x') as f:json.dump(actual,f,indent=2);f.write('\n')
assert actual['checker_sha256_before']==actual['checker_sha256_after']
if r.returncode:print(json.dumps({'actual':ref(ACTUAL),'raw_log':ref(LOG)}));raise SystemExit(r.returncode)
original=json.loads(FINDINGS.read_text());d=dict(original)
d.update({'original_findings':ref(FINDINGS),'entire_original_findings_body_and_time':original,'actual_reader_execution':ref(ACTUAL),'actual_reader_raw_log':ref(LOG),'actual_reader_runner':ref(Path(__file__))})
d['closed_evidence_sha256']=dict(original['closed_evidence_sha256'])
for p in (CHECKER,FINDINGS,ACTUAL,LOG,Path(__file__)):d['closed_evidence_sha256'][str(p)]=sha(p)
with FINAL.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'peer':ref(FINAL),'actual':ref(ACTUAL),'raw_log':ref(LOG)}))
