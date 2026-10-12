from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CHECKER=Path('/tmp/check-pages27-supplemental-archives3-actual-output-independent-modules-v1.py')
ACTUAL=Path('/tmp/pages27-supplemental-archives3-independent-modules-output-actual-v1.json');LOG=ACTUAL.with_suffix('.log')
FINDINGS=Path('/tmp/pages27-supplemental-archives3-actual-output-independent-modules-findings-v1.json')
PEER=Path('/tmp/pages27-supplemental-archives3-actual-output-independent-modules-review-v1.json')
assert all(not p.exists()for p in (ACTUAL,LOG,FINDINGS,PEER))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
before=sha(CHECKER);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['python3',str(CHECKER)]
with LOG.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(CHECKER),'actual_runner':ref(Path(__file__)),'raw_log':str(LOG),'raw_log_sha256':sha(LOG)}
ACTUAL.write_text(json.dumps(d,indent=2)+'\n')
if r.returncode:print(json.dumps({'actual':ref(ACTUAL),'log':ref(LOG)}));raise SystemExit(r.returncode)
j=json.loads(FINDINGS.read_text());out=dict(j);out['entire_original_reader_findings_and_time']=j;out['actual_independent_reader_execution']=ref(ACTUAL);out['actual_independent_checker']=ref(CHECKER);out['actual_independent_reader_runner']=ref(Path(__file__));out['actual_independent_reader_raw_log']=ref(LOG);out['closed_evidence_sha256']=dict(j['closed_evidence_sha256'])
for p in (CHECKER,Path(__file__),ACTUAL,LOG,FINDINGS):out['closed_evidence_sha256'][str(p)]=sha(p)
PEER.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(PEER),'actual':ref(ACTUAL)}))
