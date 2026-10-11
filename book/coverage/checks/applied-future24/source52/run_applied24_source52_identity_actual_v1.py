from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/checks/applied-future24/prepare_applied24_source52_identity_candidate_v1.py'
PIN='cda199363e0904ba4efecfce3cf725417f2976e99b2611422c8680be8196c476'
BASE=ROOT/'book/coverage/checks/applied-future24/source52'
BASE.mkdir(parents=True,exist_ok=True)
OUT=BASE/'applied24-source52-isolated-identity-actual-v1.json'
LOG=OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(ROOT/HELPER)==PIN
cmd=['python3',HELPER,'--inventory-sha256','38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3','--root-authorized-source52-identity-rebase']
start=datetime.now(timezone.utc);t=time.monotonic()
with LOG.open('xb') as f:p=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc)
d={'status':'passed' if p.returncode==0 else 'failed','actual_exit_code':p.returncode,'command':cmd,'actual_workdir':str(ROOT),
 'helper_sha256_before':PIN,'helper_sha256_after':sha(ROOT/HELPER),'log':str(LOG.relative_to(ROOT)),
 'log_sha256':sha(LOG),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(__file__),
 'started_at_utc':start.isoformat(),'finished_at_utc':finish.isoformat(),'elapsed_seconds':time.monotonic()-t,
 'scope':'Actual isolated identity-only preparation after authoritative Root source52 apply0. No new proof, mathematical review, live owner copy, global24 or aggregate execution.'}
with OUT.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'actual_record':str(OUT.relative_to(ROOT)),'sha256':sha(OUT),'raw_log':str(LOG.relative_to(ROOT)),'raw_log_sha256':sha(LOG)}))
raise SystemExit(p.returncode)
