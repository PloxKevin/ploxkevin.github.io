"""Record one genuine isolated Module27 builder execution after actual pairs0."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time,os
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/build_modules27_candidate_current55_v2.py'
EXPECTED='1b97d374a56568996a1efb7ee83949eeaa4504aa323de1ec6548320846d63382'
RECORD=ROOT/'reports/full-coverage/modules27-current55-isolated-candidate-builder-execution-v1.json'
LOG=RECORD.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ROOT/HELPER)==EXPECTED and not RECORD.exists() and not LOG.exists()
command=['python3',HELPER,'--pair-execution','reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json']
environment=dict(os.environ);environment.pop('PYTHONHOME',None)
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as stream:
    actual=subprocess.run(command,cwd=ROOT,env=environment,stdout=stream,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after=sha(ROOT/HELPER)
body={'status':'passed_actual_isolated_candidate_preparation' if actual.returncode==0 and after==EXPECTED else 'failed_actual_isolated_candidate_preparation','actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'actual_exit_code':actual.returncode,'helper_sha256_before':{HELPER:EXPECTED},'helper_sha256_after':{HELPER:after},'log':LOG.relative_to(ROOT).as_posix(),'log_sha256':sha(LOG),'actual_runner':{'file':Path(__file__).resolve().relative_to(ROOT).as_posix(),'sha256':sha(Path(__file__))},'environment_normalization':'Only removed unrelated inherited PYTHONHOME from child process.','scope':'Genuine isolated candidate preparation only; no installed owner write or mathematical re-review, compilation, selection or aggregate claim.'}
with RECORD.open('x') as stream:stream.write(json.dumps(body,indent=2)+'\n')
print(json.dumps(body));raise SystemExit(0 if actual.returncode==0 and after==EXPECTED else 1)
