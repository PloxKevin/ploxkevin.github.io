from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=Path('/tmp/check-checkpoint29-publication-four-helpers-independent-applied-v4.py')
RECORD=Path('/tmp/checkpoint29-publication-four-helpers-independent-applied-actual-v4.json')
LOG=RECORD.with_suffix('.log')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
assert sha(CONTEXT)==CONTEXT_SHA
context=json.loads(CONTEXT.read_bytes())
guards={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}
def guard():
 assert sha(CONTEXT)==CONTEXT_SHA
 for n,h in guards.items():assert sha(ROOT/n)==h,n
guard()
before={str(HELPER):sha(HELPER),str(Path(__file__)):sha(Path(__file__))}
command=['python3',str(HELPER)]
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as out:process=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
errors=[]
try:guard()
except Exception as e:errors.append(str(e))
after={n:sha(Path(n)) for n in before}
passed=process.returncode==0 and before==after and not errors
result={'status':'passed' if passed else 'failed','actual_exit_code':process.returncode,
 'actual_runner_exit_code':0 if passed else 1,'actual_command':command,'actual_workdir':str(ROOT),
 'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':elapsed,
 'helper_sha256_before':before,'helper_sha256_after':after,'log':str(LOG),'log_sha256':sha(LOG),
 'actual_source65_installed29_context':{'file':str(CONTEXT),'sha256':CONTEXT_SHA},
 'protection_errors':errors,'protected_selected29_proof_sources':1197,
 'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,
 'production_helper_invoked':False,'git_or_publication_mutation':False,
 'scope':'Measured independent full four-helper code/schema read and focused actual pure guard cases. Synthetic schemas and isolated TMP fixtures are not future producer results. No new config2 application, plan3, stager3, kernel, commit, push, Pages workflow or live delivery success is claimed.'}
with RECORD.open('x') as out:out.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'record':str(RECORD),'actual_exit_code':process.returncode,
 'protection_errors':errors}))
raise SystemExit(0 if passed else 1)
