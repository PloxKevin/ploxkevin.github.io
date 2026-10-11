"""Measured actual preparation or canonical-pair execution; records each step once."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future25/material-batch1';BASE.mkdir(parents=True,exist_ok=True)
step=sys.argv[1];assert step in ['prepare','pairs']
name={'prepare':'prepare_foundations25_grid_and_calculus_originals_v1.py','pairs':'run_foundations25_grid_and_calculus_canonical_pairs_v1.py'}[step]
helper=ROOT/'book/coverage/checks'/name
OUT=BASE/('two-source31-export-'+step+'-actual-execution-v1.json');LOG=OUT.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists() and not LOG.exists()
cmd=['python3',helper.relative_to(ROOT).as_posix()];before=sha(helper)
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:actual=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if actual.returncode==0 else 'failed','actual_exit_code':actual.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),
   'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
   'helper':helper.relative_to(ROOT).as_posix(),'helper_sha256_before':before,'helper_sha256_after':sha(helper),
   'log':LOG.relative_to(ROOT).as_posix(),'log_sha256':sha(LOG),
   'actual_runner':Path(__file__).relative_to(ROOT).as_posix(),'actual_runner_sha256':sha(Path(__file__)),
   'execution_kind':('actual_exact_source_and_history_copy_preparation_without_compiler_command' if step=='prepare' else 'actual_source_exact_canonical_compiler_pair_helper'),
   'scope':'Distinct future25 only; installed24 owners, current52 assets/inventory and selected/frozen24 inputs held exact. No live25 integration or aggregate25 inferred.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d))
raise SystemExit(actual.returncode)
