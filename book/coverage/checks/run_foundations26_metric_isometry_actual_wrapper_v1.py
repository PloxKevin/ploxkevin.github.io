from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time
ROOT=Path(__file__).resolve().parents[3]
HELPER='book/coverage/checks/run_foundations26_metric_isometry_canonical_pair_v1.py'
RECORD='book/coverage/checks/foundations26-metric-isometry-canonical-pair-execution-v1.json'
LOG='book/coverage/checks/foundations26-metric-isometry-canonical-pair-execution-v1.log'
sha=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
assert not (ROOT/RECORD).exists() and not (ROOT/LOG).exists()
command=['python3',HELPER];before=sha(HELPER);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with (ROOT/LOG).open('xb') as f: result=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed'if result.returncode==0 else'failed','actual_exit_code':result.returncode,'actual_command':command,
 'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':{HELPER:before},'helper_sha256_after':{HELPER:sha(HELPER)},
 'log':LOG,'log_sha256':sha(LOG),'original_actual_runner':Path(__file__).relative_to(ROOT).as_posix(),
 'scope':'Genuine outer execution of two NEW reviewed canonical standalone/named proof pairs, preserving selected25/current52/live owners. No aggregate26, mapping or delivery claim.'}
with (ROOT/RECORD).open('x') as f:json.dump(record,f,indent=2);f.write('\n')
print(json.dumps({'actual_exit_code':result.returncode,'record':RECORD,'raw_log':LOG}))
raise SystemExit(result.returncode)
