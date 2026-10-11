#!/usr/bin/env python3
from pathlib import Path
import datetime,hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
CHECKER=Path('/tmp/check-wall53-full-source-independent-foundations-review27-v1.py')
OUT=Path('/tmp/wall53-full-source-independent-foundations-actual27-v1.json')
LOG=OUT.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists() and not LOG.exists()
start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();before=sha(CHECKER)
cmd=['python3',str(CHECKER)]
r=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True)
LOG.write_text(r.stdout+r.stderr)
d={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':sha(CHECKER),'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'execution_kind':'readonly_independent_byte_literal_and_evidence_review_checker_only_no_Lean_or_producer','compiler_or_owner_mutation_claimed':False}
OUT.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));raise SystemExit(r.returncode)
