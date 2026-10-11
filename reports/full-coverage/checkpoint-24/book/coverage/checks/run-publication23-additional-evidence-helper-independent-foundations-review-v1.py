from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
checker=Path('/tmp/publication23-additional-evidence-helper-independent-foundations-check-v1.py')
prefix=Path('/tmp/publication23-additional-evidence-helper-independent-foundations-actual-v1')
record=prefix.with_suffix('.json');log=prefix.with_suffix('.log')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not record.exists() and not log.exists()
cmd=['python',str(checker)];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();before=H(checker)
with log.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
out={'kind':'actual_independent_read_only_source_and_evidence_checker','actual_command':cmd,'actual_workdir':str(ROOT),
     'actual_exit_code':r.returncode,'actual_checker':str(checker),'actual_checker_sha256':before,'actual_checker_sha256_after':H(checker),
     'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(__file__),'started_at_utc':start,'finished_at_utc':finish,
     'elapsed_seconds':elapsed,'raw_log':str(log),'raw_log_sha256':H(log),
     'scope':'TMP-only genuine source/literal/evidence reader; no compiler/named/coverage execution inferred.'}
record.write_text(json.dumps(out,indent=2)+'\n');print(log.read_text());print(json.dumps(out));raise SystemExit(r.returncode)
