from pathlib import Path
from datetime import datetime,timezone
import subprocess,sys,time,json,hashlib
checker=Path(sys.argv[1]);stem=Path(sys.argv[2]);log=stem.with_suffix('.log');record=stem.with_suffix('.json')
assert checker.is_file() and checker.is_absolute() and not log.exists() and not record.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
command=[sys.executable,str(checker)];before=H(checker);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as raw:p=subprocess.run(command,cwd='/home/oxrexkevin/SafetyBased',stdout=raw,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc).isoformat();assert H(checker)==before
body={'status':'passed' if p.returncode==0 else 'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':time.monotonic()-tick,'checker':str(checker),'checker_sha256_before':before,'checker_sha256_after':H(checker),'raw_log':str(log),'raw_log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'execution_kind':'actual_independent_read_only_Pages_configuration_checker_or_isolated_guard_runner','scope':'Measured independent read-only code/guard or produced-output checker command only. No Root configuration helper, compiler, owner installation, Pages build or deployment executed by this runner.'}
record.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps({'record':str(record),'sha256':H(record),'actual_exit_code':p.returncode,'raw_log_sha256':H(log)}));sys.exit(p.returncode)
