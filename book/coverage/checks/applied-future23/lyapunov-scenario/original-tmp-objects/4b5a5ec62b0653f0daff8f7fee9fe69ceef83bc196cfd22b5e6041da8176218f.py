from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib
helper=Path('/tmp/prepare-lyapunov-scenario-precision-proposal23-v1.py');stem=Path('/tmp/applied-lyapunov-scenario-precision-proposal23-preparation-execution-v1')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
started=datetime.now(timezone.utc).isoformat();proc=subprocess.run(['python',str(helper)],cwd='/home/oxrexkevin/SafetyBased',stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
completed=datetime.now(timezone.utc).isoformat();log=Path(str(stem)+'.log');assert not log.exists();log.write_bytes(proc.stdout)
record={'status':'actual_read_only_proposal_preparation_execution','actual_command':['python',str(helper)],'cwd':'/home/oxrexkevin/SafetyBased','started_at':started,'completed_at':completed,'actual_exit_code':proc.returncode,'helper_file':str(helper),'helper_sha256':h(helper),'raw_log_file':str(log),'raw_log_sha256':h(log),'runner_file':str(Path(__file__)),'runner_sha256':h(Path(__file__)),'no_working_source_ledger_or_inventory_mutation':True}
p=Path(str(stem)+'.json');assert not p.exists();p.write_text(json.dumps(record,indent=2)+'\n');print(proc.stdout.decode(),end='');print(json.dumps(record));raise SystemExit(proc.returncode)
