from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,sys
root=Path('/home/oxrexkevin/SafetyBased');trial=int(sys.argv[1]);source=Path('/tmp/CompleteLyapunovScenarioContinuousRisk23.lean');stem=Path('/tmp/applied-lyapunov-scenario-continuous-risk23-trial'+str(trial));snapshot=Path(str(stem)+'-source.lean')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not snapshot.exists();snapshot.write_bytes(source.read_bytes());before=h(snapshot);cmd=['lake','env','lean',str(snapshot)]
started=datetime.now(timezone.utc).isoformat();proc=subprocess.run(cmd,cwd=root/'verification/lean',stdout=subprocess.PIPE,stderr=subprocess.STDOUT);completed=datetime.now(timezone.utc).isoformat();log=Path(str(stem)+'.log');assert not log.exists();log.write_bytes(proc.stdout)
r={'status':'actual_standalone_lean_execution','actual_command':cmd,'cwd':str(root/'verification/lean'),'started_at':started,'completed_at':completed,'actual_exit_code':proc.returncode,'source_file':str(snapshot),'source_sha256_before':before,'source_sha256_after':h(snapshot),'working_source_file':str(source),'working_source_sha256_after':h(source),'raw_log_file':str(log),'raw_log_sha256':h(log),'runner_file':str(Path(__file__)),'runner_sha256':h(Path(__file__))};record=Path(str(stem)+'.json');assert not record.exists();record.write_text(json.dumps(r,indent=2)+'\n');print(proc.stdout.decode(),end='');print(json.dumps(r));raise SystemExit(proc.returncode)
