from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-publication26-delivery-updater-independent-applied-v4.py');record=Path('/tmp/publication26-delivery-updater-independent-applied-actual-v4.json');log=record.with_suffix('.log');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not record.exists() and not log.exists();start=datetime.now(timezone.utc).isoformat();t=time.monotonic();h=H(checker)
with log.open('xb')as f:p=subprocess.run(['python3',str(checker)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t;assert H(checker)==h
record.write_text(json.dumps({'status':'actual_read_only_independent_updater4_checker_execution','actual_exit_code':p.returncode,'actual_command':['python3',str(checker)],'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'checker_sha256_before':h,'checker_sha256_after':H(checker),'log':str(log),'log_sha256':H(log),'scope':'Measured independent isolated native guard checker only; excludes updater producer and every progress/README/backup/output/PUB/Git/owner mutation.'},indent=2)+'\n')
print(json.dumps({'actual_exit_code':p.returncode,'actual':str(record),'actual_sha256':H(record),'log':str(log),'log_sha256':H(log),'elapsed_seconds':elapsed}));raise SystemExit(p.returncode)
