from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-foundations-source64-independent-applied29-v1.py');actual=Path('/tmp/foundations-source64-independent-applied-actual29-v1.json');log=actual.with_suffix('.log')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not actual.exists() and not log.exists();before=sha(checker);start=datetime.now(timezone.utc).isoformat();tick=time.perf_counter()
with log.open('xb') as f:r=subprocess.run(['python3',str(checker)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
a={'status':'passed_actual_independent_source64_readonly_parser_review' if r.returncode==0 else 'failed_actual_independent_source64_readonly_parser_review','actual_exit_code':r.returncode,'actual_command':['python3',str(checker)],'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.perf_counter()-tick,'helper_sha256_before':{str(checker):before},'helper_sha256_after':{str(checker):sha(checker)},'raw_log':str(log),'raw_log_sha256':sha(log),'compiler_or_live_mutation':False}
actual.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({'status':a['status'],'actual_exit_code':r.returncode,'actual':str(actual),'actual_sha256':sha(actual)}));raise SystemExit(r.returncode)
