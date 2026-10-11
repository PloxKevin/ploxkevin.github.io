from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');checker=Path('/tmp/check-pages27-config3-independent-modules-v1.py');record=Path('/tmp/pages27-config3-independent-modules-actual-v1.json');log=record.with_suffix('.log');result=Path('/tmp/pages27-config3-independent-modules-check-result-v1.json');peer=Path('/tmp/pages27-config3-independent-modules-confirmation-v1.json');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not record.exists() and not log.exists() and not result.exists() and not peer.exists();start=datetime.now(timezone.utc);tick=time.monotonic();before=H(checker);command=['python3',str(checker)]
with log.open('xb') as f:q=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed_actual_independent_pages27_config3_code_fixture_reader' if q.returncode==0 else 'failed_actual_independent_pages27_config3_code_fixture_reader','actual_command':command,'actual_workdir':str(R),'actual_exit_code':q.returncode,'started_at_utc':start.isoformat(),'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':H(checker),'raw_log':str(log),'raw_log_sha256':H(log),'actual_runner':{'file':str(Path(__file__)),'sha256':H(Path(__file__))},'scope':'Independent code/native historical bytes and explicitly isolated synthetic future27 fixture checks; no actual future27 producer execution.'};record.write_text(json.dumps(d,indent=2)+'\n')
if q.returncode==0:
 p=json.loads(result.read_bytes());p['actual_independent_execution']={'file':str(record),'sha256':H(record)};p['checker']={'file':str(checker),'sha256':H(checker)};p['actual_runner']=d['actual_runner'];p['actual_independent_raw_log']={'file':str(log),'sha256':H(log)};p['original_check_result']={'file':str(result),'sha256':H(result)}
 for x in [record,log,checker,Path(__file__),result]:p['closed_evidence_sha256'][str(x)]=H(x)
 peer.write_text(json.dumps(p,indent=2)+'\n');print(json.dumps({'status':'passed','peer':str(peer),'sha256':H(peer),'actual':H(record),'raw':H(log)}))
else:print(json.dumps(d))
raise SystemExit(q.returncode)
