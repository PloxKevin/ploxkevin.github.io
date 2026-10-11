from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');helper=Path('/tmp/modules-checkpoint27-production-output-peer-v1.py');record=Path('/tmp/modules-checkpoint27-production-output-actual-v1.json');log=record.with_suffix('.log');result=Path('/tmp/modules-checkpoint27-production-output-check-result-v1.json');out=Path('/tmp/modules-checkpoint27-production-output-independent-confirmation-v1.json')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not record.exists() and not log.exists() and not result.exists() and not out.exists()
command=['python3',str(helper)];start=datetime.now(timezone.utc);tick=time.monotonic();before=H(helper)
with log.open('xb') as f:q=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed_actual_read_only_checkpoint27_production_output_reader' if q.returncode==0 else 'failed_actual_read_only_checkpoint27_production_output_reader','actual_command':command,'actual_workdir':str(R),'actual_exit_code':q.returncode,'started_at_utc':start.isoformat(),'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':H(helper),'raw_log':str(log),'raw_log_sha256':H(log),'actual_runner':{'file':str(Path(__file__)),'sha256':H(Path(__file__))},'scope':'Independent read-only actual selection/content-map and all source/evidence/import/claim closure; no producer/compiler or owner/source writes.'}
with record.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
if q.returncode==0:
 p=json.loads(result.read_bytes());p['actual_independent_execution']={'file':str(record),'sha256':H(record)};p['actual_independent_raw_log']={'file':str(log),'sha256':H(log)};p['checker']={'file':str(helper),'sha256':H(helper)};p['actual_runner']=d['actual_runner'];p['original_check_result']={'file':str(result),'sha256':H(result)}
 p['closed_evidence_sha256']={str(x):H(x) for x in [result,record,log,helper,Path(__file__)]}
 for key in ['selection','selection_plan','original_pending_plan','independent_original_plan_review','actual_selection_execution','actual_selection_raw_log','content_map','baseline26_selection','baseline26_manifest','baseline26_actual_audit','actual_owner27_integration','actual_integration_result','source54_55_actual_application','global_integrity','freezer']:
  x=p[key];p['closed_evidence_sha256'][x['file']]=x['sha256']
 with out.open('x') as f:f.write(json.dumps(p,indent=2)+'\n')
 print(json.dumps({'status':'passed','peer':{'file':str(out),'sha256':H(out)},'actual':{'file':str(record),'sha256':H(record)},'raw_log':{'file':str(log),'sha256':H(log)}}))
else:print(json.dumps(d))
raise SystemExit(q.returncode)
