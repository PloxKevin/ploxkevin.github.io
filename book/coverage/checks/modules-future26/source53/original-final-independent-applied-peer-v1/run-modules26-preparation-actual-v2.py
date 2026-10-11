from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,subprocess,time
r=Path('/home/oxrexkevin/SafetyBased')
p=argparse.ArgumentParser();p.add_argument('helper');p.add_argument('record');p.add_argument('kind');p.add_argument('helper_arguments',nargs='*');a=p.parse_args()
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
h=r/a.helper;record=r/a.record;log=record.with_suffix('.log');assert h.is_file() and not record.exists() and not log.exists()
record.parent.mkdir(parents=True,exist_ok=True);before=H(h);command=['python3',a.helper,*a.helper_arguments]
start=datetime.now(timezone.utc);tick=time.monotonic()
with log.open('xb')as out:q=subprocess.run(command,cwd=r,stdout=out,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc);after=H(h)
body={'status':'passed_actual_execution'if q.returncode==0 and before==after else'failed_actual_execution','actual_command':command,'actual_workdir':str(r),'actual_exit_code':q.returncode,'started_at_utc':start.isoformat(),'finished_at_utc':end.isoformat(),'duration_seconds':time.monotonic()-tick,'helper':a.helper,'helper_sha256_before':before,'helper_sha256_after':after,'raw_log':str(log.relative_to(r)),'raw_log_sha256':H(log),'execution_kind':a.kind,'actual_runner':{'file':str(Path(__file__)),'sha256':H(Path(__file__))},'scope':'Genuine helper invocation; the native output supplies its limited execution scope. No production aggregate verification or live owner integration is inferred.'}
record.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps(body));raise SystemExit(q.returncode if before==after else 1)
