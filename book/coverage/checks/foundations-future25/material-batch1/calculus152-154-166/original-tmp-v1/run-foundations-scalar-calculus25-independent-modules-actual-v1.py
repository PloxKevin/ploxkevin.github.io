import sys,json,hashlib,subprocess,time
from pathlib import Path
from datetime import datetime,timezone
checker=Path(sys.argv[1]);stem=Path(sys.argv[2]);record=stem.with_suffix('.json');log=stem.with_suffix('.log')
assert checker.is_absolute() and str(checker).startswith('/tmp/')
assert not record.exists() and not log.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[sys.executable,str(checker)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic();before=sha(checker)
with log.open('wb') as out:process=subprocess.run(cmd,cwd='/home/oxrexkevin/SafetyBased',stdout=out,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();after=sha(checker);assert before==after
body={'status':'passed' if process.returncode==0 else 'failed','actual_exit_code':process.returncode,'actual_command':cmd,'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':time.monotonic()-t,'checker':str(checker),'checker_sha256_before':before,'checker_sha256_after':after,'raw_log':str(log),'raw_log_sha256':sha(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(Path(__file__)),'execution_kind':'actual_independent_read_only_full_literal_source_correspondence_checker','scope':'A fresh source-correspondence checker, not Lean compilation, named build, owner integration, kernel replay, aggregate verification or publication.'}
record.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps({'record':str(record),'sha256':sha(record),'actual_exit_code':process.returncode,'raw_log_sha256':body['raw_log_sha256']}));sys.exit(process.returncode)
