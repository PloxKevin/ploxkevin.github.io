from pathlib import Path
from datetime import datetime,timezone
import os,json,hashlib,shutil,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');D=R/'reports/full-coverage';site=D/'browser-input-19-source44/SafeLearning';site.mkdir(parents=True,exist_ok=False)
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source={}
for p in sorted((R/'SafeLearning').iterdir()):
 if p.suffix in {'.html','.css','.js'}:shutil.copy2(p,site/p.name);assert H(p)==H(site/p.name);source['SafeLearning/'+p.name]=H(p)
command=['node','qa/learning_review.mjs','--report','reports/full-coverage/browser-source44-19-v1.json','--artifacts','reports/full-coverage/browser-artifacts-source44-19-v1']
env=os.environ.copy();env['SAFELEARNING_QA_SITE']=str(site)
log=D/'browser-source44-19-v1.log';assert not log.exists();started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('w') as f:run=subprocess.run(command,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
report=D/'browser-source44-19-v1.json'
out=dict(status='passed' if run.returncode==0 else 'failed',actual_exit_code=run.returncode,command=command,actual_workdir=str(R),environment={'SAFELEARNING_QA_SITE':str(site)},started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-t,source_sha256=source,log=str(log.relative_to(R)),log_sha256=H(log),report=str(report.relative_to(R)),report_sha256=H(report),qa_source_sha256={str(p.relative_to(R)):H(p) for p in [R/'qa/learning_review.mjs',R/'qa/book_browser_checks.mjs']},scope='Actual all29-page five-width reader execution on immutable source44 site copies; screenshot existence does not assert manual visual inspection.')
p=D/'browser-source44-19-v1-execution.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'actual_exit_code':run.returncode,'report':str(report.relative_to(R))}));raise SystemExit(run.returncode)
