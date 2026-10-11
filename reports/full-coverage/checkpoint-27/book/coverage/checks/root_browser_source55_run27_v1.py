"""Run actual current55 browser checks for both changed chapter pages."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,shutil,subprocess,time

ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
STEM='browser-source55-27-v1'
record=REPORTS/(STEM+'-execution.json');log=record.with_suffix('.log')
inputs=REPORTS/(STEM+'-inputs.json');report=REPORTS/(STEM+'.json')
site=REPORTS/'browser-input27-source55/SafeLearning'
artifacts=REPORTS/'browser-artifacts-source55-27-v1'
assert not any(p.exists() for p in [record,log,inputs,report,site,artifacts])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
sources={str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'SafeLearning').iterdir() if p.suffix in ['.html','.css','.js']}
assert len(sources)==31
assert sources['SafeLearning/lyapunov-mpc.html']=='63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f'
assert sources['SafeLearning/verification.html']=='d01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53'
inventory=sha(ROOT/'book/coverage/inventory.json')
assert inventory==sha(ROOT/'book/coverage/inventory-after-correction55.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
application=json.loads((ROOT/'reports/full-coverage/source54-55-corrections-application-execution-v1.json').read_bytes())
assert type(application['actual_exit_code']) is int and application['actual_exit_code']==0
assert sha(ROOT/application['log'])==application['log_sha256']
qa={name:sha(ROOT/name) for name in ['qa/learning_review.mjs','qa/book_browser_checks.mjs']}
site.mkdir(parents=True)
for name,digest in sources.items():
 shutil.copyfile(ROOT/name,site/Path(name).name)
 assert sha(site/Path(name).name)==digest
inputs.write_text(json.dumps(dict(source_sha256=sources,qa_source_sha256=qa,source_inventory_sha256=inventory,fresh_pages=['lyapunov-mpc.html','verification.html'],site=str(site.relative_to(ROOT)),scope='Both current55 changed pages, five widths each. Browser checks are separate from mathematical verification.'),indent=2)+'\n')
command=['node','qa/learning_review.mjs','--report',str(report.relative_to(ROOT)),'--artifacts',str(artifacts.relative_to(ROOT)),'lyapunov-mpc.html','verification.html']
environment=os.environ.copy();environment['SAFELEARNING_QA_SITE']=str(site)
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as stream:
 result=subprocess.run(command,cwd=ROOT,env=environment,stdout=stream,stderr=subprocess.STDOUT)
after={n:sha(ROOT/n) for n in sources}
data=json.loads(report.read_bytes()) if report.exists() else []
passed=result.returncode==0 and after==sources and qa=={n:sha(ROOT/n) for n in qa} and len(data)==2 and {d['file'] for d in data}=={'lyapunov-mpc.html','verification.html'} and all(d['status']=='passed' and not d['errors'] and {v['width'] for v in d['viewports']}=={320,390,768,820,1280} for d in data)
out=dict(status='passed' if passed else 'failed',actual_exit_code=result.returncode,actual_command=command,actual_workdir=str(ROOT),started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-tick,source_sha256_before=sources,source_sha256_after=after,qa_source_sha256=qa,site=str(site.relative_to(ROOT)),log=str(log.relative_to(ROOT)),log_sha256=sha(log),report=str(report.relative_to(ROOT)),report_sha256=sha(report) if report.exists() else None)
with record.open('x') as stream:stream.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],actual_exit_code=result.returncode,elapsed_seconds=out['elapsed_seconds'])))
raise SystemExit(0 if passed else 1)
