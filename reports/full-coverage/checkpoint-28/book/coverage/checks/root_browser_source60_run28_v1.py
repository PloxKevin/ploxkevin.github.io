"""Run actual current60 browser checks for four changed chapter pages."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,shutil,subprocess,time

ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
STEM='browser-source60-28-v1'
record=REPORTS/(STEM+'-execution.json');log=record.with_suffix('.log')
inputs=REPORTS/(STEM+'-inputs.json');report=REPORTS/(STEM+'.json')
site=REPORTS/'browser-input28-source60/SafeLearning'
artifacts=REPORTS/'browser-artifacts-source60-28-v1'
assert not any(p.exists() for p in [record,log,inputs,report,site,artifacts])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
sources={str(p.relative_to(ROOT)):sha(p) for p in (ROOT/'SafeLearning').iterdir() if p.suffix in ['.html','.css','.js']}
assert len(sources)==31
assert sources['SafeLearning/lyapunov-mpc.html']=='10c4622f7c506642e5efeea37926c88d2785aff1937a1f8f5672072127a569ff'
assert sources['SafeLearning/verification.html']=='2b60f48b0b374ab75902df099a19d28289b1e107ba2e23187c2b1e348f7d52cb'
inventory=sha(ROOT/'book/coverage/inventory.json')
assert inventory==sha(ROOT/'book/coverage/inventory-after-correction60.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
application=json.loads((ROOT/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json').read_bytes())
assert type(application['actual_exit_code']) is int and application['actual_exit_code']==0
assert sha(ROOT/application['log'])==application['log_sha256']
qa={name:sha(ROOT/name) for name in ['qa/learning_review.mjs','qa/book_browser_checks.mjs']}
current_inventory=json.loads((ROOT/'book/coverage/inventory.json').read_bytes())
assert all(sources[n]==h for n,h in current_inventory['source_sha256'].items())
previous=json.loads((ROOT/'reports/full-coverage/browser-checkpoint-27.json').read_bytes())
assert previous['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and previous['qa_source_sha256']==qa
assert {n for n in sources if sources[n]!=previous['source_sha256'][n]}=={'SafeLearning/'+n for n in ['lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html']}
site.mkdir(parents=True)
for name,digest in sources.items():
 shutil.copyfile(ROOT/name,site/Path(name).name)
 assert sha(site/Path(name).name)==digest
inputs.write_text(json.dumps(dict(source_sha256=sources,qa_source_sha256=qa,source_inventory_sha256=inventory,fresh_pages=['lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html'],site=str(site.relative_to(ROOT)),scope='Four current60 changed pages, five widths each. Browser checks are separate from mathematical verification.'),indent=2)+'\n')
command=['node','qa/learning_review.mjs','--report',str(report.relative_to(ROOT)),'--artifacts',str(artifacts.relative_to(ROOT)),'lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html']
environment=os.environ.copy();environment['SAFELEARNING_QA_SITE']=str(site)
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as stream:
 result=subprocess.run(command,cwd=ROOT,env=environment,stdout=stream,stderr=subprocess.STDOUT)
after={n:sha(ROOT/n) for n in sources}
data=json.loads(report.read_bytes()) if report.exists() else []
passed=result.returncode==0 and after==sources and sha(ROOT/'book/coverage/inventory.json')==inventory and qa=={n:sha(ROOT/n) for n in qa} and len(data)==4 and {d['file'] for d in data}=={'lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html'} and all(d['status']=='passed' and not d['errors'] and {v['width'] for v in d['viewports']}=={320,390,768,820,1280} for d in data)
out=dict(status='passed' if passed else 'failed',actual_exit_code=result.returncode,actual_command=command,actual_workdir=str(ROOT),started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-tick,source_sha256_before=sources,source_sha256_after=after,qa_source_sha256=qa,site=str(site.relative_to(ROOT)),log=str(log.relative_to(ROOT)),log_sha256=sha(log),report=str(report.relative_to(ROOT)),report_sha256=sha(report) if report.exists() else None)
with record.open('x') as stream:stream.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],actual_exit_code=result.returncode,elapsed_seconds=out['elapsed_seconds'])))
raise SystemExit(0 if passed else 1)
