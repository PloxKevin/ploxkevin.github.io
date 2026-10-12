"""Copy the explicitly referenced fresh browser27 originals into the publication checkout."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
def safe(base,n):
 assert type(n) is str and n and not Path(n).is_absolute() and '..' not in Path(n).parts and str(Path(n))==n
 p=base/n;assert p.resolve().is_relative_to(base.resolve()) and not p.is_symlink();return p
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads(safe(ROOT,n).read_bytes())
result='reports/full-coverage/publication27-browser-original-copy-v1.json';assert not (ROOT/result).exists()
b=read('reports/full-coverage/browser-checkpoint-27.json');i=read('reports/full-coverage/browser-corrections-27-inputs.json')
assert b['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and b['coverage_complete'] is False
r=i['actual_execution'];assert r=={'file':b['actual_execution'],'sha256':b['actual_execution_sha256']} and sha(safe(ROOT,r['file']))==r['sha256']
d=read(r['file']);assert type(d['actual_exit_code']) is int and d['actual_exit_code']==0
assert d['actual_command']==['node','qa/learning_review.mjs','--report','reports/full-coverage/browser-source55-27-v1.json','--artifacts','reports/full-coverage/browser-artifacts-source55-27-v1','lyapunov-mpc.html','verification.html']
assert d['actual_workdir']==str(ROOT) and d['source_sha256_before']==d['source_sha256_after']==b['source_sha256']
assert d['qa_source_sha256']==b['qa_source_sha256'] and len(d['source_sha256_before'])==31
assert i['fresh_original_report']=={'file':d['report'],'sha256':d['report_sha256']}
files={r['file']:r['sha256'],d['report']:d['report_sha256'],d['log']:d['log_sha256']}
rows=[r for r in i['screenshot_aliases'] if r['evidence_mode']=='fresh_actual_source55_browser_execution'];assert len(rows)==4
for r in rows:
 assert r['original'].startswith('reports/full-coverage/browser-artifacts-source55-27-v1/') and sha(safe(ROOT,r['file']))==r['sha256']
 files[r['original']]=r['sha256']
assert len(files)==7
for n,h in files.items():assert sha(safe(ROOT,n))==h
for n,h in files.items():
 p=safe(PUB,n);p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(ROOT,n),p);assert sha(p)==h
report={'status':'passed_exact_explicit_fresh_browser27_original_byte_copies','copied_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(Path(__file__)),'copied_files_sha256':files,'coverage_complete':False,'pages_or_live_delivery_claimed':False}
with (ROOT/result).open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'passed','copied_original_paths':len(files)}))
