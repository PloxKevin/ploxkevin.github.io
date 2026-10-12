"""Check final checkpoint28 index and add its original native staging records."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,importlib.util
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_finish_publication28_staging_v1.py'
REPORT='reports/full-coverage/publication28-final-content-index-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
def git(a,data=None,check=True):return subprocess.run(['git',*a],cwd=PUB,input=data,capture_output=True,check=check)
spec=importlib.util.spec_from_file_location('exact28stage',ROOT/'book/coverage/checks/root_stage_publication28_v6.py')
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
assert sha(ROOT/'book/coverage/checks/root_stage_publication28_v6.py')=='68e80bf6b9259e18e2813e5b64bd9b60ba8add4168a198b9d9bffd3a3f31431f'
d=read('reports/full-coverage/publication28-staged-byte-check-v1.json')
assert d['status']=='passed_exact_audited_checkpoint28_staged_bytes' and d['coverage_complete'] is False
assert git(['rev-parse','HEAD']).stdout.decode().strip()==d['baseline_head']=='8fa808699674d13e4297d226ef1530a7ec744ad0'
base={**d['staged_paths_sha256'],'reports/full-coverage/publication28-staged-byte-check-v1.json':sha(ROOT/'reports/full-coverage/publication28-staged-byte-check-v1.json')}
extras={SELF:sha(ROOT/SELF)}
for stem,command in [
 ('prepare-publication28-stage-plan-execution-v1',['python3','book/coverage/checks/root_prepare_publication28_stage_plan_v1.py']),
 ('stage-publication28-execution-v1',['python3','book/coverage/checks/root_stage_publication28_v6.py','--plan',d['plan']['file'],'--plan-sha256',d['plan']['sha256'],'--apply'])]:
 n='reports/full-coverage/'+stem+'.json';r=read(n)
 assert r['status']=='passed' and type(r['actual_exit_code']) is int and r['actual_exit_code']==0
 assert r['actual_command']==command and r['actual_workdir']==str(ROOT)
 assert r['helper_sha256_before']==r['helper_sha256_after']=={command[1]:sha(ROOT/command[1])}
 assert sha(ROOT/r['log'])==r['log_sha256']
 extras[n]=sha(ROOT/n);extras[r['log']]=r['log_sha256']
for n,h in base.items():assert sha(s.safe(PUB,n))==h
assert not git(['diff','--name-only','-z']).stdout
before={x.decode() for x in git(['diff','--cached','--name-only','-z']).stdout.split(b'\0') if x}
assert before==set(base)
for n,h in extras.items():
 p=s.safe(PUB,n);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s.safe(ROOT,n).read_bytes());assert sha(p)==h
record={'status':'passed_exact_checkpoint28_final_content_index','checked_at_utc':datetime.now(timezone.utc).isoformat(),
 'original_staging_report':{'file':'reports/full-coverage/publication28-staged-byte-check-v1.json','sha256':base['reports/full-coverage/publication28-staged-byte-check-v1.json']},
 'additional_native_records_sha256':extras,'coverage_complete':False,'content_commit_push_pages_live_pending':True}
b=(json.dumps(record,indent=2)+'\n').encode();assert s.website_size()+len(b)<850000000
for root in [ROOT,PUB]:
 with s.safe(root,REPORT).open('xb') as f:f.write(b)
expected={**base,**extras,REPORT:sha(ROOT/REPORT)}
git(['add','-f','--pathspec-from-file=-','--pathspec-file-nul'],b'\0'.join(n.encode() for n in sorted({*extras,REPORT}))+b'\0')
names={x.decode() for x in git(['diff','--cached','--name-only','-z']).stdout.split(b'\0') if x};assert names==set(expected)
for row in git(['status','--porcelain','-z','--untracked-files=all']).stdout.decode().split('\0'):
 if row:assert row[:2] in ('M ','A ') and row[3:] in names
entries={}
for row in git(['ls-files','--stage','-z']).stdout.split(b'\0'):
 if row:
  header,n=row.split(b'\t',1);mode,oid,stage=header.split();assert stage==b'0';entries[n.decode()]=(mode,oid)
ordered=sorted(names);oids=git(['hash-object','--stdin-paths','--no-filters'],''.join(str(s.safe(PUB,n))+'\n' for n in ordered).encode()).stdout.splitlines()
assert len(oids)==len(ordered) and all(entries[n][0] in (b'100644',b'100755') and entries[n][1]==oid for n,oid in zip(ordered,oids))
assert all(sha(s.safe(PUB,n))==h for n,h in expected.items())
git(['diff','--cached','--check','--','.',*[':(literal,exclude)'+n for n in sorted(d['exact_original_archival_whitespace'])]])
manifest=read('reports/full-coverage/checkpoint-28-manifest.json')
for n,h in manifest['working_inputs_sha256'].items():
 if n.startswith(('SafeLearning/','verification/lean/')) or n in {'book/coverage/'+v+'.json' for v in ['core','foundations','applied','modules','applied-promotions']}:
  assert sha(s.safe(ROOT,n))==h
print(json.dumps({'status':record['status'],'staged_paths':len(names),'coverage_complete':False}))
