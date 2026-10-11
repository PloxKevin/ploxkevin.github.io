"""Genuine new-name canonical pair; preserved current22 proof and source guards."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future23/semicontinuity'
TMP=Path('/tmp');NAME='CompleteFoundationsSemicontinuity23'
SOURCE=TMP/'foundations-semicontinuity23-trial2.lean'
DIGEST='280be25369c9cc9b3336d87ada8e5cf4d899cd454da1a4cabcf33725cb612b14'
REQUEST=TMP/'foundations-semicontinuity23-basics1202-1237-full-source-review-request-v1.json'
REQUEST_SHA='430909a23b6ad13222b9e2fc6cd4adadcf5f21676b06863bcb4cd6b9b3ef418a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def write_new(p,x):
 with p.open('x') as f:f.write(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def copy_exact(s,t):
 if t.exists():assert t.read_bytes()==s.read_bytes()
 else:
  with t.open('xb') as f:f.write(s.read_bytes())
 assert sha(t)==sha(s)
assert sha(SOURCE)==DIGEST and sha(REQUEST)==REQUEST_SHA
manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')
protected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/inventory.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}})
def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
guard();BASE.mkdir(parents=True,exist_ok=True);archive=BASE/'original-tmp';archive.mkdir(exist_ok=True)
originals=[TMP/f'foundations-semicontinuity23-trial{n}.{s}' for n in [1,2] for s in ['lean','json','log']]
originals.extend([REQUEST,TMP/'run-foundations-semicontinuity23-trial-v1.py',TMP/'prepare-foundations-semicontinuity23-source-review-request-v1.py'])
copies={}
for original in originals:
 target=archive/original.name;copy_exact(original,target);copies[str(original)]={'file':rel(target),'sha256':sha(target)}
canonical=ROOT/'verification/lean/SafeLearning'/f'{NAME}.lean'
assert not canonical.exists();copy_exact(SOURCE,canonical)
snapshot=BASE/f'{NAME}-source-v1.lean';copy_exact(SOURCE,snapshot)
assert len(re.findall(r'^theorem ',canonical.read_text(),re.M))==10
pairs=[]
for suffix,command in [('standalone',['lake','env','lean',f'SafeLearning/{NAME}.lean']),('named-build',['lake','build',f'SafeLearning.{NAME}'])]:
 record=BASE/f'{NAME}-{suffix}-v1.json';log=BASE/f'{NAME}-{suffix}-v1.log'
 assert not record.exists() and not log.exists()
 before=sha(canonical);started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
 with log.open('xb') as f:actual=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
 finished=datetime.now(timezone.utc).isoformat();after=sha(canonical)
 data={'source':rel(canonical),'source_sha256_before':before,'source_sha256_after':after,'preserved_source':rel(snapshot),'preserved_source_sha256':sha(snapshot),'command':command,'actual_workdir':str(ROOT/'verification/lean'),'actual_exit_code':actual.returncode,'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-t,'log':rel(log),'log_sha256':sha(log),'actual_pair_helper':rel(Path(__file__)),'actual_pair_helper_sha256':sha(Path(__file__)),'scope':'Actual new unselected canonical future23 pair only. No owner mapping, current22 mutation, aggregate23 or semantic approval is inferred.'}
 write_new(record,data);pairs.append({'file':rel(record),'sha256':sha(record),'raw_log':{'file':rel(log),'sha256':sha(log)},'actual_exit_code':actual.returncode})
 assert before==after==DIGEST;guard()
 if actual.returncode:raise SystemExit(actual.returncode)
request=read(REQUEST)
result={'status':'passed_actual_canonical_pair_semicontinuity_future23_source_binding_requested','canonical_pair_prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_TMP_request':copies[str(REQUEST)],'entire_original_TMP_request_body_and_created_time':request,'canonical_source':{'file':rel(canonical),'sha256':DIGEST},'canonical_source_snapshot':{'file':rel(snapshot),'sha256':DIGEST},'public_theorem_count':10,'actual_canonical_pair':pairs,'all_original_TMP_byte_copies':copies,'actual_helper':{'file':rel(Path(__file__)),'sha256':sha(Path(__file__))},'all1113_selected22_sources_exact':True,'all31_current48_assets_inventory_and_four_working22_ledgers_exact':True,'coverage_complete':False,'scope':'Original complete-literal request/created time/body preserved unchanged. This records actual canonical compiler execution only. Independent full semantic review/canonical binding, new49 identity, candidate mapping and aggregate23 remain separate.'}
out=BASE/'basics1202-1237-canonical-paired-source-readiness-v1.json';write_new(out,result);guard()
print(json.dumps({'status':result['status'],'request':rel(out),'request_sha256':sha(out),'source_sha256':DIGEST,'actual_records':pairs}))
