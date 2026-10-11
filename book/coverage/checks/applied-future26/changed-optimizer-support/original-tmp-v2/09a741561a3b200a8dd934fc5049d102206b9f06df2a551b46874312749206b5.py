from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[5]
BASE=ROOT/'book/coverage/checks/applied-future26/changed-optimizer-support'
NAME='CompleteLyapunovChangedOptimizerSupport26'
SOURCE=Path('/tmp/CompleteLyapunovChangedOptimizerSupport26-trial2.lean')
DIGEST='a6a11320cfddadef69b09669fdbeb2b9dfb6f535ffd7bd1055adcfa5186b2832'
PEER=Path('/tmp/lyapunov-current53-support5-and-whole1397-exercise19a-independent-foundations-final-review26-v1.json')
PEER_SHA='9d7acf0578fe79e75eaf5f75e8965f8374faf5a9cbfcae258b58bc18fdde31a3'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(p.relative_to(ROOT)),'sha256':H(p)}
selection=read(ROOT/'reports/full-coverage/checkpoint-25-selection.json')
assert len(selection['proof_files'])==1156
manifest=read(ROOT/'reports/full-coverage/checkpoint-25-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
protected={n:r['sha256'] for n,r in selection['proof_files'].items()}
owners={f'book/coverage/{n}.json' for n in ('core','foundations','applied','modules','applied-promotions')}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in owners})
assert len([n for n in protected if n.startswith('SafeLearning/')])==31 and owners<=protected.keys()
protected['SafeLearning/lyapunov-mpc.html']='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
protected['book/coverage/inventory.json']='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
protected['book/coverage/inventory-after-correction53.json']=protected['book/coverage/inventory.json']
protected['reports/full-coverage/source53-correction-application-v1.json']='fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548'
for name in ('reports/full-coverage/checkpoint-25-selection.json','reports/full-coverage/checkpoint-25-manifest.json','/tmp/root_tmp_lean26_runner_v3.py'):
 protected[name]=H(ROOT/name if not name.startswith('/') else Path(name))
def guard():
 for name,h in protected.items():assert H(ROOT/name if not name.startswith('/') else Path(name))==h,name
guard();assert H(SOURCE)==DIGEST and H(PEER)==PEER_SHA
peer=read(PEER);assert peer['errors']==[] and peer['entire_new_five_theorem_source_body_read']==SOURCE.read_text()
assert len(peer['new_five_public_theorems'])==len(re.findall(r'^theorem ',SOURCE.read_text(),re.M))==5
canonical=ROOT/'verification/lean/SafeLearning'/f'{NAME}.lean'
readiness=BASE/'support5-canonical-source53-paired-readiness-v1.json'
assert not canonical.exists() and not readiness.exists()
originals={SOURCE,PEER}
def collect(value):
 if isinstance(value,dict):
  for k,v in value.items():collect(k);collect(v)
 elif isinstance(value,list):
  for v in value:collect(v)
 elif isinstance(value,str) and value.startswith('/tmp/') and len(value)<240 and '\n' not in value and '\x00' not in value:
  p=Path(value)
  if p.is_file() and not p.is_symlink() and p.suffix in {'.py','.json','.log','.lean','.txt'}:originals.add(p)
collect(peer)
for pattern in ('*changed*support26*','CompleteLyapunovChangedOptimizerSupport26*'):
 originals.update(p for p in Path('/tmp').glob(pattern) if p.is_file() and p.suffix in {'.py','.json','.log','.lean','.txt'})
originals.add(Path('/tmp/root_tmp_lean26_runner_v3.py'))
aliases={}
for p in sorted(originals):
 target=BASE/'original-tmp'/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 assert not target.exists()
 with target.open('xb') as stream:stream.write(p.read_bytes())
 assert H(p)==H(target);aliases[str(p)]=ref(target)
canonical.parent.mkdir(parents=True,exist_ok=True)
with canonical.open('xb') as stream:stream.write(SOURCE.read_bytes())
snapshot=BASE/f'{NAME}-original-source-v1.lean'
with snapshot.open('xb') as stream:stream.write(SOURCE.read_bytes())
pairs=[]
for helper,suffix in [('book/coverage/check_core_standalone.py','-standalone.json'),('book/coverage/check_core_named_build.py','-named-build.json')]:
 record=ROOT/'book/coverage/checks'/f'{NAME}{suffix}';assert not record.exists()
 result=subprocess.run(['python3',helper,NAME],cwd=ROOT)
 guard();assert H(canonical)==DIGEST
 if result.returncode:raise SystemExit(result.returncode)
 actual=read(record);assert type(actual['exit_code'])is int and actual['exit_code']==0
 assert actual['source_sha256_before']==actual['source_sha256_after']==DIGEST and actual['source_unchanged'] is True
 assert H(ROOT/actual['log'])==actual['log_sha256']
 pairs.append({'record':ref(record),'entire_original_actual_record':actual,'raw_log':{'file':actual['log'],'sha256':actual['log_sha256']},'source_snapshot':ref(snapshot)})
guard()
out={'status':'passed_actual_canonical_support5_pair_current53_unselected_future26','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source':ref(canonical),'source_snapshot':ref(snapshot),'original_full_current53_semantic_peer':aliases[str(PEER)],'entire_original_semantic_peer_body_and_time':peer,'public_theorems':peer['new_five_public_theorems'],'public_theorem_count':5,'actual_canonical_pair':pairs,'actual_canonical_execution_count':2,'original_TMP_byte_copies':aliases,'protected_input_sha256':protected,'protected_selected25_sources':1156,'protected_current53_assets':31,'protected_installed25_owners':5,'scope':'Exact five changed-unique-removal support bridge bodies and original successful/full current53 semantic decisions, failed/pass trials and times preserved. Actual distinct canonical standalone/named pair only; no aggregate, owner, source or checkpoint25 coverage mutation.'}
with readiness.open('x') as stream:stream.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed','readiness':ref(readiness),'original_aliases':len(aliases),'public_theorems':5}))
