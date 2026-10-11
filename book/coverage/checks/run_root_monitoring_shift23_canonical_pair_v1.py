from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future23-monitoring';TMP=Path('/tmp');NAME='CompleteMonitoringShiftedMean23';SOURCE=TMP/'root-monitoring-shifted-mean23-trial4.lean';DIGEST='23367dac7f0ad16b258a895ffeaa62dcc334b3291646458760fb20f58fdc4c46'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def exact_copy(s,t):
 t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert sha(t)==sha(s),str(t)
 else:
  with t.open('xb') as f:f.write(s.read_bytes())
 assert sha(t)==sha(s)
selection=read(ROOT/'reports/full-coverage/checkpoint-22-selection.json');manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage' and len(selection['proof_files'])==1113
protected={n:r['sha256'] for n,r in selection['proof_files'].items()}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/inventory.json','book/coverage/core.json','book/coverage/modules.json','book/coverage/foundations.json','book/coverage/applied.json'}})
protected['SafeLearning/cmdp.html']='5a503475452eacbeb8d5b8f4b3dd846bc3d88ff6817bd900a3cf3b2e2b23f6e9'
protected['book/coverage/inventory.json']='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
assert read(ROOT/'reports/full-coverage/source49-apply-execution-v1.json')['actual_exit_code']==0
def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
guard();assert sha(SOURCE)==DIGEST
canonical=ROOT/'verification/lean/SafeLearning'/f'{NAME}.lean'
assert not canonical.exists()
for suffix in ['-standalone.json','.log','-named-build.json','-named-build.log']:
 assert not (ROOT/'book/coverage/checks'/f'{NAME}{suffix}').exists()
BASE.mkdir(parents=True,exist_ok=True)
originals={p for p in TMP.glob('root-monitoring-shifted-mean23-trial*') if p.is_file()}
assert len(originals)==16
archived={}
for p in sorted(originals):
 target=BASE/'original-tmp'/p.name;exact_copy(p,target);archived[str(p)]={'file':rel(target),'sha256':sha(target)}
exact_copy(SOURCE,canonical);snapshot=BASE/f'{NAME}-source-v1.lean';exact_copy(SOURCE,snapshot)
assert len(re.findall(r'^theorem ',canonical.read_text(),re.M))==2
for helper in ['book/coverage/check_core_standalone.py','book/coverage/check_core_named_build.py']:
 r=subprocess.run(['python3',helper,NAME],cwd=ROOT,check=False);guard();assert sha(canonical)==DIGEST
 if r.returncode:raise SystemExit(r.returncode)
pairs=[]
for suffix in ['-standalone.json','-named-build.json']:
 p=ROOT/'book/coverage/checks'/f'{NAME}{suffix}';d=read(p)
 assert d['exit_code']==0 and d['source_sha256_before']==d['source_sha256_after']==DIGEST and sha(ROOT/d['log'])==d['log_sha256']
 pairs.append({'file':rel(p),'sha256':sha(p),'log':{'file':d['log'],'sha256':d['log_sha256']},'actual_exit_code':0})
result=BASE/'root-monitoring-shift23-canonical-readiness-v1.json';assert not result.exists()
with result.open('x') as f:f.write(json.dumps({'status':'passed_actual_canonical_standalone_and_named_pair_unselected_future23','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source':{'file':rel(canonical),'sha256':DIGEST},'source_snapshot':{'file':rel(snapshot),'sha256':DIGEST},'public_theorem_count':2,'actual_canonical_pair':pairs,'original_TMP_byte_copies':archived,'protected_selected22_source_count':1113,'protected_current49_asset_count':31,'scope':'Original failed and passing trials remain exact byte copies. Independent two-body/component review remains separate and pending. Canonical pair establishes actual compiler executions only. Source49 correspondence, aggregate23 kernel/axiom audit, selection and whole exercise approval remain separate.','coverage_complete':False},indent=2)+'\n')
guard();print(json.dumps({'status':'passed','canonical_source_sha256':DIGEST,'public_theorems':2,'archived_originals':len(archived),'readiness':rel(result)}))
