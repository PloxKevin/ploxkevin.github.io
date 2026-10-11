"""Genuine new-name pair with explicit frozen22/source49/source50 identities."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future23/linalg-refresher'
TMP=Path('/tmp');NAME='CompleteFoundationsLinalgRefresher23'
SOURCE=TMP/'foundations-linalg-refresher23-trial2.lean'
DIGEST='1918ab182f7fe20385966020197f3195abca4d61068ebeb1f21bfc9bd2061f0e'
REQUEST=TMP/'foundations-linalg-refresher23-eleven-literals-full-source-review-request-v1.json'
REQUEST_SHA='67835ed0ee903e73565c80453bc08a5d55bdc8bcad6f30c41c9a560576739a2a'
PEER=TMP/'foundations-linalg-refresher-eleven-literals-independent-modules-source-review23-v1.json'
PEER_SHA='be9f21c01be811f7b8137e0ea6d6638f9f11ad5a6c5e3f489dd6189393939f5f'
CURRENT50='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(p),'sha256':sha(p)}
def write_new(p,x):
 with p.open('x') as f:f.write(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def copy_exact(s,t):
 if t.exists():assert t.read_bytes()==s.read_bytes()
 else:
  with t.open('xb') as f:f.write(s.read_bytes())
 assert sha(t)==sha(s)
assert sha(SOURCE)==DIGEST and sha(REQUEST)==REQUEST_SHA and sha(PEER)==PEER_SHA
request=read(REQUEST);peer=read(PEER);assert 'passed' in peer['status']
manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')
proofs={n:r['sha256'] for n,r in manifest['proof_files'].items()};assert len(proofs)==1113
frozenassets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(frozenassets)==31
protected={**proofs,**frozenassets}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}})
protected.update({'SafeLearning/cmdp.html':'5a503475452eacbeb8d5b8f4b3dd846bc3d88ff6817bd900a3cf3b2e2b23f6e9','SafeLearning/lyapunov-mpc.html':'228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c','book/coverage/inventory.json':CURRENT50,'book/coverage/inventory-after-correction50.json':CURRENT50})
def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
 for n,h in frozenassets.items():assert sha(ROOT/'reports/full-coverage/checkpoint-22'/n)==h,n
 assert sha(ROOT/'book/coverage/inventory-after-correction49.json')=='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
 inv=read(ROOT/'book/coverage/inventory.json');units={r['key']:r for r in inv['material_source_units']}
 for row in request['material_units']:assert units[row['source_unit_key']]==row['entire_inventory_record']
guard();BASE.mkdir(parents=True,exist_ok=True);archive=BASE/'original-tmp';archive.mkdir(exist_ok=True)
originals=[TMP/f'foundations-linalg-refresher23-trial{n}.{s}' for n in [1,2] for s in ['lean','json','log']]
originals.extend([REQUEST,PEER,TMP/'run-foundations-linalg-refresher23-trial-v1.py',TMP/'run-foundations-linalg-refresher23-trial-v2.py',TMP/'prepare-foundations-linalg-refresher23-source-review-request-v1.py',TMP/'foundations-linalg-refresher23-initial-old48-guard-observed-failure-v1.json',TMP/'modules-linalg-refresher23-eleven-literal-review-check-v1.py',TMP/'modules-linalg-refresher23-independent-review-actual-execution-v1.json',TMP/'modules-linalg-refresher23-independent-review-actual-execution-v1.log'])
copies={}
for original in originals:
 target=archive/original.name;copy_exact(original,target);copies[str(original)]=ref(target)
canonical=ROOT/'verification/lean/SafeLearning'/f'{NAME}.lean';assert not canonical.exists();copy_exact(SOURCE,canonical)
snapshot=BASE/f'{NAME}-source-v1.lean';copy_exact(SOURCE,snapshot);assert len(re.findall(r'^theorem ',canonical.read_text(),re.M))==23
pairs=[]
for suffix,command in [('standalone',['lake','env','lean',f'SafeLearning/{NAME}.lean']),('named-build',['lake','build',f'SafeLearning.{NAME}'])]:
 record=BASE/f'{NAME}-{suffix}-source50-v1.json';log=BASE/f'{NAME}-{suffix}-source50-v1.log';assert not record.exists() and not log.exists()
 before=sha(canonical);started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
 with log.open('xb') as f:actual=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
 finished=datetime.now(timezone.utc).isoformat();after=sha(canonical)
 data={'source':rel(canonical),'source_sha256_before':before,'source_sha256_after':after,'preserved_source':rel(snapshot),'preserved_source_sha256':sha(snapshot),'command':command,'actual_workdir':str(ROOT/'verification/lean'),'actual_exit_code':actual.returncode,'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-t,'log':rel(log),'log_sha256':sha(log),'actual_pair_helper':rel(Path(__file__)),'actual_pair_helper_sha256':sha(Path(__file__)),'scope':'Actual new unselected canonical future23 pair only. Current50 identity is distinct from immutable original49 request/peer; no ledger mapping or aggregate23 claim.'}
 write_new(record,data);pairs.append({**ref(record),'raw_log':ref(log),'actual_exit_code':actual.returncode});assert before==after==DIGEST;guard()
 if actual.returncode:raise SystemExit(actual.returncode)
result={'status':'passed_actual_canonical_pair_23_linalg_bodies_source50_original49_semantics_preserved_future23','canonical_pair_prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_TMP_request':copies[str(REQUEST)],'entire_original_TMP_request_body_and_created_time':request,'original_independent_Module_peer':copies[str(PEER)],'entire_original_independent_peer_body_and_reviewed_time':peer,'canonical_source':ref(canonical),'canonical_source_snapshot':ref(snapshot),'public_theorem_count':23,'actual_canonical_pair':pairs,'all_original_TMP_byte_copies':copies,'actual_helper':ref(Path(__file__)),'current_authoritative_source50_inventory':ref(ROOT/'book/coverage/inventory-after-correction50.json'),'original_source49_inventory':ref(ROOT/'book/coverage/inventory-after-correction49.json'),'all11_whole_linalg_literal_records_unchanged49_to50':True,'all1113_selected22_sources_exact':True,'all31_frozen22_source48_assets_exact':True,'all31_current50_assets_inventory_and_four_working22_ledgers_exact':True,'coverage_complete':False,'scope':'Original23 full-body/11 complete literal request and independent original review body/time remain unchanged. Only actual canonical compiler evidence is added. Narrow canonical binding, isolated future23 mapping and aggregate23/selection remain separate.'}
out=BASE/'eleven-literals-canonical-paired-source50-readiness-v1.json';write_new(out,result);guard();print(json.dumps({'status':result['status'],'request':ref(out),'source_sha256':DIGEST,'actual_records':pairs}))
