"""Bind the reviewed Core11 draft to its actual canonical pair, isolated only."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,copy
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/future27-core/core-current55-final-v1'
DRAFT=Path('/tmp/core27-current55-eleven-component-draft-v1')
READY=DRAFT/'core27-current55-eleven-component-readiness-draft-v1.json'
READY_SHA='eafe5b010a9afda1bb152c0d0562f49ee2ccb644a19ad9b0bc6395435a64901e'
CANONICAL='verification/lean/SafeLearning/CompleteCoreMPCFirstSuccessor27.lean'
SOURCE_SHA='09fc59984a9e53f86e8ddfa82b2bee79f163aeffd5dc173b88eb6d8fc9c8000c'
PAIRS='book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json'
ACTUAL='reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json'
INV_SHA='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
OLD_SHA='1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p),'sha256':sha(p)}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
 assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256']
 return p
def zero(d):
 codes=[d[k] for k in ['actual_exit_code','exit_code'] if k in d]
 assert codes and all(type(c) is int and c==0 for c in codes)
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def copy_new(s,t):
 assert not s.is_symlink() and not t.exists()
 t.parent.mkdir(parents=True,exist_ok=True)
 with t.open('xb') as f:f.write(s.read_bytes())
 assert sha(t)==sha(s)
parser=argparse.ArgumentParser();parser.add_argument('--draft-peer',required=True);parser.add_argument('--draft-peer-sha256',required=True);args=parser.parse_args()
assert sha(READY)==READY_SHA and sha(ROOT/'book/coverage/core.json')==OLD_SHA
assert sha(ROOT/'book/coverage/inventory.json')==INV_SHA and sha(ROOT/CANONICAL)==SOURCE_SHA
assert not BASE.exists()
ready=json.loads(READY.read_bytes());draft_path=checked(ready['candidate']);draft=json.loads(draft_path.read_bytes())
peer_path=checked({'file':args.draft_peer,'sha256':args.draft_peer_sha256});peer=json.loads(peer_path.read_bytes())
assert 'passed' in peer['status'] and peer.get('errors',[])==[]
assert peer['candidate']==ready['candidate'] and peer['readiness']==ref(READY)
peer_closure=peer['closed_evidence_sha256']
assert isinstance(peer_closure,dict) and len(peer_closure)==13
for n,h in peer_closure.items():checked({'file':n,'sha256':h})
pairs=json.loads((ROOT/PAIRS).read_bytes());actual=json.loads((ROOT/ACTUAL).read_bytes());zero(actual)
assert pairs['status']=='passed_actual_eight_source141_canonical_standalone_and_named_pairs_unselected_future27'
assert pairs['errors']==[] and pairs['source_count']==8 and pairs['public_theorem_count']==141
assert actual['actual_command']==['python3','book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py','--apply']
assert actual['helper_sha256_before']==actual['helper_sha256_after'] and actual['actual_workdir']==str(ROOT)
assert sha(ROOT/actual['log'])==actual['log_sha256']
for n,h in actual['helper_sha256_after'].items():assert sha(ROOT/n)==h
rows=[r for r in pairs['actual_paired_records'] if r['source']['file']==CANONICAL]
assert len(rows)==2 and {r['kind'] for r in rows}=={'standalone','named'}
for r in rows:
 assert r['source']['sha256']==SOURCE_SHA and type(r['actual_exit_code']) is int and r['actual_exit_code']==0
 d=json.loads(checked(r['actual_record']).read_bytes());zero(d)
 assert d['source']==CANONICAL and d['source_sha256_before']==d['source_sha256_after']==SOURCE_SHA
 expected=['lake','env','lean','SafeLearning/CompleteCoreMPCFirstSuccessor27.lean'] if r['kind']=='standalone' else ['lake','build','SafeLearning.CompleteCoreMPCFirstSuccessor27']
 assert d['command']==expected and d['actual_workdir']==str(ROOT/'verification/lean')
 assert r['raw_log']=={'file':d['log'],'sha256':d['log_sha256']};checked(r['raw_log']);checked(r['source_snapshot']);assert r['source_snapshot']['sha256']==SOURCE_SHA
aliases=pairs['original_closed_byte_aliases']
for r in aliases.values():checked({'file':r['file'],'sha256':r['sha256']})
def alias(original,digest):
 r=aliases[original+'::'+digest];assert r['original_file']==original and r['original_sha256']==digest
 return {'file':r['file'],'sha256':digest}
new=copy.deepcopy(draft)
oldproofs=copy.deepcopy(new['proof_files']);assert len(oldproofs)==181 and CANONICAL not in oldproofs
new['proof_files'][CANONICAL]=SOURCE_SHA;new['counts']['proof_files']=182
new_claims=[]
for r in new['material_claims']+[c for e in new['exercises'] for c in e['claims']]:
 if 'core27-mpc-precise-component-' in r['id']:
  oldref=r['independent_review'];canonical_ref=alias(oldref['source'],oldref['sha256'])
  r['independent_review']={**oldref,'source':canonical_ref['file']}
  new_claims.append(r)
assert len(new_claims)==44
assert new['generated_at_utc']==draft['generated_at_utc']
assert next(e for e in new['exercises'] if e['inventory_key']=='lyapunov-mpc.html::exercise-18')['status']=='partial'
for key in ['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739','lyapunov-mpc.html::node-1387']:
 assert any(key in r['source_unit_keys'] and r['status']=='pending' for r in new['material_claims'])
new['future27_component_pair_binding']={'paired_readiness':ref(ROOT/PAIRS),'actual_execution':ref(ROOT/ACTUAL),'new_source':{'file':CANONICAL,'sha256':SOURCE_SHA},'public_theorem_count':11,'whole_MPC_exercise_and_certificate_pending':True}
BASE.mkdir(parents=True)
closed={}
for p in sorted(DRAFT.iterdir()):
 assert p.is_file() and p.suffix=='.json'
 t=BASE/'original-draft'/p.name;copy_new(p,t);closed[str(p)]=ref(t)
copy_new(peer_path,BASE/'original-peer'/peer_path.name);closed[str(peer_path)]=ref(BASE/'original-peer'/peer_path.name)
for n,h in sorted(peer_closure.items()):
 p=checked({'file':n,'sha256':h});t=BASE/'original-peer'/p.name;copy_new(p,t);closed[n]=ref(t)
source_row=next(r for r in pairs['sources'] if r['canonical_source']==CANONICAL)
declarations=source_row['all_public_declarations'];assert len(declarations)==11
evidence={CANONICAL:SOURCE_SHA,PAIRS:sha(ROOT/PAIRS),ACTUAL:sha(ROOT/ACTUAL),actual['log']:actual['log_sha256']}
for r in rows:
 for k in ['actual_record','raw_log','source_snapshot']:
  evidence[r[k]['file']]=r[k]['sha256']
for r in closed.values():evidence[r['file']]=r['sha256']
semantic=[]
for oldref in ready['original_full_component_peers']:
 a=alias(oldref['file'],oldref['sha256']);p=checked(a);body=json.loads(p.read_bytes())
 assert body==oldref['entire_original_body_and_time']
 semantic.append({**a,'original_review_status':body['status'],'original_review_time':body['reviewed_at_utc']})
 evidence[a['file']]=a['sha256']
candidate=BASE/'core27-current55-eleven-component-candidate-v1.json';write(candidate,new)
offer=BASE/'core27-current55-eleven-component-offer-v1.json'
proof={'sha256':SOURCE_SHA,'evidence_sha256':evidence,'theorem_count':11,'public_theorem_names':declarations,'mapped_named_declarations':declarations,'actual_pair':rows}
write(offer,{'status':'paired_isolated_current55_core_candidate_awaiting_final_independent_mapping_review','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'mapped_ledger':ref(candidate)['file'],'mapped_ledger_sha256':sha(candidate),'inventory':'book/coverage/inventory-after-correction55.json','inventory_sha256':INV_SHA,'source_sha256':new['source_sha256'],'proof_files':{CANONICAL:proof},'candidate':ref(candidate),'original_draft':closed[str(READY)],'original_draft_mechanics_peer':closed[str(peer_path)],'original_full_component_peers':semantic,'original_byte_aliases':closed,'canonical_original_history_packet':ref(ROOT/PAIRS),'actual_canonical_pair_execution':ref(ROOT/ACTUAL),'actual_canonical_commands':2,'new_components':11,'new_material_component_rows':33,'whole_exercise18_and_material737_739_1387_pending':True,'old181_proof_files_retained':True,'all92_exercise_statuses_unchanged':True,'coverage_complete':False,'prepared_by':ref(Path(__file__))})
assert sha(ROOT/'book/coverage/core.json')==OLD_SHA and sha(ROOT/'book/coverage/inventory.json')==INV_SHA
print(json.dumps({'status':'passed_isolated_core27_canonical_pair_binding','candidate':ref(candidate),'offer':ref(offer),'new_source_count':1,'exports':11,'actual_commands':2,'installed_owner_write':False}))
