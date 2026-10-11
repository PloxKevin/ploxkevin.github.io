"""Prepare seven whole literal decisions in a separate future25 candidate."""
from pathlib import Path
from datetime import datetime, timezone
import copy,hashlib,json

ROOT=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/future25-core'
OLD='book/coverage/core.json'
OLD_SHA='47b676890af40692cc1161c5472b461397b224e1a3724ee6990f03bb64d56bf5'
INV='book/coverage/inventory.json'
INV_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
READY=BASE+'/barrier-control/root-barrier-control25-canonical-readiness-v1.json'
SOURCE='verification/lean/SafeLearning/CompleteBarrierControlMaterial25.lean'
ORIGINALS=BASE+'/barrier-control/original-tmp/'
PEERS={ORIGINALS+'root-barrier-control-material25-two-literals-independent-applied-review-v1.json':
    '76e1758db4acca9f756742e630a66a69f7cd604a7380e4e6370e183f583162a5',
    ORIGINALS+'root-core25-case-study-guidance-five-whole-units-independent-applied-review-v1.json':
    '11a90753b9114695527c4ebbf707f81275237558b7793014994ad62ffb831190'}
OUT=BASE+'/core25-source52-material-candidate-v1.json'
REPORT=BASE+'/core25-source52-material-candidate-integrity-v1.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def write(n,d):
    p=ROOT/n;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')

assert sha(OLD)==OLD_SHA and sha(INV)==INV_SHA
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
audit=read('reports/full-coverage/lean-checkpoint-24/verification-original.json')
assert audit['status']=='passed' and audit['proof_file_count']==1144 and audit['theorem_count']==9279
assert all(c['exit_code']==0 for c in audit['checks'])
protected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')
    or n in {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']}
    or n==INV})
def guard():
    for n,h in protected.items():assert sha(n)==h,n
guard()
old=read(OLD);candidate=copy.deepcopy(old);inventory=read(INV)
units={r['key']:r for r in inventory['material_source_units']}
ready=read(READY)
assert ready['status']=='passed_actual_canonical_pair_unselected_future25'
assert ready['source']['file']==SOURCE and sha(SOURCE)==ready['source']['sha256']
assert ready['public_theorem_count']==7 and len(ready['actual_canonical_pair'])==2
for pair in ready['actual_canonical_pair']:
    assert sha(pair['file'])==pair['sha256']
    row=read(pair['file'])
    assert row['exit_code']==0 and row['source_sha256_before']==row['source_sha256_after']==sha(SOURCE)
    assert sha(row['log'])==row['log_sha256']
whole={}
identity=[]
for n,h in PEERS.items():
    assert sha(n)==h
    peer=read(n);assert 'passed' in peer['status'] and peer['errors']==[]
    assert peer['reviewer']=='/root/applied_next' and peer['reviewed_at_utc']
    prior_inventory=peer.get('current_inventory',peer.get('inventory'))
    assert prior_inventory['sha256'] in {INV_SHA,'d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'}
    for unit in peer['material_units']:
        key=unit['source_unit_key'];assert key not in whole
        assert unit['whole_unit_approved'] is True and unit['missing_clauses']==[]
        assert unit['review_status'] in {'passed','not_a_formal_claim'}
        assert unit['entire_inventory_record']==units[key]
        assert sha(units[key]['source'])==units[key]['source_sha256']
        assert unit['material_status'] in {'proved','not_a_formal_claim'}
        assert bool(unit['lean_declarations'])==(unit['material_status']=='proved')
        whole[key]=(unit,n,peer['reviewed_at_utc'])
    identity.append({'original_peer':ref(n),'entire_original_peer_body_and_time':peer,
        'original_inventory_binding':prior_inventory,'current_inventory':ref(INV),
        'all_owned_entire_inventory_records_literal_and_source_sha256_exact':True,
        'scope':'Current52 identity binding only. The original full semantic review body and time are unchanged.'})
assert len(whole)==7 and sum(u['material_status']=='proved' for u,n,t in whole.values())==2
changes=[]
for prior,row in zip(old['material_claims'],candidate['material_claims']):
    keys=row['source_unit_keys']
    if len(keys)!=1 or keys[0] not in whole:continue
    key=keys[0];unit,n,time=whole[key]
    assert prior['status']=='pending' and prior['source_text']==units[key]['source_text']
    assert prior['statement_in_prose']==prior['source_text']
    if 'entire_original_pending_claim_body_and_time' in unit:assert unit['entire_original_pending_claim_body_and_time']==prior
    row.update(kind='independently_reviewed_literal_material_unit',status=unit['material_status'],
        lean_declarations=copy.deepcopy(unit['lean_declarations']),hypotheses=copy.deepcopy(unit['hypotheses']),
        correspondence=unit['per_unit_reason'],remaining_gaps=[],
        independent_review={'source':n,'sha256':sha(n),'original_review_time':time},
        original_complete_literal_review_record=copy.deepcopy(unit),
        original_source52_entire_pending_material_row=copy.deepcopy(prior))
    changes.append(key)
assert set(changes)==set(whole) and len(changes)==7
assert SOURCE not in candidate['proof_files']
candidate['proof_files'][SOURCE]=sha(SOURCE)
candidate['generated_at_utc']=datetime.now(timezone.utc).isoformat()
candidate['future25_material_candidate_binding']={'original_source52_owner':ref(OLD),
    'current_inventory':ref(INV),'canonical_readiness':ref(READY),
    'whole_source_reviews':[ref(n) for n in PEERS],'original_review_identity_bindings':identity,
    'actual_verified24_audit':ref('reports/full-coverage/lean-checkpoint-24/verification-original.json'),
    'scope':'Seven complete literal decisions: two actual control-affine mathematical units and five case-study instructions. No exercise or parent-unit promotion. Live owners remain unchanged.',
    'coverage_complete':False}
assert candidate['exercises']==old['exercises'] and candidate['counts']==old['counts']
for prior,row in zip(old['material_claims'],candidate['material_claims']):
    if row['source_unit_keys'][0] in whole:assert row['original_source52_entire_pending_material_row']==prior
    else:assert row==prior
assert len(candidate['material_claims'])==len(old['material_claims'])
assert {n:h for n,h in candidate['proof_files'].items() if n!=SOURCE}==old['proof_files']
write(OUT,candidate)
write(REPORT,{'status':'passed_isolated_candidate_exact_original_rows_and_independent_whole_decisions',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(OUT),
    'original_owner':ref(OLD),'canonical_readiness':ref(READY),'whole_source_reviews':[ref(n) for n in PEERS],
    'new_proof_sources':1,'new_public_theorems':7,'whole_material_units':sorted(changes),
    'proved_whole_units':2,'study_guidance_whole_units':5,'all_92_exercises_exact':True,
    'all_other_material_rows_exact':True,'live_owner_written':False,'coverage_complete':False})
guard()
print(json.dumps({'status':'passed','candidate':ref(OUT),'whole_material_units':7,'new_public_theorems':7}))
