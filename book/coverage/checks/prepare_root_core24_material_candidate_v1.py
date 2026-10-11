"""Prepare an isolated candidate from ten independently reviewed whole literals."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
BASE = 'book/coverage/checks/future24-core'
OLD = 'book/coverage/core.json'
OLD_SHA = '1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a'
INV = 'book/coverage/inventory.json'
INV_SHA = 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
READY = BASE+'/barrier-intro/root-barrier-intro24-canonical-readiness-v1.json'
SOURCE = 'verification/lean/SafeLearning/CompleteBarrierIntroMaterial24.lean'
PEERS = {
    BASE+'/barrier-intro/original-tmp/root-barrier-intro24-three-literals-independent-applied-review-v1.json':
        'ad7ed9ea70ee14d4871ff861c2e5fa3b5868e661f88d9cd0025984735a2a225f',
    BASE+'/barrier-intro/original-tmp/root-core24-seven-guidance-independent-applied-review-v1.json':
        '7b699bec787dd4fa79b7b77aed0da6bef3a44af6821ff30dd0371b4da4b90c3a'}
OUT = BASE+'/core24-source51-material-candidate-v1.json'
REPORT = BASE+'/core24-source51-material-candidate-integrity-v1.json'

def sha(name): return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT/name).read_text())
def ref(name): return {'file':name,'sha256':sha(name)}
def write(name,data):
    p=ROOT/name;assert not p.exists(),name
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')

assert sha(OLD)==OLD_SHA and sha(INV)==INV_SHA
old=read(OLD);candidate=copy.deepcopy(old);inventory=read(INV)
units={r['key']:r for r in inventory['material_source_units']}
manifest=read('reports/full-coverage/checkpoint-23-manifest.json')
protected={n:h for n,h in manifest['working_inputs_sha256'].items()
           if n.startswith('SafeLearning/') or n in {OLD,INV,'book/coverage/modules.json',
              'book/coverage/foundations.json','book/coverage/applied.json','book/coverage/applied-promotions.json'}}
def guard():
    for name,digest in protected.items():assert sha(name)==digest,name
guard()
ready=read(READY)
assert ready['status']=='passed_actual_canonical_pair_unselected_future24'
assert ready['source']['file']==SOURCE and sha(SOURCE)==ready['source']['sha256']
assert ready['public_theorem_count']==4 and len(ready['actual_canonical_pair'])==2
for pair in ready['actual_canonical_pair']:
    assert sha(pair['file'])==pair['sha256']
    row=read(pair['file'])
    assert row['exit_code']==0 and row['source_sha256_before']==row['source_sha256_after']==sha(SOURCE)
    assert sha(row['log'])==row['log_sha256']
whole={}
for name,digest in PEERS.items():
    assert sha(name)==digest
    peer=read(name)
    assert peer['status']=='independent_whole_literal_source_review_passed'
    assert peer['reviewer']=='/root/applied_next' and peer['reviewed_at_utc']
    assert peer['current_inventory']['sha256']==INV_SHA
    for unit in peer['material_units']:
        key=unit['source_unit_key'];assert key not in whole
        assert unit['whole_unit_approved'] is True and unit['missing_clauses']==[]
        assert unit['review_status']=='independent_whole_source_review_passed'
        assert unit['entire_inventory_record']==units[key]
        assert unit['unit_text_sha256']==units[key]['text_sha256']
        assert unit['source_sha256']==units[key]['source_sha256']==sha(units[key]['source'])
        assert unit['material_status'] in {'proved','not_a_formal_claim'}
        assert (bool(unit['lean_declarations'])==(unit['material_status']=='proved'))
        whole[key]=(unit,name,peer['reviewed_at_utc'])
assert len(whole)==10
assert sum(u['material_status']=='proved' for u,n,t in whole.values())==1
changes=[]
for prior,row in zip(old['material_claims'],candidate['material_claims']):
    keys=row['source_unit_keys']
    if len(keys)!=1 or keys[0] not in whole:continue
    key=keys[0];unit,name,time=whole[key]
    assert prior['status']=='pending'
    assert prior['source_text']==unit['entire_inventory_record']['source_text']
    assert prior['statement_in_prose']==prior['source_text']
    if 'preserved_entire_original_pending_claim' in unit:
        assert unit['preserved_entire_original_pending_claim']==prior
    row.update(kind='independently_reviewed_literal_material_unit',
        status=unit['material_status'],lean_declarations=copy.deepcopy(unit['lean_declarations']),
        hypotheses=copy.deepcopy(unit['hypotheses']),correspondence=unit['per_unit_reason'],
        remaining_gaps=[],independent_review={'source':name,'sha256':sha(name),'original_review_time':time},
        original_complete_literal_review_record=copy.deepcopy(unit),
        original_source51_entire_pending_material_row=copy.deepcopy(prior))
    changes.append(key)
assert set(changes)==set(whole) and len(changes)==10
assert SOURCE not in candidate['proof_files']
candidate['proof_files'][SOURCE]=sha(SOURCE)
candidate['generated_at_utc']=datetime.now(timezone.utc).isoformat()
candidate['future24_material_candidate_binding']={
    'original_source51_owner':ref(OLD),'current_inventory':ref(INV),
    'canonical_readiness':ref(READY),'whole_source_reviews':[ref(n) for n in PEERS],
    'scope':'Ten full literal decisions: one actual mathematical worked unit and nine study instructions. Original mathematical review times and complete prior pending rows are preserved. Live owners are unchanged.',
    'coverage_complete':False}
assert candidate['exercises']==old['exercises'] and candidate['counts']==old['counts']
for prior,row in zip(old['material_claims'],candidate['material_claims']):
    if row['source_unit_keys'][0] in whole:assert row['original_source51_entire_pending_material_row']==prior
    else:assert row==prior
assert len(candidate['material_claims'])==len(old['material_claims'])
assert {n:h for n,h in candidate['proof_files'].items() if n!=SOURCE}==old['proof_files']
write(OUT,candidate)
write(REPORT,{'status':'passed_isolated_candidate_exact_original_rows_and_independent_whole_decisions',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(OUT),
    'original_owner':ref(OLD),'canonical_readiness':ref(READY),
    'whole_source_reviews':[ref(n) for n in PEERS],
    'new_proof_sources':1,'new_public_theorems':4,'whole_material_units':sorted(changes),
    'proved_whole_units':1,'study_guidance_whole_units':9,
    'all_92_exercises_exact':True,'all_other_material_rows_exact':True,
    'live_owner_written':False,'coverage_complete':False})
guard()
print(json.dumps({'status':'passed','candidate':ref(OUT),'whole_material_units':10,'new_public_theorems':4}))
