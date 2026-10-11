"""Prepare only48 reviewed whole label decisions against the held Core25 candidate."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/future26-core/box-labels'
PRIOR='book/coverage/checks/future25-core/core25-source52-material-candidate-v1.json'
PEER=BASE+'/original-tmp/root-core26-box-label-118-independent-applied-full-context-review-v1.json'
CAT=BASE+'/closed-original-byte-aliases-v1.json'
OUT=BASE+'/core26-source52-labels-candidate-v1.json'
REPORT=BASE+'/core26-source52-labels-candidate-integrity-v1.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def write(n,d):
 p=ROOT/n;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert not (ROOT/OUT).exists() and not (ROOT/REPORT).exists()
assert sha(PRIOR)=='4e96c717055187cfc24e9e60a19a7d183499336570d99fbf9954ff199ff49572'
assert sha(PEER)=='c1d15307054f027da5f5ff25b7bec6d9703360e629947c452888d1cc20ded167'
assert sha('book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
assert len(manifest['proof_files'])==1144 and len(manifest['frozen_inputs_sha256'])==40485
held={n:r['sha256'] for n,r in manifest['proof_files'].items()}
held.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']}})
def guard():
 for n,h in held.items():assert sha(n)==h,n
guard()
prior=read(PRIOR);live=read('book/coverage/core.json');peer=read(PEER);catalog=read(CAT)
assert 'passed' in peer['status'] and peer['errors']==[] and peer['individually_read_complete_labels']==118
assert peer['original_core24_sha256']==sha('book/coverage/core.json')
assert peer['whole_nonformal_labels_approved']==48 and peer['substantive_titles_retained_pending']==70
assert peer['proved_mathematical_units']==0 and peer['lean_declarations']==[]
for row in catalog['original_absolute_path_byte_aliases']:assert sha(row['canonical_file'])==row['sha256']
units={r['key']:r for r in read('book/coverage/inventory.json')['material_source_units']}
live_rows={r['source_unit_keys'][0]:r for r in live['material_claims'] if len(r['source_unit_keys'])==1}
base_rows={r['source_unit_keys'][0]:r for r in prior['material_claims'] if len(r['source_unit_keys'])==1}
approved={}
for row in peer['material_units']:
 key=row['source_unit_key'];assert row['entire_inventory_record']==units[key] and units[key]['classes']==['box-label']
 assert row['entire_original_pending_claim_body_and_time']==live_rows[key]==base_rows[key]
 assert base_rows[key]['status']=='pending' and sha(units[key]['source'])==units[key]['source_sha256']
 if row['whole_unit_approved']:
  assert row['material_status']=='nonformal' and row['missing_clauses']==[] and row['lean_declarations']==[] and row['hypotheses']==[]
  assert key not in approved;approved[key]=row
 else:assert row['material_status']=='pending' and row['missing_clauses']
assert len(approved)==48 and len(peer['material_units'])==118
candidate=copy.deepcopy(prior);changes=[]
for before,row in zip(prior['material_claims'],candidate['material_claims']):
 keys=row['source_unit_keys']
 if len(keys)!=1 or keys[0] not in approved:continue
 unit=approved[keys[0]]
 row.update(kind='independently_reviewed_literal_material_unit',status='not_a_formal_claim',lean_declarations=[],hypotheses=[],correspondence=unit['per_unit_reason'],remaining_gaps=[],independent_review={'source':PEER,'sha256':sha(PEER),'original_review_time':peer['reviewed_at_utc']},original_complete_literal_review_record=copy.deepcopy(unit),original_source52_entire_pending_material_row=copy.deepcopy(before))
 changes.append(keys[0])
assert set(changes)==set(approved)
candidate['generated_at_utc']=datetime.now(timezone.utc).isoformat()
candidate['future26_label_material_candidate_binding']={'prior_isolated_owner25_candidate':ref(PRIOR),'current_inventory':ref('book/coverage/inventory.json'),'original_full118_label_peer':ref(PEER),'closed_original_byte_aliases':ref(CAT),'scope':'48 complete literal labels only.70 substantive label assertions remain pending; all neighboring bodies, exercises and theorem proofs remain unchanged. The isolated base25 and this26 candidate have not been installed or aggregate-verified.','coverage_complete':False}
assert candidate['proof_files']==prior['proof_files'] and candidate['exercises']==prior['exercises'] and candidate['counts']==prior['counts']
for before,row in zip(prior['material_claims'],candidate['material_claims']):
 if len(row['source_unit_keys'])==1 and row['source_unit_keys'][0] in approved:assert row['original_source52_entire_pending_material_row']==before
 else:assert row==before
write(OUT,candidate)
write(REPORT,{'status':'passed_isolated_core26_labels_candidate_exact_48_whole_nonformal_decisions','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(OUT),'prior_isolated_owner25_candidate':ref(PRIOR),'original_full118_label_peer':ref(PEER),'whole_nonformal_units':sorted(changes),'substantive_labels_retained_pending':70,'new_proof_sources':0,'new_public_theorems':0,'all_other_rows_and_92_exercises_and_177_proof_hashes_exact':True,'live_owner_written':False,'aggregate_verification_pending':True,'coverage_complete':False})
guard();print(json.dumps({'status':'passed','whole_nonformal_labels':48,'substantive_labels_pending':70,'new_theorems':0,'live_owners_unchanged':True}))
