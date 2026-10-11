from pathlib import Path
import collections, datetime, hashlib, json, sys

ROOT=Path('/home/oxrexkevin/SafetyBased')
HERE=ROOT/'book/coverage/checks/foundations-future22'
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def fp(x): return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def checked(name,digest):
 p=ROOT/name; assert sha(p)==digest,name; return read(p)

expected={
 'book/coverage/build_foundations22.py':'2177085302d3dee0cb67b25e9346f566c5ef40ec48d85d7d2de450d8421d385f',
 'book/coverage/checks/foundations-future22/foundations-source48-candidate-ledger22-v1.json':'cba5b6308dc33346cb3e86dc7fc3c5e2f43773ec95b55d0c4a0b42bdd0cb4cbb',
 'book/coverage/checks/foundations-future22/foundations-source48-material22-interface-binding-v1.json':'7a0729299f3545ced42662c820681c01fc95a11ef3a9343955f937767bdde31c',
 'book/coverage/checks/foundations-future22/foundations-source48-integration-offer22-draft-v1.json':'bb4d6dcb74a62d1fd0e694c8e250383bad42624c7fae3a43896a7153e213ce89'}
for n,h in expected.items(): assert sha(ROOT/n)==h,n
offer=read(HERE/'foundations-source48-integration-offer22-draft-v1.json')
binding=read(HERE/'foundations-source48-material22-interface-binding-v1.json')
base=checked(offer['held21_ledger'],offer['held21_ledger_sha256'])
candidate=checked(offer['mapped_ledger'],offer['mapped_ledger_sha256'])
inventory=checked(offer['current_inventory'],offer['current_inventory_sha256'])
assert sha(ROOT/'book/coverage/inventory.json')==offer['current_inventory_sha256']
units={r['key']:r for r in inventory['material_source_units']}
selection=checked(offer['base_selection'],offer['base_selection_sha256'])
audit=checked(offer['actual_passing_baseline_audit'],offer['actual_passing_baseline_audit_sha256'])
assert audit['status']=='passed' and audit['proof_file_count']==1089
assert all(r['exit_code']==0 for r in audit['checks'])
protected=read(HERE/'original-tmp/foundations-future22-tmp-proof-index-v1.json')['held_checkpoint21_assets_exact']
for n,h in protected.items(): assert sha(ROOT/n)==h,n
for n,r in selection['proof_files'].items(): assert sha(ROOT/n)==r['sha256'],n
assert len(selection['proof_files'])==1089
for field in ['exact_source_reviews_sha256','canonical_source_peer_bindings_sha256','actual_canonical_execution_records_sha256']:
 for n,h in offer[field].items(): assert sha(ROOT/n)==h,n
original_rows={}
original_times={}
for n,h in offer['exact_source_reviews_sha256'].items():
 review=read(ROOT/n)
 assert sha(Path('/tmp')/Path(n).name)==h
 original_times[n]=review['reviewed_at_utc']
 for r in review['material_units']:
  assert r['source_unit_key'] not in original_rows
  assert r['entire_inventory_record']==units[r['source_unit_key']]
  assert r['material_status']=='proved' and r['whole_unit_approved'] and not r['missing_clauses']
  original_rows[r['source_unit_key']]=(r,n,h,review['reviewed_at_utc'])
assert len(original_rows)==16
interface={r['source_unit_key']:r for r in binding['material_units']}
assert set(interface)==set(original_rows)
approved=set(interface)
newclaims=[]
for key,r in interface.items():
 original,n,h,time=original_rows[key]
 assert r['original_unit_row']==original and r['original_review']==n and r['original_review_sha256']==h and r['original_reviewed_at_utc']==time
 assert r['exact_current48_inventory_record']==units[key]
 old=[c for c in base['material_claims'] if key in c['source_unit_keys']]
 assert r['original_current21_claims']==old
 assert r['retained_original_proved_or_nonformal_claims']==[c for c in old if c['status']!='pending']
 assert r['removed_pending_clauses']==[c for c in old if c['status']=='pending']
 claim=r['new_candidate_claim']; newclaims.append(claim)
 assert claim['source_unit_keys']==[key] and claim['status']=='proved' and claim['remaining_gaps']==[]
 for field in ['source','locator','source_text','source_sha256']: assert claim[field]==units[key][field]
 assert claim['source_text_sha256']==units[key]['text_sha256']
 assert claim['lean_declarations']==original['lean_declarations'] and claim['hypotheses']==original['hypotheses']
 assert claim['statement_in_prose']==units[key]['source_text']
 assert original['per_unit_reason'] in claim['correspondence']
 assert n in claim['correspondence'] and r['canonical_peer'] in claim['correspondence']
 assert sha(ROOT/r['canonical_peer'])==r['canonical_peer_sha256']
 peer=read(ROOT/r['canonical_peer'])
 if 'material_units' in peer: assert original in peer['material_units']
 else:
  item=next(x for x in peer['exact_literal_decision_bindings'] if x['source_unit_key']==key)
  assert item['original_unit_decision_sha256']==fp(original)
retained=[c for c in base['material_claims'] if not(set(c['source_unit_keys'])&approved and c['status']=='pending')]
assert candidate['material_claims']==retained+newclaims
assert all(c in candidate['material_claims'] for c in base['material_claims'] if c['status']!='pending')
assert candidate['exercises']==base['exercises'] and len(base['exercises'])==119
allowed={'material_claims','proof_files','proof_sha256','counts','limits','current22_material_mapping'}
assert {k:v for k,v in candidate.items() if k not in allowed}=={k:v for k,v in base.items() if k not in allowed}
assert candidate['limits'][:-1]==base['limits']
assert 'aggregate22' in candidate['limits'][-1]
assert {k:v for k,v in candidate['counts'].items() if k!='material_claim_statuses'}=={k:v for k,v in base['counts'].items() if k!='material_claim_statuses'}
assert candidate['counts']['material_claim_statuses']==dict(collections.Counter(c['status'] for c in candidate['material_claims']))
new=offer['proof_files']; assert len(new)==4
referenced={ 'verification/lean/SafeLearning/'+name.split('.')[1]+'.lean' for r in original_rows.values() for name in r[0]['lean_declarations'] }
assert set(candidate['proof_files'])==set(base['proof_files'])|set(new)|referenced
allnames=set(); theorem_count=0; pair_count=0
for n in candidate['proof_files']:
 h=sha(ROOT/n); assert candidate['proof_sha256'][n]==h
 decls=declarations((ROOT/n).read_text()); allnames.update(r['name'] for r in decls)
 if n in new:
  assert new[n]['sha256']==h and n not in selection['proof_files']
  theorem_count+=sum(r['kind'] in {'theorem','lemma'} for r in decls)
  assert sha(HERE/'sources'/(Path(n).stem+'-source-v1.lean'))==h
  assert len(new[n]['evidence_sha256'])==2
  for record_name,record_hash in new[n]['evidence_sha256'].items():
   rec=checked(record_name,record_hash); pair_count+=1
   assert rec['exit_code']==0 and rec['source']==n
   assert rec['source_sha256_before']==rec['source_sha256_after']==h
   assert sha(ROOT/rec['log'])==rec['log_sha256']
   assert rec['actual_workdir']==str(ROOT/'verification/lean')
   wanted=['lake','build','SafeLearning.'+Path(n).stem] if 'named-build' in record_name else ['lake','env','lean','SafeLearning/'+Path(n).name]
   assert rec['command']==wanted
   assert rec['elapsed_seconds']>=0 and rec['finished_at_utc']>=rec['started_at_utc']
 else: assert selection['proof_files'][n]['sha256']==h
assert theorem_count==36 and pair_count==8
assert all(set(r[0]['lean_declarations'])<=allnames for r in original_rows.values())
assert offer['new_theorem_or_lemma_count']==36 and offer['coverage_complete'] is False
def physical(ledger):
 statuses=collections.defaultdict(set)
 for c in ledger['material_claims']:
  for k in c['source_unit_keys']: statuses[k].add(c['status'])
 counts=collections.Counter('pending' if 'pending' in ss else 'not_a_formal_claim' if ss=={'not_a_formal_claim'} else 'proved' for ss in statuses.values())
 return {'total':len(statuses),'whole_proved':counts['proved'],'nonformal':counts['not_a_formal_claim'],'whole_pending':counts['pending']}
assert physical(base)==binding['physical_before']
assert physical(candidate)==binding['physical_after']==offer['material_counts']
assert physical(base)['whole_pending']==501 and physical(candidate)['whole_pending']==485
history=checked(offer['original_tmp_history_manifest'],offer['original_tmp_history_manifest_sha256'])
for row in history['copies']:
 assert sha(ROOT/row['canonical_byte_copy'])==row['canonical_byte_copy_sha256']==row['original_sha256']
 assert sha(row['original'])==row['original_sha256']
for name,h in protected.items(): assert sha(ROOT/name)==h
out=HERE/'foundations-source48-candidate22-independent-modules-confirmation-v2.json'
result={'status':'independent_exact_source48_foundation22_candidate_mapping_confirmation_passed','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checker':str(Path(__file__)),'checker_sha256':sha(__file__),'candidate_ledger':offer['mapped_ledger'],'candidate_ledger_sha256':sha(ROOT/offer['mapped_ledger']),'interface_binding':offer['material22_exact_interface_binding'],'interface_binding_sha256':sha(ROOT/offer['material22_exact_interface_binding']),'draft_offer':'book/coverage/checks/foundations-future22/foundations-source48-integration-offer22-draft-v1.json','draft_offer_sha256':sha(HERE/'foundations-source48-integration-offer22-draft-v1.json'),'held21_ledger':offer['held21_ledger'],'held21_ledger_sha256':sha(ROOT/offer['held21_ledger']),'inventory':offer['current_inventory'],'inventory_sha256':sha(ROOT/offer['current_inventory']),'original_review_times_preserved':original_times,'checks':{'all119_exercise_bodies_unchanged':True,'all_earlier_proved_atoms_retained':True,'only16_complete_literal_keys_replace_own_pending_clauses':True,'all_other_material_bodies_unchanged':True,'four_new_sources_36_public_theorems':True,'eight_genuine_paired_actual_exit0_records':True,'all1089_selected21_sources_unchanged':True,'old_tmp_reviews_failures_and_sources_byte_preserved':True},'physical_before':physical(base),'physical_after':physical(candidate),'scope':'Independent mechanics confirmation of a separate candidate, relying on original complete literal semantic peers; no live owner ledger integration or fresh aggregate22 claim.','errors':[]}
with out.open('x') as f: f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'report':str(out.relative_to(ROOT)),'report_sha256':sha(out)}))
