from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,sys
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future25-core'
OUT=B/'core25-material-candidate-independent-applied-confirmation-v1.json'
H=lambda p:hashlib.sha256((Path(p) if Path(p).is_absolute() else R/p).read_bytes()).hexdigest()
J=lambda p:json.loads((Path(p) if Path(p).is_absolute() else R/p).read_text())
def ref(p):return {'file':str(Path(p).relative_to(R)) if Path(p).is_absolute() and Path(p).is_relative_to(R) else str(p),'sha256':H(p)}
def bound(r):assert H(r['file'])==r['sha256'],r['file'];return J(r['file'])
assert not OUT.exists()
original='book/coverage/core.json';origsha='47b676890af40692cc1161c5472b461397b224e1a3724ee6990f03bb64d56bf5'
assert H(original)==origsha
old=J(original);candidate='book/coverage/checks/future25-core/core25-source52-material-candidate-v1.json';c=J(candidate);integrity=J('book/coverage/checks/future25-core/core25-source52-material-candidate-integrity-v1.json');assert integrity['candidate']==ref(candidate)
assert H('book/coverage/inventory.json')==H('book/coverage/inventory-after-correction52.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
inv=J('book/coverage/inventory.json');units={u['key']:u for u in inv['material_source_units']}
manifest=J('reports/full-coverage/checkpoint-24-manifest.json');selection=bound({'file':manifest['selection'],'sha256':manifest['selection_sha256']});assert len(selection['proof_files'])==1144
pre={p:H(p) for p in ['book/coverage/'+o+'.json' for o in ['core','modules','foundations','applied','applied-promotions']]+['book/coverage/inventory.json']+list(inv['source_sha256'])}
for p,h in inv['source_sha256'].items():assert H(p)==h,p
ready=bound(integrity['canonical_readiness']);src=ready['source'];assert H(src['file'])==H(ready['source_snapshot']['file'])==src['sha256']
assert ready['status']=='passed_actual_canonical_pair_unselected_future25';assert src['file'] not in selection['proof_files'] and src['file'] not in old['proof_files']
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
newnames=[d['name'] for d in declarations((R/src['file']).read_text()) if d['kind'] in ['theorem','lemma']];assert len(newnames)==ready['public_theorem_count']==7
actual=[]
for p in ready['actual_canonical_pair']:
 a=bound(p);assert a['exit_code']==p['actual_exit_code']==0 and a['status']=='passed';assert a['source']==src['file'] and a['source_sha256_before']==a['source_sha256_after']==src['sha256']
 assert a['actual_workdir']==str(R/'verification/lean') and H(a['log'])==a['log_sha256']==p['log']['sha256'];assert p['log']['file']==a['log']
 assert a['command'] in [['lake','env','lean','SafeLearning/CompleteBarrierControlMaterial25.lean'],['lake','build','SafeLearning.CompleteBarrierControlMaterial25']]
 assert a['checked_at_utc'] and a['elapsed_seconds']>=0;actual.append({'reference':ref(p['file']),'entire_actual_original_record':a})
for orig,r in ready['original_TMP_byte_copies'].items():assert H(orig)==H(r['file'])==r['sha256'],orig
binding=c['future25_material_candidate_binding'];assert binding['original_source52_owner']==ref(original) and binding['current_inventory']==ref('book/coverage/inventory.json')
assert binding['canonical_readiness']==integrity['canonical_readiness'] and binding['coverage_complete'] is False
approved={};peers=[]
for p in integrity['whole_source_reviews']:
 peer=bound(p);assert peer['errors']==[] and 'passed' in peer['status'];assert peer['reviewer']=='/root/applied_next' and peer['reviewed_at_utc'];peers.append(peer)
 for u in peer['material_units']:
  key=u['source_unit_key'];assert key not in approved;approved[key]=(u,p,peer['reviewed_at_utc'])
  assert u['whole_unit_approved'] is True and u['missing_clauses']==[] and u['entire_inventory_record']==units[key]
  assert H(units[key]['source'])==units[key]['source_sha256'];assert hashlib.sha256(units[key]['source_text'].encode()).hexdigest()==units[key]['text_sha256']
 for z in binding['original_review_identity_bindings']:
  if z['original_peer']==p:
   assert z['entire_original_peer_body_and_time']==peer;assert z['current_inventory']==ref('book/coverage/inventory.json');break
 else:raise AssertionError('missing exact identity binding')
assert len(approved)==7 and sum(u['material_status']=='proved' for u,p,t in approved.values())==2
assert c['exercises']==old['exercises'] and len(c['exercises'])==92 and c['counts']==old['counts']
assert c['proof_files']=={**old['proof_files'],src['file']:src['sha256']}
assert len(c['material_claims'])==len(old['material_claims'])==4147
base_names=set()
for p,z in selection['proof_files'].items():
 assert H(p)==z['sha256'],p
 base_names.update(d['name'] for d in declarations((R/p).read_text()))
changed=[];restored=copy.deepcopy(c)
for i,(a,b) in enumerate(zip(old['material_claims'],c['material_claims'])):
 keys=b['source_unit_keys']
 if len(keys)==1 and keys[0] in approved:
  key=keys[0];u,p,t=approved[key];assert b['original_source52_entire_pending_material_row']==a and a['status']=='pending'
  expected=copy.deepcopy(a);expected.update(kind='independently_reviewed_literal_material_unit',status=u['material_status'],lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_unit_reason'],remaining_gaps=[],independent_review={'source':p['file'],'sha256':p['sha256'],'original_review_time':t},original_complete_literal_review_record=copy.deepcopy(u),original_source52_entire_pending_material_row=copy.deepcopy(a))
  assert expected==b,key;assert set(b['lean_declarations'])<=base_names|set(newnames);assert b['source_text']==units[key]['source_text']
  if b['status']=='not_a_formal_claim':assert b['lean_declarations']==b['hypotheses']==[]
  changed.append(key);restored['material_claims'][i]=copy.deepcopy(a)
 else:assert a==b
assert set(changed)==set(approved)==set(integrity['whole_material_units'])
del restored['future25_material_candidate_binding'];del restored['proof_files'][src['file']];restored['generated_at_utc']=old['generated_at_utc'];assert restored==old
actualprep='reports/full-coverage/root-core25-candidate-preparation-execution-v1.json';a=J(actualprep);assert a['status']=='passed' and a['actual_exit_code']==0 and a['actual_command']==['python3','book/coverage/checks/prepare_root_core25_material_candidate_v1.py'];assert a['actual_workdir']==str(R)
assert H(a['log'])==a['log_sha256'];assert a['helper_sha256_before']==a['helper_sha256_after']=={'book/coverage/checks/prepare_root_core25_material_candidate_v1.py':H('book/coverage/checks/prepare_root_core25_material_candidate_v1.py')};assert a['selection_sha256']==manifest['selection_sha256']
audit=bound(binding['actual_verified24_audit']);assert audit['status']=='passed' and audit['proof_file_count']==1144 and audit['theorem_count']==9279 and all(x['exit_code']==0 for x in audit['checks'])
assert len(manifest['frozen_inputs_sha256'])==40485
for p,h in manifest['frozen_inputs_sha256'].items():assert H(str(Path(manifest['snapshot'])/p))==h,p
for p,h in pre.items():assert H(p)==h,p
r={'status':'passed_independent_isolated_core25_candidate_mechanics','errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(candidate),'original_owner':ref(original),'original_candidate_integrity':ref('book/coverage/checks/future25-core/core25-source52-material-candidate-integrity-v1.json'),'candidate_preparation_actual':ref(actualprep),'candidate_preparation_raw_log':ref(a['log']),'current_inventory':ref('book/coverage/inventory-after-correction52.json'),'canonical_source_and_snapshot':{'source':src,'snapshot':ready['source_snapshot']},'canonical_actual_records':actual,'original_whole_review_references':integrity['whole_source_reviews'],'entire_original_review_bodies_and_times':peers,'checked_material_keys':sorted(changed),'counts':{'exact_whole_exercise_bodies':92,'other_material_bodies':4140,'new_material_units':7,'new_proved_whole_units':2,'new_nonformal_whole_units':5,'prior_proof_metadata_rows':len(old['proof_files']),'new_proof_sources':1,'new_public_exports':7,'actual_zero_compiler_records':2,'protected_selected24_sources':1144,'protected_frozen24_inputs':40485},'scope':'Read-only exact candidate/source52 mapping and genuine source/record/history binding only. Original semantic decisions and times preserved unchanged; no new compiler, live owner write, global25, aggregate25 or publication execution.','checker':ref(__file__)}
OUT.write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','peer':ref(OUT)}))
