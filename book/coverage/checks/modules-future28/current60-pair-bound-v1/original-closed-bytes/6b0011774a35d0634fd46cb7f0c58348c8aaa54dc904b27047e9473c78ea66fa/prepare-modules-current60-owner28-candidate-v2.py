from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,collections,copy
ROOT=Path('/home/oxrexkevin/SafetyBased')
OLD=Path('/tmp/modules-current60-owner28-candidate-v1/modules-current60-owner28-pending-canonical-pairs.json')
OLDREPORT=Path('/tmp/modules-current60-owner28-candidate-v1/modules-current60-owner28-candidate-preparation-v1.json')
OLDNATIVE=Path('/tmp/modules-current60-owner28-candidate-preparation-actual-v1.json')
PEER=Path('/tmp/modules-sensor-commissioning17-independent-foundations28-v2.json')
SOURCE=Path('/tmp/CompleteModulesSensorCommissioning28-draft-v4.lean')
OUTDIR=Path('/tmp/modules-current60-owner28-candidate-v2');assert not OUTDIR.exists();OUTDIR.mkdir()
CAND=OUTDIR/'modules-current60-owner28-five-proof-pending-canonical-pairs.json'
REPORT=OUTDIR/'modules-current60-owner28-candidate-preparation-v2.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def object_sha(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
assert sha(OLD)=='bd53fcbb231599c61b1e48737a43321d0a638c1541ab4b5cfa729e61e2172cda'
assert sha(OLDREPORT)=='4a3133c8c8b4eed61d9f72443480b604aff756a5e888f34ae7b3b29268dceb1a'
assert sha(PEER)=='c9b176bd7619152f68fe1437ba5ebdcffa0595b1da2947412b63030c2be19d09'
assert sha(SOURCE)=='bb74fce90694edb80f78e00d12582c7580314802a622d704271f6b876e7a7544'
assert sha(ROOT/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
oldreport=json.loads(OLDREPORT.read_bytes());oldnative=json.loads(OLDNATIVE.read_bytes())
assert oldreport['candidate']==ref(OLD) and oldnative['actual_exit_code']==0 and oldnative['protection_errors']==[]
O=json.loads(OLD.read_bytes());prior=copy.deepcopy(O)
BASE=json.loads((ROOT/'book/coverage/modules.json').read_bytes());baseclaims={c['id']:c for c in BASE['material_claims']}
peer=json.loads(PEER.read_bytes());assert peer['errors']==[] and peer['public_theorem_count']==17
assert peer['whole976_sharp_lipschitz_constant_approved'] is False
I=json.loads((ROOT/'book/coverage/inventory.json').read_bytes()); units={u['key']:u for u in I['material_source_units']}
changes=[]
for r in peer['material_units']:
 key=r['inventory_key'];assert r['whole_unit_approved'] is True and r['missing_clauses']==[]
 assert r['entire_current60_inventory_record']==units[key]
 claim=next(c for c in O['material_claims'] if c['id']==key+'::claim-review')
 assert claim['status']=='pending' and claim['statement_in_prose']==units[key]['source_text']
 original=baseclaims[claim['id']]
 claim.update({'status':'proved','lean_declarations':r['lean_declarations'],'hypotheses':r['hypotheses'],'correspondence':r['mathematical_correspondence'],'remaining_gaps':[],'independent_source_review':ref(PEER),'whole_current60_source_unit_approved':True,'actual_current60_text_sha256':units[key]['text_sha256']})
 claim['reviewed_owner28_transition']={'original_owner':oldreport['original_owner'],'original_claim_id':original['id'],'original_claim_canonical_json_sha256':object_sha(original),'whole_current60_full_literal_peer':ref(PEER),'canonical_pair_pending':True}
 changes.append({'id':claim['id'],'original_status':'pending','candidate_status':'proved','actual_current60_text_sha256':units[key]['text_sha256']})
assert len(changes)==2 and {r['id'] for r in changes}=={'lipsdp.html::node-972::claim-review','lipsdp.html::node-974::claim-review'}
s=SOURCE.read_text();namespace='SafeLearning.CompleteModulesSensorCommissioning28';destination='verification/lean/SafeLearning/CompleteModulesSensorCommissioning28.lean'
names=[];new=[]
for m in re.finditer(r'^theorem ([A-Za-z0-9_]+)',s,re.M):
 name=namespace+'.'+m.group(1);names.append(name);end=s.find(':=',m.end());assert end!=-1
 new.append({'name':name,'file':destination,'line':s.count('\n',0,m.start())+1,'statement':s[m.start():end].rstrip()})
assert len(new)==17 and destination not in O['proof_files']
O['declarations'].extend(new)
O['proof_files'][destination]={'sha256':sha(SOURCE),'selection_scope':'direct_reviewed_reference','standalone_compile_status':'pending_actual_root_canonical_pairs','declarations':names,'original_tmp_source':ref(SOURCE),'original_tmp_trial':ref('/tmp/modules-sensor-commissioning28-trial4.json'),'canonical_pair_evidence_directory_assigned_by_root':'book/coverage/checks/future28-core/current60-canonical-pairs-v1/','canonical_paired_evidence_not_yet_available':True}
O['counts']={'exercises':len(O['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in O['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in O['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in O['material_claims'])),'new_declarations':len(O['declarations'])}
assert O['counts']['material_claim_status']=={'not_a_formal_claim':536,'pending':3583,'proved':1081}
assert O['counts']['new_declarations']==3412
assert O['exercises']==prior['exercises'] and O['declarations'][:len(prior['declarations'])]==prior['declarations']
assert all(O['proof_files'][k]==v for k,v in prior['proof_files'].items())
changedids={r['id'] for r in changes}
assert all(a==b for a,b in zip(prior['material_claims'],O['material_claims']) if a['id'] not in changedids)
O['reviewed_work_integration28_current60_candidate_v2']={'status':'prepared_four_whole_exercises_and26_material_units_153_public_declarations_pending_actual_five_canonical_pairs','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_v1_candidate':ref(OLD),'original_v1_preparation':ref(OLDREPORT),'original_v1_actual_preparation':ref(OLDNATIVE),'new_full17_commissioning_whole972_974_peer':ref(PEER),'changed_only_two_original_pending_material_claims':changes,'added_only17_public_declarations':True,'new_source':ref(SOURCE),'canonical_source':destination,'all_five_actual_canonical_pairs_pending':True,'original_v1_findings_body_time_and_data_preserved':True,'whole976_or_other_source_or_live_owner_or_selection_or_audit_or_publication_changed':False}
O['generated_at_utc']=datetime.now(timezone.utc).isoformat()
CAND.write_text(json.dumps(O,indent=2,ensure_ascii=False)+'\n')
report={'status':'prepared_current60_owner28_five_proof_candidate_with_explicit_pending_canonical_pairs','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(CAND),'identity':oldreport['identity'],'original_owner':oldreport['original_owner'],'actual_inventory60':ref(ROOT/'book/coverage/inventory.json'),'original_v1_candidate':ref(OLD),'original_v1_preparation':ref(OLDREPORT),'original_v1_actual_preparation':ref(OLDNATIVE),'independent_full17_commissioning_peer':ref(PEER),'counts':O['counts'],'pending_pair_count':5,'new_public_declaration_count':153,'whole_exercises_proposed':4,'whole_material_units_proposed':26,'old_proof_metadata_and_original_declarations_retained_exact':True,'all_original_claim_ids_and_history_fields_retained':True,'canonical_pair_evidence_or_kernel_or_owner_application_or_aggregate_or_publication_claimed':False,'only_two_whole_approved_claims_and17_public_declarations_added_to_v1':True,'changed_claims':changes}
REPORT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(ref(REPORT)));print(json.dumps(report['counts']))
