from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules30-current79-provisional-v1');assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(v):p=path(v['file']);assert sha(p)==v['sha256'];return p
def read(p):return json.loads(Path(p).read_bytes())
def put(p,d):
 with Path(p).open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def literal(x):return {k:v for k,v in x.items() if k!='source_sha256'}
CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');assert sha(CTX)=='d06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737';ctx=read(CTX);held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']};assert all(sha(path(n))==h for n,h in held.items())
BASE=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json';assert sha(BASE)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d';old=read(BASE);cand=copy.deepcopy(old)
OLDINV=R/'book/coverage/inventory-after-correction65.json';INV=R/'book/coverage/inventory-after-correction79.json';a=read(OLDINV);b=read(INV);assert sha(INV)==sha(R/'book/coverage/inventory.json');scope=set(old['scope_pages'])
IP=Path('/tmp/modules-compiled-supply-inventory30-v7.json');assert sha(IP)=='a8243c63c9cef4699b67620258b459ec16821db855fc04c57b254bebf80dc4d1';inv=read(IP);families={f['id']:f for f in inv['families']}
PLAN=R/'book/coverage/checks/future30-core/current79-canonical-plan45-v2.json';assert sha(PLAN)=='4a2c2ab8e877d098f243562adc2112c116aa93062b40757c2d5e0cd57f90b09d';plan=read(PLAN)
namemod=R/'book/coverage/lean_names.py';assert sha(namemod)=='9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d';spec=importlib.util.spec_from_file_location('modules30_provisional_names',namemod);names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
rows={};allnames=[]
for fid,f in families.items():
 p=checked(f['compiled_source']);decl=names.declarations(p.read_text());assert decl==f['public_declarations'];theorems=[x['name'] for x in decl if x['kind'] in ['theorem','lemma']];assert len(theorems)==f['public_theorem_count'];match=[r for r in plan['sources'] if r['original_tmp_source']['sha256']==sha(p)];assert len(match)==1;row=match[0];assert row['public_declarations']==decl;rows[fid]=row;allnames+=theorems
 assert read(checked(f['actual_native']))['actual_exit_code']==0
assert len(rows)==15 and len(allnames)==len(set(allnames))==504 and sum(len(r['public_declarations']) for r in rows.values())==707 and not set(allnames)&set(old['declarations'])
peerpaths={fid:checked(f['full_semantic_peer']) for fid,f in families.items() if f['full_semantic_peer'] is not None}
MP=R/'book/coverage/checks/modules-future30/matrix53-independent-foundations-v1/modules-matrix53-full-source-provided-matrix-normal-eleven-components-independent-foundations30-closed-peer-v1.json';assert sha(MP)=='19696a80b81334d91b3d047e2f7b77cb7fab35b1823768ef7e56beef02f789a3';peerpaths['matrix_open_five_sample_obstruction']=MP
CP=checked(inv['distinct_exact_Chain49_whole_exercise_review']);S57=checked(inv['original_shelf57_intentional_gap_peer']);S83=checked(inv['shelf_actual_continuous_control_whole_composition_peer']);peers={fid:read(p) for fid,p in peerpaths.items()}
for d in peers.values():assert d['errors']==[] and d['status'].startswith('passed_')
assert read(CP)['errors']==read(S57)['errors']==read(S83)['errors']==[]
changed={};records={}
for section in ['exercises','material_source_units']:
 aa={x['key']:x for x in a[section] if x['source'] in scope};bb={x['key']:x for x in b[section] if x['source'] in scope};assert aa.keys()==bb.keys();changed[section]=[]
 for k in aa:
  if literal(aa[k])!=literal(bb[k]):changed[section].append(k);records[k]={'entire_historical65':aa[k],'entire_actual79':bb[k]}
assert len(changed['exercises'])==len(changed['material_source_units'])==7
SUP=Path('/tmp/modules-seven-unnumbered-qualifiers-root-offer30-v1.json');assert sha(SUP)=='5df8cb07cdf76e4997f80b57d1c4aeabf1402fbf4530cc724356ff2465fadca7';supply=read(SUP)
EX={x['key']:x for x in b['exercises']};UN={x['key']:x for x in b['material_source_units']};qual=[]
for offer in supply['individual_unnumbered_proposals']:
 p=checked(offer['unnumbered_proposal']);d=read(p);entire=d['entire_current_and_proposed_literal_records'];assert isinstance(entire,dict)
 for key,pair in entire.items():
  actual=EX.get(key,UN.get(key));assert actual is not None and literal(pair['entire_proposed'])==literal(actual)
 qual.append({'id':offer['id'],'original_proposal':ref(p),'original_narrow_peer':offer['independent_narrow_full_literal_parser_peer'],'original_full_math_peer':offer['independent_full_mathematical_peer'],'actual79_entire_proposed_literal_identity_verified_keys':list(entire),'current_page_hash_is_cumulative79_not_individual65_candidate':True,'original_false_whole_status_and_reader_time_preserved_in_exact_original_peer':True})
B.mkdir();IDENT=B/'modules30-source65-to79-entire-owned-literal-identity-v1.json';put(IDENT,{'status':'passed_exact_actual79_owned_literals_identity_with_seven_approved_exercise_and_unit_changes','historical_inventory':ref(OLDINV),'actual_inventory':ref(INV),'original_installed29_owner':ref(BASE),'actual_source79_application':ctx['source79_application'],'actual_source79_application_execution':ctx['source79_application_execution'],'owned_exercise_count':len(EX.keys() & {e['inventory_key'] for e in old['exercises']}),'owned_material_source_unit_count':len({x['key'] for x in b['material_source_units'] if x['source'] in scope}),'changed_keys':changed,'entire_changed_records':records,'all_other_owned_records_entire_equal_except_whole_page_source_fingerprint':True,'seven_exact_original_proposed_literals_individually_equal_actual79':qual,'original_semantic_body_times_not_reinterpreted':True,'coverage_complete':False})
patches=[]
def change(parts,v):
 d=cand
 for k in parts[:-1]:d=d[k]
 k=parts[-1];exists=k in d if isinstance(d,dict) else True;before=copy.deepcopy(d[k]) if exists else None
 if exists and before==v:return
 patches.append({'path':parts,'existed':exists,'before':before});d[k]=copy.deepcopy(v)
def theorem_names(fid):return [x['name'] for x in rows[fid]['public_declarations'] if x['kind'] in ['theorem','lemma']]
change(['source_sha256'],{n:b['source_sha256'][n] for n in old['scope_pages']});change(['chapter_fragment_sha256'],{n:sha(R/n) for n in old['chapter_fragment_sha256']});change(['current_inventory'],INV.relative_to(R).as_posix());change(['current_inventory_sha256'],sha(INV));change(['current_identity_binding_validation'],{'status':'actual79_isolated_mapping_identity_verified_canonical_pair_and_installation_pending','inventory':ref(INV),'identity':ref(IDENT),'canonical_owner_integrated':False});change(['inventory_identity_rebase79'],{'status':'prepared_exact_original65_to_actual79_owned_literal_rebase','actual_full_identity':ref(IDENT),'original_installed29_owner':ref(BASE),'source79_application_precedes_candidate':True})
wholeex={
'lipsdp.html::exercise-17':(['coupled_tanh'],peerpaths['coupled_tanh']),
'NN_UNUSED':([],None),
'nn-in-the-loop.html#book-m14-b2':(['delayed_square'],peerpaths['delayed_square']),
 'toolkit-gp.html#book-m3-b1':(['physical_GP'],peerpaths['physical_GP']),
 'toolkit-gp.html#book-m3-b2':(['physical_GP'],peerpaths['physical_GP']),
 'viability.html#book-m7-b2':(['thermal'],peerpaths['thermal']),
 'viability.html::exercise-18':(['physical_Chain53'],CP),
 'viability.html::exercise-20':(['entropy'],peerpaths['entropy']),
 'viability.html::exercise-17':(['shelf_threshold_rounding','shelf_global_shape','shelf_actual_continuous_control_association'],S83)};del wholeex['NN_UNUSED'];assert len(wholeex)==8
unitmap={}
for fid,nums,page in [('coupled_tanh',[1297,1301,1302,1303,1304],'lipsdp'),('physical_GP',[940,944,948,955,959],'toolkit-gp'),('delayed_square',[909,916,920],'nn-in-the-loop'),('thermal',[838,839,864,871,875],'viability'),('entropy',[1167,1171,1173,1174],'viability'),('physical_Chain53',[1135,1139,1141,1143,1144],'viability')]:
 for num in nums:unitmap[f'{page}.html::node-{num}']=([fid],CP if fid=='physical_Chain53' else peerpaths[fid])
for num in [1122,1131,1126,1130]:unitmap[f'viability.html::node-{num}']=(['shelf_threshold_rounding','shelf_global_shape','shelf_actual_continuous_control_association'],S83 if num==1130 else S57)
unitmap['viability.html::node-1153']=(['finite_DP2','actual_expected_duality31'],peerpaths['actual_expected_duality31']);assert len(unitmap)==32
assert peers['coupled_tanh']['exercise_whole_approved'] is True and set(peers['coupled_tanh']['whole_material_approved'])=={k for k in unitmap if k.startswith('lipsdp')}
for fid in ['physical_GP','delayed_square','thermal','entropy']:
 actualkeys={k for k,(fids,p) in unitmap.items() if fids==[fid]};assert actualkeys==set(peers[fid]['current_whole_material_approved']+peers[fid]['prospective_corrected_material_whole_approved'])
assert peers['actual_expected_duality31']['whole_current_exercise_approved'] is False and peers['actual_expected_duality31']['whole_prospective_corrected_exercise_approved'] is False
assert peers['actual_expected_duality31']['individual_decisions'][1]['key']=='viability.html::node-1153' and peers['actual_expected_duality31']['individual_decisions'][1]['current_whole_approved'] is True
exass=[];matass=[];gapass=[]
def support(fids):return [n for fid in fids for n in theorem_names(fid)]
def oldhash(d):return hashlib.sha256(json.dumps(d,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
def newclaim(row,fids,peer,key,whole):
 z=copy.deepcopy(row);z.update({'status':'proved','lean_declarations':support(fids),'remaining_gaps':[],'independent_source_review':ref(peer),'hypotheses':['Exact actual79 source/model domains and independently approved hypotheses in the full source peer remain explicit; source-supplied data and confidence-envelope events remain assumptions.'],'correspondence':'This exact '+('whole literal and each requested clause' if whole else 'bounded requirement component')+' is discharged in the unchanged full mathematical peer and mapped actual sources. The fresh identity binds the original current/prospective literal to actual Source79; old original decision/body/time is preserved.','reviewed_owner30_transition':{'original_owner':ref(BASE),'original_claim_id':row['id'],'original_claim_canonical_json_sha256':oldhash(row),'actual79_identity':ref(IDENT),'whole_scope_approval':whole,'original_full_semantic_peer':ref(peer),'canonical_pair_pending':True}});return z
for i,e in enumerate(cand['exercises']):
 key=e['inventory_key'];actual=EX[key];change(['exercises',i,'source_sha256'],actual['source_sha256'])
 if key in changed['exercises']:change(['exercises',i,'source_text_sha256'],actual['text_sha256'])
 if key not in wholeex:continue
 fids,p=wholeex[key];pending=[j for j,z in enumerate(e['claims']) if z['status']=='pending'];assert pending
 for j in pending:
  row=newclaim(e['claims'][j],fids,p,key,True);change(['exercises',i,'claims',j],row);exass.append({'exercise':key,'claim_id':row['id'],'declarations':row['lean_declarations'],'peer':ref(p)})
 for j,z in enumerate(e['claims']):
  if z['status']=='proved' and 'proved-component-' in z['id'] and z['remaining_gaps']:
   prior=copy.deepcopy(z['remaining_gaps']);reason='The actual derived roots/convergence/roundings close the independent prior stability gaps.' if fids==['delayed_square'] else 'Actual full all-history Bellman/infinite discounted-series and optimal-action results close the old all-policy gap.' if fids==['thermal'] else 'Actual arbitrary-n inverse/action/posterior and unique linear system close the old scalar-to-matrix gap.'
   if key=='toolkit-gp.html#book-m3-b2':reason='The exact old probability note remains true: the exercise explicitly assumes its posterior-envelope event. This transition removes an obsolete completion-gap slot, does not prove that event, and retains the exact original note here and all old hypotheses/prose/declarations/correspondence/time unchanged.'
   gapass.append({'exercise':key,'claim_id':z['id'],'only_original_remaining_gaps_list_changed':True,'original_remaining_gaps':prior,'completion_support_declarations':support(fids),'completion_full_scope_peer':ref(p),'actual79_identity':ref(IDENT),'reason':reason,'source_assumed_probability_event_not_derived':key=='toolkit-gp.html#book-m3-b2'});change(['exercises',i,'claims',j,'remaining_gaps'],[])
 change(['exercises',i,'status'],'complete_math');change(['exercises',i,'entire_literal_closure30'],{'whole_exercise_approved':True,'remaining_gaps':[],'entire_actual79_record':actual,'original_full_semantic_peer':ref(p),'actual79_identity':ref(IDENT),'canonical_pair_and_installation_pending':True})
for key,(fids,p) in unitmap.items():
 idx=[i for i,z in enumerate(cand['material_claims']) if z['status']=='pending' and z.get('source_unit_keys')==[key]];assert len(idx)==1,(key,len(idx));i=idx[0];row=newclaim(cand['material_claims'][i],fids,p,key,True);row.update({'statement_in_prose':UN[key]['source_text'],'kind':'independently_reviewed_complete_mathematical_source_unit','entire_original_literal_decision_and_review_time':{'source_unit_key':key,'entire_actual79_record':UN[key],'whole_literal_approved':True,'original_full_semantic_peer':ref(p),'original_body_and_review_time_unchanged':True,'actual79_identity':ref(IDENT)}});change(['material_claims',i],row);matass.append({'key':key,'index':i,'claim_id':row['id'],'declarations':row['lean_declarations'],'peer':ref(p)})
# Source78 changed the complete update paragraph, while its unproved generic associations stay pending.
for i,z in enumerate(cand['material_claims']):
 if z.get('source_unit_keys')==['viability.html::node-1162'] and z['status']=='pending':change(['material_claims',i,'statement_in_prose'],UN['viability.html::node-1162']['source_text'])
component_requirements=[('viability.html::exercise-19','requirement-3',['finite_DP2','actual_expected_duality31'],peerpaths['actual_expected_duality31']),('verification.html::exercise-19','requirement-2',['scenario_exact_samples_and_scalar_infeasibility'],peerpaths['scenario_exact_samples_and_scalar_infeasibility']),('verification.html::exercise-19','requirement-3',['scenario_exact_samples_and_scalar_infeasibility'],peerpaths['scenario_exact_samples_and_scalar_infeasibility'])]
for key,suffix,fids,p in component_requirements:
 i=next(i for i,e in enumerate(cand['exercises']) if e['inventory_key']==key);e=cand['exercises'][i];j=next(j for j,z in enumerate(e['claims']) if z['id'].endswith('::'+suffix));assert e['claims'][j]['status']=='pending';row=newclaim(e['claims'][j],fids,p,key,False);change(['exercises',i,'claims',j],row);change(['exercises',i,'status'],'partial');exass.append({'exercise':key,'claim_id':row['id'],'component_only':True,'declarations':row['lean_declarations'],'peer':ref(p)})
assert len(gapass)==5
ASSOC=B/'modules30-original-inherited-gap-and-component-associations-v1.json';put(ASSOC,{'status':'isolated_exact_five_original_gap_slot_completions_and_approved_component_associations_pending_independent_final_mapping','original_owner':ref(BASE),'actual79_identity':ref(IDENT),'inherited_gap_list_only_changes':gapass,'component_only_exercise_requirements':component_requirements,'all15_compiled_family_full_semantic_associations':[{'family':fid,'source':f['compiled_source'],'original_actual_native':f['actual_native'],'full_semantic_peer':ref(peerpaths[fid]),'scope_pointer':f['exact_peer_scope_decisions'],'whole_scope_not_inferred_from_component':True} for fid,f in families.items()],'matrix53_original42_scope_and_new11_peer':ref(MP),'whole_duality_7_5_remains_false':True,'whole_scenario_15_5_remains_false':True,'all_historical_statement_hypotheses_declarations_correspondence_and_times_unchanged_for_proved_claims':True,'coverage_complete':False})
newproof={}
for fid,r in rows.items():
 ns=theorem_names(fid);meta={'sha256':r['original_tmp_source']['sha256'],'selection_scope':'direct_reviewed_reference_pending_actual_canonical_pair','standalone_compile_status':'pending_actual_root_canonical_pair','declarations':ns,'public_theorem_names':ns,'mapped_named_declarations':ns,'theorem_count':len(ns),'public_declarations':r['public_declarations'],'original_tmp_source':r['original_tmp_source'],'original_actual_tmp_trial':r['original_actual_tmp_trial'],'independent_source_review':ref(peerpaths[fid]),'actual_pair':None,'canonical_pair_pending':True};newproof[r['canonical_source']]=meta;change(['proof_files',r['canonical_source']],meta)
change(['declarations'],old['declarations']+allnames);counts=copy.deepcopy(old['counts']);counts['exercise_status']=dict(Counter(e['status'] for e in cand['exercises']));counts['exercise_claim_status']=dict(Counter(z['status'] for e in cand['exercises'] for z in e['claims']));counts['material_claim_status']=dict(Counter(z['status'] for z in cand['material_claims']));counts['new_declarations']=len(cand['declarations']);change(['counts'],counts)
change(['reviewed_work_integration30_current79_candidate'],{'status':'prepared_isolated_actual79_eight_whole_exercises32_whole_units_and_bounded_components_with_actual_pairs_pending','author_prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_installed29_owner':ref(BASE),'actual79_identity':ref(IDENT),'whole_exercises':list(wholeex),'whole_material_units':list(unitmap),'component_only_exercise_requirements':[{'exercise':x[0],'claim_suffix':x[1]} for x in component_requirements],'new_sources':list(newproof),'new_public_theorem_count':len(allnames),'new_public_declaration_count':707,'original_gap_and_component_associations':ref(ASSOC),'every_old_proved_body_time_claim_id_proof_metadata_and_decl_prefix_retained':True,'whole_duality7_5_and_scenario15_5_approved':False,'canonical_pair_pending':True,'current_owner_canonical_selection_publication_written':False,'coverage_complete':False})
CAND=B/'modules30-current79-provisional-candidate-v1.json';put(CAND,cand)
rev=copy.deepcopy(cand)
for item in reversed(patches):
 d=rev
 for k in item['path'][:-1]:d=d[k]
 if item['existed']:d[item['path'][-1]]=copy.deepcopy(item['before'])
 else:del d[item['path'][-1]]
assert rev==old and (json.dumps(rev,indent=2,ensure_ascii=False)+'\n').encode()==BASE.read_bytes()
assert cand['proof_files'].keys() >= old['proof_files'].keys() and all(cand['proof_files'][k]==v for k,v in old['proof_files'].items()) and cand['declarations'][:len(old['declarations'])]==old['declarations']
INVERSE=B/'modules30-current79-exact-forward-inverse-interface-v1.json';put(INVERSE,{'status':'exact_full_original_owner29_byte_inverse_verified_pending_final_independent_mapping','base':ref(BASE),'candidate':ref(CAND),'restore_patches_in_reverse_order':patches,'exact_inverse_restores_entire_original_raw29':True,'new_exercise_claim_associations':exass,'new_material_claim_associations':matass,'five_inherited_gap_slot_associations':ref(ASSOC),'all_other_old_claim_prose_hypotheses_decl_correspondence_metadata_history_times_unchanged':True,'old502_proof_metadata_rows_and3484_declaration_prefix_exact':True,'actual_canonical_receipts_pending_not_invented':True,'coverage_complete':False})
O=B/'modules30-current79-provisional-offer-v1.json';put(O,{'status':'isolated_modules30_actual79_mapping_pending_actual_pairs_and_independent_final_mapping','errors':[],'candidate':ref(CAND),'inventory':ref(INV),'inventory_sha256':sha(INV),'source_sha256':cand['source_sha256'],'identity_sidecar':ref(IDENT),'exact_inverse_interface':ref(INVERSE),'completion_component_associations':ref(ASSOC),'proof_files':newproof,'canonical_plan':ref(PLAN),'original_owner':ref(BASE),'whole_exercises':list(wholeex),'whole_material_keys':list(unitmap),'component_only_exercise_requirements':[{'exercise':x[0],'claim_suffix':x[1]} for x in component_requirements],'counts':counts,'actual_canonical_pairs_pending':True,'installation_ready':False,'live_changes':False,'coverage_complete':False})
assert all(sha(path(n))==h for n,h in held.items());print(json.dumps({'candidate':ref(CAND),'offer':ref(O),'inverse':ref(INVERSE),'identity':ref(IDENT),'associations':ref(ASSOC),'counts':counts,'new_sources':len(newproof),'new_theorems':len(allnames),'whole_exercises':len(wholeex),'whole_units':len(unitmap),'patches':len(patches)}))
