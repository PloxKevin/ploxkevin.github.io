from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import sys,json,hashlib,copy
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules29-current65-two-whole-candidate-v1');assert not B.exists();B.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(v):p=path(v['file']);assert sha(p)==v['sha256'];return p
def put(p,d):
 with Path(p).open('x')as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
CTX=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');assert sha(CTX)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';ctx=read(CTX);held={**ctx['pins_sha256'],**ctx['held_current_source_sha256']}
for n,h in held.items():assert sha(path(n))==h
BASE=R/'reports/full-coverage/checkpoint-28/book/coverage/modules.json';assert sha(BASE)==sha(R/'book/coverage/modules.json')=='1c91d42f7a720cbb486d7ca57778012681875d450b2e1779cd5be47c10aaa4e9';old=read(BASE);candidate=copy.deepcopy(old);OLDINV=R/'book/coverage/inventory-after-correction60.json';INV=R/'book/coverage/inventory-after-correction65.json';assert sha(INV)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68';a=read(OLDINV);b=read(INV);scope=set(old['scope_pages'])
changed={};records={}
for section in ['exercises','material_source_units']:
 aa={x['key']:x for x in a[section]if x['source']in scope};bb={x['key']:x for x in b[section]if x['source']in scope};assert aa.keys()==bb.keys();changed[section]=[]
 for k in aa:
  av={x:y for x,y in aa[k].items()if x!='source_sha256'};bv={x:y for x,y in bb[k].items()if x!='source_sha256'}
  if av!=bv:changed[section].append(k);records[k]={'entire_historical60':aa[k],'entire_actual65':bb[k]}
assert changed=={'exercises':['lipsdp.html::exercise-16','lipsdp.html::exercise-19'],'material_source_units':['lipsdp.html::node-1293','lipsdp.html::node-1328','lipsdp.html::node-1329']}
EX={x['key']:x for x in b['exercises']};UN={x['key']:x for x in b['material_source_units']};planp=R/'book/coverage/checks/future29-core/current65-canonical-plan10-v1.json';plan=read(planp);sources=[x for x in plan['sources']if x['owner']=='modules'];assert len(sources)==2 and sum(x['public_theorem_count']for x in sources)==72
LP=R/'book/coverage/checks/future29-applied/leakyqc30-full-independent-v1/leakyqc30-full-source-independent-applied29-peer-v1.json';SP=R/'book/coverage/checks/future29-applied/scalar-lipsdp42-full-independent-v1/scalar-lipsdp42-full-source-independent-applied29-peer-v1.json';assert sha(LP)=='cb9e1cf744d8acb4e2fd66ea5582545dfebcd2180555e1e573cec72692f35215'and sha(SP)=='b690a6d229fd067aa426216c9c9711ac9750fe917736eb0a2abf17f5c531a3ef';l=read(LP);s=read(SP);assert l['errors']==s['errors']==[] and l['prospective_source63_exercise']['whole_exercise_approved']and s['exercise']['prospective_corrected65_whole_exercise_approved']
def literal_equal(x,y):return {k:v for k,v in x.items()if k!='source_sha256'}=={k:v for k,v in y.items()if k!='source_sha256'}
assert literal_equal(l['prospective_source63_exercise']['entire_source_record'],EX['lipsdp.html::exercise-16'])and literal_equal(s['exercise']['entire_prospective_corrected65_literal'],EX['lipsdp.html::exercise-19'])
keys=[f'lipsdp.html::node-{x}'for x in [1289,1290,1291,1292,1293,1320,1324,1326,1327,1328,1329]]
for row in l['material_units']:
 src=l['prospective_source63_node1293']['entire_source_record']if row['key'].endswith('1293')else row['entire_source_record'];assert literal_equal(src,UN[row['key']])
for row in s['material_units']:assert literal_equal(row['entire_prospective_corrected65_literal'],UN[row['key']])and row['prospective_corrected65_whole_material_unit_approved']
I=B/'modules29-entire-owned-source60-to65-identity-v1.json';identity={'status':'passed_exact_actual65_owned_literal_identity_with_only_approved_two_exercise_three_unit_changes','historical_inventory':ref(OLDINV),'actual_inventory':ref(INV),'original_installed28_owner':ref(BASE),'actual_source61_64_application':ctx['actual_source61_to64_application'],'actual_source65_application':ctx['actual_source65_application'],'actual_source65_native':ctx['actual_source65_application_native'],'owned_exercise_count':217,'owned_material_source_unit_count':len({x['key']for x in b['material_source_units']if x['source']in scope}),'changed_keys':changed,'entire_changed_records':records,'all_other_owned_records_entire_equal_except_whole_page_source_fingerprint':True,'original_semantic_peer_bodies_and_review_times_not_reinterpreted':True,'prospective_peer_literal_texts_and_structural_identity_equal_actual65_individually':True,'coverage_complete':False};put(I,identity)
patches=[]
def change(parts,value):
 d=candidate
 for part in parts[:-1]:d=d[part]
 k=parts[-1];exists=k in d if isinstance(d,dict)else True;before=copy.deepcopy(d[k])if exists else None
 if exists and before==value:return
 patches.append({'path':parts,'existed':exists,'before':before});d[k]=copy.deepcopy(value)
changedpages={n:b['source_sha256'][n]for n in scope if old['source_sha256'][n]!=b['source_sha256'][n]};assert set(changedpages)=={'SafeLearning/lipsdp.html'}
change(['source_sha256'],{n:b['source_sha256'][n]for n in old['scope_pages']})
frags=copy.deepcopy(old['chapter_fragment_sha256'])
for n in frags:
 if n.endswith('/lipsdp.html'):frags[n]=sha(R/n)
change(['chapter_fragment_sha256'],frags);change(['current_inventory'],str(INV.relative_to(R)));change(['current_inventory_sha256'],sha(INV));change(['current_identity_binding_validation'],{'status':'actual_source65_two_whole_candidate_identity_matched_canonical_pairs_and_live_owner_integration_pending','inventory':ref(INV),'identity':ref(I),'canonical_owner_integrated':False});change(['inventory_identity_rebase65'],{'status':'prepared_exact_source60_to65_module_owned_literal_rebase','actual_full_identity':ref(I),'original_installed28_owner':ref(BASE),'source65_applied_before_this_author_preparation':True})
lnames=[x['name']for x in sources[0]['public_declarations']if x['kind']in ['theorem','lemma']];snames=[x['name']for x in sources[1]['public_declarations']if x['kind']in ['theorem','lemma']];assert len(lnames)==30 and len(snames)==42
lg={p:[]for p in 'abcd'}
for name in lnames:
 tail=name.rsplit('.',1)[1]
 if any(t in tail for t in ['piecewise','continuous','derivatives','slope_restricted','right_derivative','interval_integrable','slope_integral','almost_everywhere','average_of_the_genuine']):lg['a'].append(name)
 if any(t in tail for t in ['matrix_expansion','qc_is_nonnegative','slope_interval_iff_chord_product']):lg['b'].append(name)
 if any(t in tail for t in ['qc_equality','zero_input_chord','same_sign','printed_leaky','opposite_strict_sign']):lg['c'].append(name)
 if any(t in tail for t in ['zero_lower','conservative','training','multiplier','negative_gram']):lg['d'].append(name)
assert all(lg.values());sg={x['part']:x['declarations']for x in s['component_groups']};assert set(sg)=='abcde'if False else set(sg)==set('abcde')
lreason={x['part']:x['reason']for x in l['components']};lhy={x['part']:x['hypotheses']for x in l['components']};sreason={x['part']:x['scope']for x in s['component_groups']}
completion_associations=[];new_ex_claims=[]
for i,e in enumerate(candidate['exercises']):
 actual=EX[e['inventory_key']]
 if e.get('source_sha256')!=actual['source_sha256']:change(['exercises',i,'source_sha256'],actual['source_sha256'])
 if e['inventory_key']not in changed['exercises']:continue
 change(['exercises',i,'source_text_sha256'],actual['text_sha256']);kind='leaky'if e['inventory_key'].endswith('16')else'scalar';peer=LP if kind=='leaky'else SP;groups=lg if kind=='leaky'else sg;reasons=lreason if kind=='leaky'else sreason;reqparts=['a','a','b','c','d','d']if kind=='leaky'else['a','a','b','c','d','e']
 pending=[j for j,z in enumerate(e['claims'])if z['status']=='pending'];assert len(pending)==6
 for order,j in enumerate(pending):
  part=reqparts[order];row=copy.deepcopy(e['claims'][j]);original=copy.deepcopy(row);row.update({'status':'proved','lean_declarations':groups[part],'hypotheses':lhy[part]if kind=='leaky'else['Exact source scalar network,0≤alpha<beta and both real weights nonzero.','Part(d) uses arbitrary globally slope-restricted activation; finite ratio requires positive derivative supremum, and constant activation is separate.'],'correspondence':reasons[part],'remaining_gaps':[],'independent_source_review':ref(peer),'reviewed_owner29_transition':{'original_owner':ref(BASE),'original_claim_id':row['id'],'original_claim_canonical_json_sha256':hashlib.sha256(json.dumps(original,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest(),'whole_exercise_full_literal_peer':ref(peer),'actual_current65_identity':ref(I),'canonical_pair_pending':True}});change(['exercises',i,'claims',j],row);new_ex_claims.append({'exercise':e['inventory_key'],'claim_id':row['id'],'part':part,'declarations':groups[part]})
 inherited=[j for j,z in enumerate(e['claims'])if z['id'].endswith('proved-component-1')];assert len(inherited)==1;j=inherited[0];gap=e['claims'][j]['remaining_gaps'];assert gap
 fullnames=lnames if kind=='leaky'else snames
 completion_associations.append({'exercise':e['inventory_key'],'claim_id':e['claims'][j]['id'],'original_remaining_gaps':copy.deepcopy(gap),'new_remaining_gaps':[],'original_statement_declarations_hypotheses_correspondence_and_historical_time_fields_unchanged':True,'completion_support_declarations':fullnames,'completion_full_scope_peer':ref(peer),'reason':'The original matrix QC expansion/local activation values are proved by actual full leaky30 bodies.'if kind=='leaky'else'Actual genuine first/iterated second derivative, unique stationary/global optimizer, arbitrary-activation least constant via AC/FTC and exact printed charpoly/eigenvectors/rounding are proved by full scalar42 bodies.','actual_source65_identity':ref(I)});change(['exercises',i,'claims',j,'remaining_gaps'],[]);change(['exercises',i,'status'],'complete_math');change(['exercises',i,'entire_literal_closure29'],{'whole_exercise_approved':True,'remaining_gaps':[],'actual_current65_text_sha256':actual['text_sha256'],'unchanged_original_full_semantic_peer':ref(peer),'actual_current65_literal_identity':ref(I),'canonical_pair_and_owner_integration_pending':True})
partbyunit={1289:'a',1290:'b',1291:'b',1292:'c',1293:'d',1320:'all',1324:'a',1326:'b',1327:'c',1328:'d',1329:'e'};newmats=[]
for key in keys:
 rows=[i for i,z in enumerate(candidate['material_claims'])if z['status']=='pending'and z.get('source_unit_keys')==[key]];assert len(rows)==1;i=rows[0];row=copy.deepcopy(candidate['material_claims'][i]);original=copy.deepcopy(row);num=int(key.rsplit('-',1)[1]);kind='leaky'if num<1300 else'scalar';peer=LP if kind=='leaky'else SP;groups=lg if kind=='leaky'else sg;reasons=lreason if kind=='leaky'else sreason;part=partbyunit[num];decl=(lnames if kind=='leaky'else snames)if part=='all'else groups[part];reason='Entire actual source scalar model and every requested part(a)-(e) are discharged by the full42-body independent peer.'if part=='all'else reasons[part]
 row.update({'statement_in_prose':UN[key]['source_text'],'kind':'independently_reviewed_complete_mathematical_source_unit','status':'proved','lean_declarations':decl,'hypotheses':['Exact actual current65 source literal and independently approved full mathematical model; all domain/nonzero/slope and finite ratio hypotheses remain explicit in the proof and source.'],'correspondence':reason,'remaining_gaps':[],'independent_source_review':ref(peer),'entire_original_literal_decision_and_review_time':{'source_unit_key':key,'entire_actual_current65_inventory_record':UN[key],'whole_literal_approved':True,'original_full_semantic_peer':ref(peer),'original_review_time_preserved_by_exact_peer_body':True,'actual_source_application_and_current65_identity':ref(I)},'reviewed_owner29_transition':{'original_owner':ref(BASE),'original_claim_id':row['id'],'original_claim_canonical_json_sha256':hashlib.sha256(json.dumps(original,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest(),'actual_current65_identity':ref(I),'canonical_pair_pending':True}});change(['material_claims',i],row);newmats.append({'key':key,'index':i,'claim_id':row['id'],'part':part,'declarations':decl})
newproof={}
for r in sources:
 names=[v['name']for v in r['public_declarations']if v['kind']in ['theorem','lemma']];newproof[r['canonical_source']]={'sha256':r['original_tmp_source']['sha256'],'selection_scope':'direct_reviewed_reference_pending_actual_canonical_pair','standalone_compile_status':'pending_actual_root_canonical_pair','declarations':names,'public_theorem_names':names,'mapped_named_declarations':names,'theorem_count':len(names),'public_declarations':r['public_declarations'],'original_tmp_source':r['original_tmp_source'],'original_actual_tmp_trial':r['original_actual_tmp_trial'],'independent_source_review':r['independent_source_peers'][0],'actual_pair':None,'canonical_pair_pending':True};change(['proof_files',r['canonical_source']],newproof[r['canonical_source']])
change(['declarations'],old['declarations']+lnames+snames)
counts=copy.deepcopy(old['counts']);counts['exercise_status']=dict(Counter(e['status']for e in candidate['exercises']));counts['exercise_claim_status']=dict(Counter(z['status']for e in candidate['exercises']for z in e['claims']));counts['material_claim_status']=dict(Counter(z['status']for z in candidate['material_claims']));counts['new_declarations']=len(candidate['declarations']);change(['counts'],counts)
A=B/'modules29-two-inherited-gap-completion-associations-v1.json';put(A,{'status':'exact_two_original_gap_list_clearings_fully_discharged_by_approved_full_source_peers_pending_independent_final_mapping','original_owner':ref(BASE),'actual_current65_identity':ref(I),'associations':completion_associations,'only_original_remaining_gaps_changed_in_two_inherited_proved_components':True,'coverage_complete':False})
change(['reviewed_work_integration29_current65_candidate'],{'status':'prepared_isolated_actual65_two_whole_exercises_eleven_units_with_actual_canonical_pairs_pending','author_prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_installed28_owner':ref(BASE),'actual_current65_identity':ref(I),'whole_exercises':changed['exercises'],'whole_material_units':keys,'new_sources':sources,'new_public_theorem_count':72,'new_public_name_count':91,'two_inherited_gap_completion_associations':ref(A),'original_semantic_peer_bodies_times_and_every_old_proved_claim_metadata_retained':True,'current_owner_canonical_selection_publication_written':False,'coverage_complete':False})
CAND=B/'modules29-current65-two-whole-candidate-v1.json';put(CAND,candidate)
reverse=copy.deepcopy(candidate)
for item in reversed(patches):
 d=reverse
 for k in item['path'][:-1]:d=d[k]
 if item['existed']:d[item['path'][-1]]=copy.deepcopy(item['before'])
 else:del d[item['path'][-1]]
assert reverse==old and (json.dumps(reverse,indent=2,ensure_ascii=False)+'\n').encode()==BASE.read_bytes()
assert candidate['counts']['exercise_status']=={'complete_math':189,'pending':19,'partial':9}and candidate['counts']['material_claim_status']=={'not_a_formal_claim':536,'pending':3572,'proved':1092}and len(candidate['declarations'])==3484
INVERSE=B/'modules29-current65-exact-forward-inverse-interface-v1.json';put(INVERSE,{'status':'exact_candidate_forward_and_full_byte_inverse_verified_pending_independent_mapping','base':ref(BASE),'candidate':ref(CAND),'restore_patches_in_reverse_order':patches,'exact_inverse_restores_entire_raw1c91_original_bytes':True,'new_exercise_claim_associations':new_ex_claims,'new_material_claim_associations':newmats,'inherited_only_two_gap_arrays':ref(A),'all_other_old_claim_prose_hypotheses_declarations_correspondence_metadata_history_and_times_unchanged':True,'old500_proof_rows_and3412_declaration_prefix_exact':True,'new_proofs_have_no_fake_canonical_receipt_fields':True,'coverage_complete':False})
O=B/'modules29-current65-two-whole-offer-draft-v1.json';put(O,{'status':'isolated_modules29_current65_two_whole_exercises_eleven_units_pending_actual_canonical_pairs_and_independent_mapping','errors':[],'candidate':ref(CAND),'inventory':ref(INV),'inventory_sha256':sha(INV),'source_sha256':candidate['source_sha256'],'identity_sidecar':ref(I),'exact_inverse_interface':ref(INVERSE),'completion_associations':ref(A),'proof_files':newproof,'canonical_plan':ref(planp),'original_owner':ref(BASE),'original_full_leaky_peer':ref(LP),'original_full_scalar_peer':ref(SP),'new_exercises':changed['exercises'],'new_material_keys':keys,'counts':counts,'actual_canonical_pairs_pending':True,'canonical_owner_selection_publication_changes':False,'coverage_complete':False})
for n,h in held.items():assert sha(path(n))==h
print(json.dumps({'candidate':ref(CAND),'offer':ref(O),'inverse':ref(INVERSE),'identity':ref(I),'completion_associations':ref(A),'counts':counts,'old_immutable_base':ref(BASE),'restore_patch_count':len(patches)}))
