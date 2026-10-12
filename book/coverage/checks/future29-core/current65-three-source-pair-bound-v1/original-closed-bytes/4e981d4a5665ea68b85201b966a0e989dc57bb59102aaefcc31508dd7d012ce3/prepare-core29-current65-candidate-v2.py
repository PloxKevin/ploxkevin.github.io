from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,copy,importlib.util
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/core29-current65-approved-candidate-v2');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def ref(p):p=Path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def put(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';ctx=read(C)
assert ctx['status']=='actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'
held={}
for m in [ctx['pins_sha256'],ctx['held_current_source_sha256'],ctx['owners_sha256']]:
 for n,h in m.items():assert n not in held or held[n]==h;held[n]=h
BASE=R/'book/coverage/core.json';assert sha(BASE)=='5260f60e35a921106021e6c9d88197f4a96494fdd24c3b39ae143a06ea594036';base=read(BASE)
INV=R/'book/coverage/inventory-after-correction65.json';OLD=R/'book/coverage/inventory-after-correction60.json';assert sha(INV)==sha(R/'book/coverage/inventory.json')=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
inv,old=read(INV),read(OLD);scope=set(base['scope_pages'])
for sec,count in [('exercises',92),('material_source_units',3982)]:
 a={x['key']:x for x in old[sec] if x['source'] in scope};b={x['key']:x for x in inv[sec] if x['source'] in scope};assert a==b and len(a)==count
assert base['source_sha256']=={n:inv['source_sha256'][n] for n in scope}
units={x['key']:x for x in inv['material_source_units']};exindex={x['key']:x for x in inv['exercises']};closure={};aliases={}
def add(q):
 p=path(q['file']) if isinstance(q,dict) else Path(q);h=sha(p)
 if isinstance(q,dict):assert h==q['sha256'],str(p)
 rr=ref(p);assert rr['file'] not in closure or closure[rr['file']]==h;closure[rr['file']]=h;return read(p) if p.suffix=='.json' else p.read_text()
def record_alias(original,q):
 assert set(q) <= {'file','sha256','bytes'} and {'file','sha256'} <= set(q)
 p=path(q['file']);assert sha(p)==q['sha256']
 if 'bytes' in q:assert type(q['bytes']) is int and q['bytes']==p.stat().st_size
 simple=ref(p);assert original not in aliases or aliases[original]==simple;aliases[original]=simple
 return simple
def peer(n,h):
 p=R/n;assert sha(p)==h;d=add(ref(p));assert d['errors']==[] and d['status'].startswith('passed_')
 original_aliases=d.get('original_closed_byte_aliases',{})
 assert isinstance(original_aliases,dict)
 for original,q in original_aliases.items():record_alias(original,q)
 for k in ['required_evidence_artifacts_sha256','closed_evidence_sha256']:
  for f,v in d.get(k,{}).items():
   q=path(f)
   if not q.is_file() or sha(q)!=v:
    # The original peer retains historical Source60 hashes. Resolve only exact
    # immutable bytes; do not overwrite its map, body, or review time.
    possibilities=[]
    if f in original_aliases and original_aliases[f]['sha256']==v:possibilities.append(path(original_aliases[f]['file']))
    if f in ['book/coverage/inventory.json','book/coverage/material-corrections.json']:possibilities.append(R/'reports/full-coverage/checkpoint-28'/f)
    matches=[x for x in possibilities if x.is_file() and sha(x)==v];assert matches,f
    q=matches[0];record_alias(f,ref(q))
   add({'file':str(q),'sha256':v})
 return p,d
MPC,mpc=peer('book/coverage/checks/future28-foundations/mpc-primary9-full-independent-foundations29-v1/mpc-primary9-full-source-whole-exercise18-and-node1387-independent-foundations29-peer-v1.json','4dcd20c0f99558441ac46f51140e8fb603de5f835955a4bb41968ac9fe67bc07')
DUAL,dual=peer('book/coverage/checks/future29-applied/projected-dual17-full-independent-v1/projected-dual17-full-source-independent-applied29-peer-v1.json','a7e7b6b4b19bfa6b2bdc5a5ef6e706fcbc08b5dd47e61c4986fc327948d0ac58')
MON,mon=peer('book/coverage/checks/future29-applied/monitoring-fixed-selector29-full-independent-v1/monitoring-fixed-selector29-full-source-independent-applied29-peer-v1.json','72df0b38c651812d6d985810ed460f08ebd24434b02f029af8554a22422c4229')
ED,ed=peer('book/coverage/checks/future29-core/editorial13-independent-modules-v1/editorial13-independent-full-literal-modules29-peer-v1.json','3aeb7e28c10867335b43dbacc561b3f84e336bf557b7ed601e9e83e6cafdf0b0')
assert [x['inventory_key'] for x in mpc['whole_decisions']]==['lyapunov-mpc.html::exercise-18','lyapunov-mpc.html::node-1387'] and all(x['whole_unit_approved'] and x['missing_clauses']==[] for x in mpc['whole_decisions'])
assert len(dual['components'])==4 and dual['whole750_752_or_exercise21_approved'] is False
assert len(mon['components'])==3 and mon['whole_exercise21_or_node1141_approved'] is False
assert len(ed['individual_full_literal_decisions'])==13 and all(x['approved_status']=='not_a_formal_claim' and x['entire_literal_classification_approved'] for x in ed['individual_full_literal_decisions'])
PLAN=R/'book/coverage/checks/future29-core/current65-canonical-plan10-v1.json';plan=add(ref(PLAN));rows=[x for x in plan['sources'] if x['owner']=='core'];assert len(rows)==2
spec=importlib.util.spec_from_file_location('core29_names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
planned={}
for row in rows:
 original=row['original_tmp_source'];s=add(original);ds=names.declarations(s);assert ds==row['public_declarations']
 planned[row['canonical_source']]={'sha256':original['sha256'],'original_tmp_source':original,'declarations':ds,'actual_pair':None,'canonical_pair_binding_status':'pending_actual_standalone_and_named_commands'}
q=mon['proof_source'];ms=add(q);md=names.declarations(ms);assert len(md)==29 and sum(x['kind']=='theorem' for x in md)==16
planned['verification/lean/SafeLearning/CompleteCoreMonitoringFixedSelector29.lean']={'sha256':q['sha256'],'original_tmp_source':q,'declarations':md,'actual_pair':None,'canonical_pair_binding_status':'pending_actual_standalone_and_named_commands'}
assert len(planned)==3 and sum(len(x['declarations']) for x in planned.values())==142 and sum(sum(y['kind'] in ['theorem','lemma'] for y in x['declarations']) for x in planned.values())==93
newnames={d['name'] for x in planned.values() for d in x['declarations']};assert len(newnames)==142
mpcnames=[x for x in newnames if x.rsplit('.',1)[-1] in mpc['new_public_names']];assert len(mpcnames)==9
SELF=Path(__file__);selfsha=sha(SELF)
def guard():
 assert sha(SELF)==selfsha
 for f,h in held.items():assert sha(path(f))==h,f
 for f,h in closure.items():assert sha(path(f))==h,f
for f,h in {
 '/tmp/prepare-core29-current65-candidate-v1.py':'17061da9668494eac635b53c39cede1d89990c89e043ba7228f8209383081d1c',
 '/tmp/run-core29-current65-candidate-preparation-v1.py':'f2ffb76b91279d541fe8c32f67bb902b001621306f508d28292b814936e6a065',
 '/tmp/core29-current65-candidate-preparation-actual-v1.json':'4459e6d82f8cab8384dadaccbb1c4a4833fef8abb002635b486af58251b65f9a',
 '/tmp/core29-current65-candidate-preparation-actual-v1.log':'9bfb0b347efe784304095e58fd6539a597af501c2f164f37c9ebe022178c5373'
}.items():add({'file':f,'sha256':h})
assert read('/tmp/core29-current65-candidate-preparation-actual-v1.json')['actual_exit_code']==1
guard();OUT.mkdir(exist_ok=False)
ORIGINAL=OUT/'original-installed28-core.json'
with ORIGINAL.open('xb') as f:f.write(BASE.read_bytes())
assert sha(ORIGINAL)==sha(BASE)
HIST=OUT/'core29-original-changed-rows-and-inverse-v1.json';IDENT=OUT/'core29-source60-to65-entire-owned-literal-identity-v1.json'
put(IDENT,{'status':'passed_actual_entire_core_source60_to65_owned_literal_identity','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'historical_inventory':ref(OLD),'current_inventory':ref(INV),'entire_equal_owned_inventory_records':{'exercises':92,'material_source_units':3982},'old_owner':ref(ORIGINAL),'changed_owned_literal_keys':[],'scope':'Source61-65 modifies other owners pages only; unchanged Core literal records do not imply any new mathematical review.'})
original_exercises={};original_material={};appended_exercise_ids=[];appended_material_ids=[];candidate=copy.deepcopy(base)
def original_mat(row):
 assert row['id'] not in original_material;original_material[row['id']]=copy.deepcopy(row)
def review_pointer(p,d):return {'source':ref(p)['file'],'sha256':sha(p),'original_review_time':d.get('review_completed_at_utc',d.get('reader_finished_at_utc'))}
def component(cid,text,decls,hyp,reason,p,d,decision):
 assert decls and set(decls)<=newnames
 return {'id':cid,'kind':'independently_reviewed_precise_source_components','status':'proved','statement_in_prose':text,'lean_declarations':decls,'hypotheses':hyp,'correspondence':reason,'remaining_gaps':[],'independent_review':review_pointer(p,d),'original_review_component':copy.deepcopy(decision)}
def dualcomponent(x,cid):
 return component(cid,x['id'],['SafeLearning.CompleteCoreProjectedDualDrift29.'+n for n in x['names']],[x['scope']],x['independent_reason'],DUAL,dual,x)
monitor_names=[n for x in mon['components'] for n in x['lean_declarations']];assert len(monitor_names)==16
monitor_hyp=list(dict.fromkeys(v for x in mon['components'] for v in x['hypotheses']))
monitor_reason=' '.join(x['reason'] for x in mon['components'])
monitor_decision={'scope':'One fixed-price selector component composed from three individually approved groups. Whole Exercise21/node1141 remains pending generic A1-A3 stochastic execution.','groups':copy.deepcopy(mon['components'])}
def monitoringcomponent(cid):return component(cid,'Actual stationary monitoring selector for every fixed real price and initial state',monitor_names,monitor_hyp,monitor_reason,MON,mon,monitor_decision)
for e in candidate['exercises']:
 key=e['inventory_key']
 if key not in ['lyapunov-mpc.html::exercise-18','cmdp.html::exercise-21']:continue
 original_exercises[key]=copy.deepcopy(e)
 if key=='lyapunov-mpc.html::exercise-18':
  pending=[x for x in e['claims'] if x['status']=='pending'];assert len(pending)==1;x=pending[0]
  retained=[n for c in e['claims'] if c['status']=='proved' for n in c['lean_declarations']]
  x.update(kind='independently_reviewed_entire_source_exercise',status='proved',lean_declarations=list(dict.fromkeys(retained+mpcnames)),hypotheses=copy.deepcopy(mpc['scope_limits']),correspondence=' '.join(mpc['whole_decisions'][0][letter] for letter in ['a','b','c','d']),remaining_gaps=[],independent_review=review_pointer(MPC,mpc),original_complete_literal_review_record=copy.deepcopy(mpc['whole_decisions'][0]),original_pending_row_archive={'file':str(HIST),'binding':'completed_after_exact_history_write'})
  e['status']='complete_math'
 else:
  pending=[x for x in e['claims'] if x['status']=='pending'];assert len(pending)==1;x=pending[0]
  x['remaining_gaps']=['The general Section7 stochastic exact-maximizer execution theorem under A1-A3 remains pending. Conditional epoch unbiasedness is not inferred from fixed-price long-run maximization.']
  x['correspondence']='The actual arbitrary-price stationary selector is now independently proved; generic A1-A3 stochastic execution remains separate and pending.';x['original_pending_row_archive']={'file':str(HIST),'binding':'completed_after_exact_history_write'}
  for d in dual['components']:
   cid=key+'::core29-dual-component-'+d['id'];e['claims'].append(dualcomponent(d,cid));appended_exercise_ids.append(cid)
  cid=key+'::core29-fixed-selector-component';e['claims'].append(monitoringcomponent(cid));appended_exercise_ids.append(cid)
  assert e['status']=='partial'
edits={x['claim_id']:x for x in ed['individual_full_literal_decisions']}
for row in candidate['material_claims']:
 key=row['source_unit_keys'][0]
 if row['id'] in edits:
  d=edits[row['id']];assert row['status']=='pending' and d['source_unit_key']==key;original_mat(row)
  row.update(kind='independently_reviewed_entire_editorial_literal',status='not_a_formal_claim',lean_declarations=[],hypotheses=[],correspondence=d['rationale'],remaining_gaps=[],independent_review=review_pointer(ED,ed),original_complete_literal_review_record=copy.deepcopy(d),original_pending_row_archive={'file':str(HIST),'binding':'completed_after_exact_history_write'})
 elif key=='lyapunov-mpc.html::node-1387' and row['status']=='pending':
  original_mat(row);d=mpc['whole_decisions'][1];row.update(kind='independently_reviewed_literal_material_unit',status='proved',lean_declarations=mpcnames,hypotheses=copy.deepcopy(mpc['scope_limits']),correspondence=d['correspondence'],remaining_gaps=[],independent_review=review_pointer(MPC,mpc),original_complete_literal_review_record=copy.deepcopy(d),original_pending_row_archive={'file':str(HIST),'binding':'completed_after_exact_history_write'})
 elif key=='cmdp.html::node-749' and row['status']=='pending':
  original_mat(row);d=dual['whole_material_units'][0];assert d['key']==key and d['whole_unit_approved'] and d['missing_clauses']==[]
  row.update(kind='independently_reviewed_literal_material_unit',status='proved',lean_declarations=['SafeLearning.CompleteCoreProjectedDualDrift29.'+n for n in dual['components'][0]['names']],hypotheses=copy.deepcopy(d['operational_hypotheses']),correspondence=d['correspondence'],remaining_gaps=[],independent_review=review_pointer(DUAL,dual),original_complete_literal_review_record=copy.deepcopy(d),original_pending_row_archive={'file':str(HIST),'binding':'completed_after_exact_history_write'})
 elif key=='cmdp.html::node-1141' and row['status']=='pending':
  original_mat(row);row['remaining_gaps']=['Generic Section7 A1-A3 exact-maximizer stochastic switching feasibility/expected near-optimality remains pending. No unbiased finite epoch inference from long-run maximization.'];row['correspondence']='The fixed-price all-initial-state selector, the prior explicit changing-price cycle and representation/bias components are independently proved; the general stochastic passage remains pending.';row['original_pending_row_archive']={'file':str(HIST),'binding':'completed_after_exact_history_write'}
assert len(original_material)==16
for key in ['cmdp.html::node-750','cmdp.html::node-752']:
 for d in dual['components']:
  cid=key+'::core29-dual-component-'+d['id'];a=dualcomponent(d,cid);u=units[key];a.update(source_unit_keys=[key],source=u['source'],source_sha256=u['source_sha256'],source_text=u['source_text'],text_sha256=u['text_sha256'],parent_remaining_gaps=copy.deepcopy(dual['remaining_generic_theorem_gaps']));candidate['material_claims'].append(a);appended_material_ids.append(cid)
key='cmdp.html::node-1141';cid=key+'::core29-fixed-selector-component';a=monitoringcomponent(cid);u=units[key];a.update(source_unit_keys=[key],source=u['source'],source_sha256=u['source_sha256'],source_text=u['source_text'],text_sha256=u['text_sha256'],parent_remaining_gaps=copy.deepcopy(mon['remaining_gaps']));candidate['material_claims'].append(a);appended_material_ids.append(cid)
for f,x in planned.items():assert f not in candidate['proof_files'];candidate['proof_files'][f]=x['sha256']
candidate['current_inventory']=str(INV.relative_to(R));candidate['current_inventory_sha256']=sha(INV)
candidate['counts']=copy.deepcopy(base['counts']);candidate['counts']['exercise_statuses']=dict(sorted(Counter(e['status'] for e in candidate['exercises']).items()));candidate['counts']['material_claims']=len(candidate['material_claims']);candidate['counts']['proof_files']=len(candidate['proof_files'])
assert candidate['counts']['exercise_statuses']=={'complete_math':90,'partial':2} and candidate['counts']['material_claims']==4219 and candidate['counts']['proof_files']==185
put(HIST,{'status':'exact_original_core28_changed_rows_and_reversible_candidate_delta','original_entire_owner':ref(ORIGINAL),'original_exercises':original_exercises,'original_material_rows':original_material,'appended_exercise_claim_ids':appended_exercise_ids,'appended_material_claim_ids':appended_material_ids,'new_planned_proof_files':list(planned),'original_top_level':{k:copy.deepcopy(base[k]) for k in ['counts','current_inventory','current_inventory_sha256']},'inverse_recipe':'Restore two complete exercise rows and16 exact original material rows; remove nine appended material rows and three proof rows; restore three top-level fields and delete future29_current65_candidate_binding. Every other field stays exact.'})
for e in candidate['exercises']:
 for x in e['claims']:
  if 'original_pending_row_archive' in x and x['original_pending_row_archive'].get('binding')=='completed_after_exact_history_write':x['original_pending_row_archive']=ref(HIST)
for x in candidate['material_claims']:
 if 'original_pending_row_archive' in x and x['original_pending_row_archive'].get('binding')=='completed_after_exact_history_write':x['original_pending_row_archive']=ref(HIST)
candidate['future29_current65_candidate_binding']={'identity':ref(IDENT),'original_changed_rows_and_exact_inverse':ref(HIST),'original_entire_owner':ref(ORIGINAL),'source_correspondence_peers':[ref(MPC),ref(DUAL),ref(MON),ref(ED)],'canonical_pair_binding_status':'pending_all_three_actual_standalone_named_pairs','whole_exercises':['lyapunov-mpc.html::exercise-18'],'whole_mathematical_units':['lyapunov-mpc.html::node-1387','cmdp.html::node-749'],'not_formal_claim_ids':list(edits),'still_partial_exercises':[x['inventory_key'] for x in candidate['exercises'] if x['status']=='partial'],'prepared_at_utc':datetime.now(timezone.utc).isoformat()}
reverse=copy.deepcopy(candidate);reverse['exercises']=[copy.deepcopy(original_exercises.get(e['inventory_key'],e)) for e in reverse['exercises']];reverse['material_claims']=[copy.deepcopy(original_material.get(x['id'],x)) for x in reverse['material_claims'] if x['id'] not in appended_material_ids]
for f in planned:reverse['proof_files'].pop(f)
for k in ['counts','current_inventory','current_inventory_sha256']:reverse[k]=copy.deepcopy(base[k])
reverse.pop('future29_current65_candidate_binding');assert reverse==base and json.dumps(reverse,indent=2,ensure_ascii=False)+'\n'==BASE.read_text()
# All original proved exercise/material records remain exactly equal.
for olde,e in zip(base['exercises'],candidate['exercises']):
 for oldc,c in zip(olde['claims'],e['claims']):
  if oldc['status']!='pending':assert oldc==c,oldc['id']
for oldc,c in zip(base['material_claims'],candidate['material_claims']):
 if oldc['status']!='pending':assert oldc==c,oldc['id']
CAND=OUT/'core29-current65-three-source-approved-scope-candidate-v1.json';put(CAND,candidate)
for p in [BASE,ORIGINAL,INV,OLD,C,SELF,IDENT,HIST]:add(ref(p))
OFFER=OUT/'core29-current65-three-source-pending-pair-offer-v1.json';put(OFFER,{'schema_version':1,'status':'isolated_core29_current65_approved_mapping_pending_three_actual_canonical_pairs','errors':[],'candidate':ref(CAND),'identity':ref(IDENT),'original_changed_rows_and_inverse':ref(HIST),'inventory_sha256':sha(INV),'source_sha256':candidate['source_sha256'],'planned_proof_files':planned,'proof_files':{},'new_public_declaration_count':142,'new_theorem_lemma_count':93,'whole_exercises':['lyapunov-mpc.html::exercise-18'],'whole_mathematical_units':['lyapunov-mpc.html::node-1387','cmdp.html::node-749'],'editorial_not_formal_count':13,'dual_component_count':4,'fixed_selector_component_count':1,'source_correspondence_peers':[ref(MPC),ref(DUAL),ref(MON),ref(ED)],'canonical_pair_ready':False,'actual_finalizer':None,'candidate_builder':ref(SELF),'required_evidence_artifacts_sha256':closure,'original_closed_byte_aliases':aliases,'counts':candidate['counts'],'whole_exercise21_or_generic_stochastic_CMDP_approved':False,'original_semantic_bodies_review_times_and_proved_rows_preserved':True,'coverage_complete':False,'live_owner_written':False})
guard();print(json.dumps({'status':'passed_isolated_pending_pair_core29_mapping','candidate':ref(CAND),'offer':ref(OFFER),'history':ref(HIST),'counts':candidate['counts'],'planned_sources':3,'public_declarations':142,'theorem_lemma_count':93,'exact_inverse_and_old_proved_records_preserved':True}))
