"""Prepare a reversible isolated Core26 candidate; Root alone executes this helper.

It retains all former semantic decisions/times, adds exact conditional MPC
components, and approves Exercise19 and five literal units only via the independent actual53 full review.
It does not write live owners, HTML, inventory, selection, publication or Git.
"""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/future26-core/composed-source53-v2'
OLD='book/coverage/core.json';OLD_SHA='4e96c717055187cfc24e9e60a19a7d183499336570d99fbf9954ff199ff49572'
# The exact full baseline digest is asserted through the fixed label candidate's
# independently checked original-owner binding as well as the installed ledger.
LABEL='book/coverage/checks/future26-core/box-labels/core26-source52-labels-candidate-v1.json'
LABEL_SHA='19a7dd99511117f0cb192167f0a2d04c4c11220505ea93526600e5396845fa3c'
INV='book/coverage/inventory-after-correction53.json';INV_SHA='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
MPC='book/coverage/checks/future26-core/mpc-hybrid-matrix/root-mpc-hybrid-matrix26-canonical-readiness-v1.json'
MPC_SHA='fc80e2d201ea77ebfefd6548c92020c21a41aa06e4138641fcb1e34c1f6abe94'
SCALAR='book/coverage/checks/applied-future26/scalar-scenario-v2/two-source13-canonical-paired-build-readiness-v1.json'
SCALAR_SHA='ddc5ba6a00b69056d560d743ba1a18543693d5045b4c12218376efde9530c130'
SUPPORT='book/coverage/checks/applied-future26/changed-optimizer-support/support5-canonical-source53-paired-readiness-v1.json'
SUPPORT_SHA='d33a3b1c5333dfe85c9f600e67064ba6bf63f2c20b40d0dd750c1a235963f52a'
FULLPEER=Path('/tmp/lyapunov-current53-exercise19-all-four-parts-independent-foundations-full-review26-final-v1.json');FULLPEER_SHA='9fc6afef3d329176ee7e543882eacabaa7d2fca4ca2434de6db4cc5410db641d'
OUT=BASE+'/core26-source53-composed-candidate-v1.json';REPORT=BASE+'/core26-source53-composed-candidate-integrity-v1.json';IDENTITY=BASE+'/source52-to53-core-entire-row-identity-and-history-v1.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def write(n,d):
 p=ROOT/n;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def exact_ref(r):assert sha(r['file'])==r['sha256'],r['file'];return read(r['file'])
def zero(d):
 values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
 assert values and all(type(x)is int and x==0 for x in values)
assert sha(OLD)==OLD_SHA and sha(INV)==INV_SHA==sha('book/coverage/inventory.json') and sha(LABEL)==LABEL_SHA
old=read(OLD);label=read(LABEL)
# Both fixed baseline and fixed label candidate must have the same full original
# exercise, proof, count and top-level provenance bodies.
label_binding=label['future26_label_material_candidate_binding']
prior_ref=label_binding['prior_isolated_owner25_candidate']
assert prior_ref is not None and exact_ref(prior_ref)==old and prior_ref['sha256']==sha(OLD)
assert old['owner']=='core' and len(old['exercises'])==92 and len(old['proof_files'])==177
assert label['exercises']==old['exercises'] and label['proof_files']==old['proof_files']
assert label['counts']==old['counts'] and len(label['material_claims'])==len(old['material_claims'])==4147
nf=[i for i,(a,b) in enumerate(zip(old['material_claims'],label['material_claims'])) if a!=b]
assert len(nf)==48
for i in nf:
 assert old['material_claims'][i]['status']=='pending' and label['material_claims'][i]['status']=='not_a_formal_claim'
 assert label['material_claims'][i]['original_source52_entire_pending_material_row']==old['material_claims'][i]
selection=read('reports/full-coverage/checkpoint-25-selection.json');assert selection['proof_file_count']==len(selection['proof_files'])==1156
manifest=read('reports/full-coverage/checkpoint-25-manifest.json');assert manifest['status']=='formal_verification_passed_partial_coverage'
protected={n:r['sha256'] for n,r in selection['proof_files'].items()}
owners={'book/coverage/'+o+'.json' for o in ('core','foundations','applied','modules','applied-promotions')}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in owners})
protected['SafeLearning/lyapunov-mpc.html']='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
protected[INV]=INV_SHA;protected['book/coverage/inventory.json']=INV_SHA
protected['reports/full-coverage/source53-correction-application-v1.json']='fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548'
def guard():
 for n,h in protected.items():assert sha(n)==h,n
 assert sha(OLD)==prior_ref['sha256'] and sha(LABEL)==LABEL_SHA
guard();inventory=read(INV);units={x['key']:x for x in inventory['material_source_units']};exercises={x['key']:x for x in inventory['exercises']}
for n,h in [(MPC,MPC_SHA),(SCALAR,SCALAR_SHA),(SUPPORT,SUPPORT_SHA)]:assert sha(n)==h
mpc=read(MPC);scalar=read(SCALAR);support=read(SUPPORT)
whole_ref=support['original_full_current53_semantic_peer'];whole_peer=exact_ref(whole_ref)
assert whole_peer==support['entire_original_semantic_peer_body_and_time']
assert whole_peer['errors']==[] and whole_peer['whole_answer1397_approved'] is True and whole_peer['whole_exercise_component_a_approved'] is True
assert whole_peer['whole_exercise_approved'] is False and whole_peer['current53_inventory']['sha256']==INV_SHA
whole=whole_peer['material_units'][0];assert whole['source_unit_key']=='lyapunov-mpc.html::node-1397' and whole['entire_inventory_record']==units[whole['source_unit_key']]
assert whole['whole_material_unit_approved'] is True and whole['missing_clauses']==[] and whole['remaining_gaps']==[]
mpc_peer_ref=mpc['original_full_source_peer'];mpc_peer=exact_ref(mpc_peer_ref)
# Only the exact preserved MPC prefix chain is traversed, avoiding unrelated
# nested historical scenario reviews.
mpc_groups=[];current=mpc_peer;current_ref=mpc_peer_ref
while True:
 assert current['errors']==[] and current['whole_exercise_approved'] is False
 for unit in current['material_units']:
  if unit['source_unit_key']=='lyapunov-mpc.html::node-1387':
   for component in unit['components']:
    assert component['missing_clauses']==[] and component['decision'].startswith('approved')
    mpc_groups.append({'original_component':copy.deepcopy(component),'original_review':copy.deepcopy(current_ref),'original_review_time':current['reviewed_at_utc']})
 links=[v for k,v in current.items() if k in {'preserved_original25_component_review','preserved_original_eighteen_component_review','preserved_original_fifteen_component_review','preserved_original_thirteen_component_review','preserved_original_seven_component_review'} and isinstance(v,dict) and 'entire_original_body_and_time' in v and 'record' in v]
 if not links:break
 assert len(links)==1
 current_ref=links[0]['record'];current=links[0]['entire_original_body_and_time']
 # Original absolute TMP references are retained; their exact canonical byte
 # copies were checked in the MPC readiness before candidate use.
 if current_ref['file'].startswith('/tmp/'):
  alias=mpc['original_TMP_byte_copies'][current_ref['file']];assert alias['sha256']==current_ref['sha256'];assert exact_ref(alias)==current
 else:assert exact_ref(current_ref)==current
mpc_names=[n for g in mpc_groups for n in g['original_component']['lean_declarations']]
assert len(mpc_groups)==len(mpc_names)==len(set(mpc_names))==30
source_rows=[{'source':mpc['source'],'source_snapshot':mpc['source_snapshot'],'public_count':30,'pair':mpc['actual_canonical_pair'],'readiness':ref(MPC)}]
for r in scalar['proof_sources']:source_rows.append({'source':r['source'],'source_snapshot':r['source_snapshot'],'public_count':len(r['public_theorems']),'pair':r['actual_canonical_pair'],'readiness':ref(SCALAR)})
source_rows.append({'source':support['source'],'source_snapshot':support['source_snapshot'],'public_count':5,'pair':support['actual_canonical_pair'],'readiness':ref(SUPPORT)})
assert len(source_rows)==4 and sum(r['public_count'] for r in source_rows)==48
for r in source_rows:
 assert sha(r['source']['file'])==r['source']['sha256']==sha(r['source_snapshot']['file'])
 assert len(r['pair'])==2
 assert len(re.findall(r'^theorem ',(ROOT/r['source']['file']).read_text(),re.M))==r['public_count']
 for pair in r['pair']:
  actual_ref=pair.get('record',pair);actual=exact_ref(actual_ref);zero(actual)
  assert actual['source_sha256_before']==actual['source_sha256_after']==r['source']['sha256'] and actual['source_unchanged'] is True
  assert sha(actual['log'])==actual['log_sha256'] and actual['actual_workdir']==str(ROOT/'verification/lean')
  assert actual['command'][0]=='lake'
 assert r['source']['file'] not in old['proof_files']
# Fresh whole(a--d) decisions are distinct from the earlier part(a) review.
assert hashlib.sha256(FULLPEER.read_bytes()).hexdigest()==FULLPEER_SHA
full=json.loads(FULLPEER.read_text());assert full['errors']==[] and full['whole_exercise_approved'] is True and full['missing_clauses']==[] and full['remaining_gaps']==[]
assert full['current_inventory']['sha256']==INV_SHA
full_ex=full['exercise_records'][0]
assert full_ex['inventory_key']=='lyapunov-mpc.html::exercise-19' and full_ex['entire_inventory_record']==exercises[full_ex['inventory_key']]
assert full_ex['whole_exercise_approved'] is True and full_ex['missing_clauses']==[]
whole_units={u['source_unit_key']:u for u in full['material_units']}
assert set(whole_units)=={'lyapunov-mpc.html::node-'+str(k) for k in (1393,1397,1399,1401,1403)}
for key,u in whole_units.items():assert u['entire_inventory_record']==units[key] and u['whole_unit_approved'] is True and u['missing_clauses']==[] and u['remaining_gaps']==[]
# Archive every actual TMP reader/proof/reference needed by this fresh review,
# preserving byte bodies, failures and original times. This produces only NEW
# versioned closure paths and never changes the original reports.
originals={FULLPEER}
def collect_tmp(v):
 if isinstance(v,dict):
  for k,x in v.items():collect_tmp(k);collect_tmp(x)
 elif isinstance(v,list):
  for x in v:collect_tmp(x)
 elif isinstance(v,str) and v.startswith('/tmp/') and len(v)<240 and '\n' not in v and '\x00' not in v:
  p=Path(v)
  if p.is_file() and not p.is_symlink() and p.suffix in {'.json','.py','.log','.lean','.txt'}:originals.add(p)
collect_tmp(full)
full_aliases={}
for p in sorted(originals):
 digest=hashlib.sha256(p.read_bytes()).hexdigest();n=BASE+'/original-full-exercise19-peer/'+digest+p.suffix;t=ROOT/n;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert sha(n)==digest
 else:
  with t.open('xb') as f:f.write(p.read_bytes())
 full_aliases[str(p)]={'file':n,'sha256':digest}
full_ref=full_aliases[str(FULLPEER)]
candidate=copy.deepcopy(label);history=[];changed_keys={'lyapunov-mpc.html::node-'+str(x) for x in (753,755,866,868,1387)}
for index,row in enumerate(candidate['exercises']):
 record=exercises[row['inventory_key']]
 if row['source']=='SafeLearning/lyapunov-mpc.html':
  before=copy.deepcopy(row);changed=row['source_text']!=record['source_text']
  assert changed==(row['inventory_key']=='lyapunov-mpc.html::exercise-18')
  row.update({k:record[k] for k in ('source_sha256','text_sha256','source_text')})
  if changed:
   for claim in row['claims']:
    if claim['status']=='pending' and claim.get('statement_in_prose')==before['source_text']:
     claim['statement_in_prose']=record['source_text']
     claim['remaining_gaps']=list(dict.fromkeys(claim['remaining_gaps']+['Generic Assumptions1–4 robust replanning/constraint tightening must derive the explicit robustOneStepCertificate; the conditional actual switching lemmas do not supply that derivation.']))
  history.append({'kind':'exercise','index':index,'entire_original_source52_row':before,'entire_current53_outer_rebased_row':copy.deepcopy(row),'text_changed':changed})
for index,row in enumerate(candidate['material_claims']):
 if row.get('source')!='SafeLearning/lyapunov-mpc.html':continue
 assert len(row['source_unit_keys'])==1;key=row['source_unit_keys'][0];record=units[key];before=copy.deepcopy(row)
 if 'source_sha256' in row:row['source_sha256']=record['source_sha256']
 if 'source_text' in row:
  changed=row['source_text']!=record['source_text'];assert changed==(key in changed_keys)
  if changed:
   assert row['status']=='pending'
   for k in ('source_text','text_sha256'):row[k]=record[k]
   if row.get('statement_in_prose')==before['source_text']:row['statement_in_prose']=record['source_text']
 else:changed=False
 if row!=before:history.append({'kind':'material','index':index,'entire_original_source52_row':before,'entire_current53_outer_rebased_row':copy.deepcopy(row),'text_changed':changed})
new_whole_keys=[];existing_whole_bindings=[]
for key,unit in whole_units.items():
 indices=[i for i,r in enumerate(candidate['material_claims']) if r['source_unit_keys']==[key] and r['id']==key+'::semantic-review'];assert len(indices)==1
 i=indices[0];prior=copy.deepcopy(candidate['material_claims'][i])
 if prior['status']=='pending':
  candidate['material_claims'][i].update(kind='independently_reviewed_literal_material_unit',status='proved',lean_declarations=copy.deepcopy(unit['lean_declarations']),hypotheses=copy.deepcopy(unit['hypotheses']),correspondence=unit['reason'],remaining_gaps=[],independent_review={'source':full_ref['file'],'sha256':full_ref['sha256'],'original_review_time':full['reviewed_at_utc']},original_complete_literal_review_record=copy.deepcopy(unit),original_source53_entire_pending_material_row=prior)
  new_whole_keys.append(key)
 else:
  assert prior['status']=='proved'
  existing_whole_bindings.append({'source_unit_key':key,'exact_existing_whole_row_body_and_original_review_time':prior,'fresh_current53_entire_literal_decision':copy.deepcopy(unit),'fresh_review':full_ref,'fresh_review_time':full['reviewed_at_utc'],'scope':'Existing approved body/declarations/hypotheses/original review time remain exact; this fresh full-exercise correspondence is a transparent supplement.'})
assert set(new_whole_keys)=={'lyapunov-mpc.html::node-1393','lyapunov-mpc.html::node-1397'}
ex18=next(x for x in candidate['exercises'] if x['inventory_key']=='lyapunov-mpc.html::exercise-18')
ex19=next(x for x in candidate['exercises'] if x['inventory_key']=='lyapunov-mpc.html::exercise-19')
for number,g in enumerate(mpc_groups):
 component=g['original_component'];reason=component.get('reason',component.get('per_component_reason'))
 claim={'id':'core26-mpc-conditional-component-'+str(number),'kind':'independently_reviewed_precise_mathematical_component','status':'proved','statement_in_prose':component['component_id'],'lean_declarations':copy.deepcopy(component['lean_declarations']),'hypotheses':copy.deepcopy(component['hypotheses']),'correspondence':reason,'remaining_gaps':[],'independent_review':{'source':g['original_review']['file'],'sha256':g['original_review']['sha256'],'original_review_time':g['original_review_time']},'original_review_component':copy.deepcopy(component),'scope_limits':['Conditional actual finite-entry switching and safety/convergence under explicit robust one-step and terminal matrix premises; no generic Hertneck robust-MPC derivation or whole Exercise18 approval.']}
 ex18['claims'].append(copy.deepcopy(claim));material=copy.deepcopy(claim);material.update(id='lyapunov-mpc.html::node-1387::core26-conditional-component-'+str(number),source_unit_keys=['lyapunov-mpc.html::node-1387'],source='SafeLearning/lyapunov-mpc.html',source_sha256=units['lyapunov-mpc.html::node-1387']['source_sha256'],text_sha256=units['lyapunov-mpc.html::node-1387']['text_sha256'],source_text=units['lyapunov-mpc.html::node-1387']['source_text']);candidate['material_claims'].append(material)
prior_partial_ex19=copy.deepcopy(ex19)
assert ex19['status']=='partial' and len(ex19['claims'])==13 and ex19['claims'][0]['status']=='pending'
original12=copy.deepcopy(ex19['claims'][1:]);assert len(original12)==12 and all(r['status']=='proved' for r in original12)
ex19['claims']=copy.deepcopy(original12)
assert len(full_ex['components'])==4
for part in full_ex['components']:
 assert part['whole_exercise_component_approved'] is True and part['missing_clauses']==[] and part['remaining_gaps']==[]
 ex19['claims'].append({'id':'core26-exercise19-complete-part-'+part['component_id'],'kind':'independently_reviewed_complete_exercise_component','status':'proved','statement_in_prose':part.get('source_question_text',units[part['answer_source_unit_key']]['source_text']),'lean_declarations':copy.deepcopy(part['lean_declarations']),'hypotheses':copy.deepcopy(part['hypotheses']),'correspondence':part['per_component_reason'],'remaining_gaps':[],'independent_review':{'source':full_ref['file'],'sha256':full_ref['sha256'],'original_review_time':full['reviewed_at_utc']},'original_review_component':copy.deepcopy(part),'scope_limits':copy.deepcopy(full['scope_limits'])})
ex19.update(status='complete_math',prior_source53_partial_exercise_body_preserved26=prior_partial_ex19,independent_whole_source_review26=full_ref,entire_original_complete_exercise_review_record=copy.deepcopy(full_ex),entire_original_complete_exercise_review_body_and_time=full)
assert ex19['claims'][:12]==original12 and ex18['status']=='partial'
for r in source_rows:candidate['proof_files'][r['source']['file']]=r['source']['sha256']
candidate['source_sha256']['SafeLearning/lyapunov-mpc.html']=inventory['source_sha256']['SafeLearning/lyapunov-mpc.html']
candidate['current_inventory']=INV;candidate['current_inventory_sha256']=INV_SHA
candidate['counts']['exercise_statuses']={'complete_math':89,'partial':3}
candidate['counts']['material_claims']=len(candidate['material_claims']);candidate['counts']['proof_files']=len(candidate['proof_files'])
candidate['generated_at_utc']=datetime.now(timezone.utc).isoformat()
write(IDENTITY,{'status':'passed_exact_original_source52_body_and_current53_outer_literal_rebase','original_owner':ref(OLD),'fixed_label_candidate':ref(LABEL),'current_inventory':ref(INV),'source53_actual_application':ref('reports/full-coverage/source53-correction-application-v1.json'),'entire_row_history':history,'changed_material_keys':sorted(changed_keys),'all_original_semantic_review_bodies_hypotheses_and_times_preserved':True,'scope':'Outer source hashes/current literal fields only; exact before rows retained. All existing component semantics and review times unchanged.'})
candidate['future26_composed_candidate_binding']={'original_live_core25':ref(OLD),'fixed_48_nonformal_label_candidate':ref(LABEL),'source53_identity_and_original_row_history':ref(IDENTITY),'current_inventory':ref(INV),'new_proof_sources':source_rows,'earlier_whole_part_a_review':whole_ref,'entire_original_earlier_part_a_review_body_and_time':whole_peer,'whole_source_review':full_ref,'entire_original_current53_whole_exercise_review_body_and_time':full,'original_full_exercise19_review_TMP_byte_aliases':full_aliases,'existing_whole_bcd_current53_binding_supplements':existing_whole_bindings,'new_whole_material_unit_keys':new_whole_keys,'original_mpc_component_groups':mpc_groups,'scope':'48 separately reviewed nonformal labels;30 true conditional MPC components; whole1393/1397, full Exercise19(a--d) and unchanged bcd whole correspondence from fresh independent current53 review. Exercise18 remains partial; no live owner or aggregate coverage claim.','coverage_complete':False}
assert len(candidate['proof_files'])==181 and len(candidate['exercises'])==92 and len(candidate['material_claims'])==4177
assert sum(x['status']=='complete_math' for x in candidate['exercises'])==89
write(OUT,candidate)
write(REPORT,{'status':'passed_isolated_core26_source53_composition','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(OUT),'original_owner':ref(OLD),'identity_history':ref(IDENTITY),'new_source_count':4,'new_public_theorem_count':48,'new_actual_canonical_records':8,'nonformal_whole_units':48,'new_whole_mathematical_units':new_whole_keys,'whole_exercise19_approved':True,'new_mpc_conditional_component_count':30,'exercise18_status':'partial','exercise19_status':'complete_math','live_owner_written':False,'coverage_complete':False})
guard();print(json.dumps({'status':'passed','candidate':ref(OUT),'integrity':ref(REPORT)}))
