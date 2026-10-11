"""Independent read-only Core26 composition/body/evidence checker; no producer execution."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/core26-composed-candidate-independent-foundations-observation-v1.json')
C='book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-v1.json'
CS='1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38'
OLD='book/coverage/core.json';OS='4e96c717055187cfc24e9e60a19a7d183499336570d99fbf9954ff199ff49572'
INV='book/coverage/inventory-after-correction53.json';IS='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
HELP='book/coverage/checks/prepare_root_core26_composed_candidate_source53_v3.py'
SEL='reports/full-coverage/checkpoint-25-selection.json';MAN='reports/full-coverage/checkpoint-25-manifest.json'
def path(n):return Path(n) if str(n).startswith('/') else ROOT/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':str(n),'sha256':sha(n)}
def checkref(r):
 assert sha(r['file'])==r['sha256'],r['file']
 return read(r['file'])
def zero(d):
 vs=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
 assert vs and all(type(v)is int and v==0 for v in vs)
def canonical(n):
 p=Path(n);assert isinstance(n,str) and str(p)==n and not p.is_absolute() and '..' not in p.parts
 assert path(n).resolve().is_relative_to(ROOT)
assert sha(C)==CS and sha(OLD)==OS and sha(INV)==IS==sha('book/coverage/inventory.json')
c=read(C);old=read(OLD);b=c['future26_composed_candidate_binding'];h=checkref(b['source53_identity_and_original_row_history']);label=checkref(b['fixed_48_nonformal_label_candidate'])
assert checkref(b['original_live_core25'])==old and h['original_owner']==ref(OLD)
inv=read(INV);units={r['key']:r for r in inv['material_source_units']};exs={r['key']:r for r in inv['exercises']}
full=checkref(b['whole_source_review']);assert full==b['entire_original_current53_whole_exercise_review_body_and_time']
assert full['errors']==[] and full['whole_exercise_approved'] is True and full['missing_clauses']==full['remaining_gaps']==[]
assert full['current_inventory']==ref(INV)
originaltmp='/tmp/lyapunov-current53-exercise19-all-four-parts-independent-foundations-full-review26-final-v1.json'
assert ref(originaltmp)['sha256']=='9fc6afef3d329176ee7e543882eacabaa7d2fca4ca2434de6db4cc5410db641d'
assert full==read(originaltmp)
for original,alias in b['original_full_exercise19_review_TMP_byte_aliases'].items():
 canonical(alias['file']);assert sha(original)==alias['sha256']==sha(alias['file'])
assert b['original_full_exercise19_review_TMP_byte_aliases'][originaltmp]==b['whole_source_review']
assert checkref(b['earlier_whole_part_a_review'])==b['entire_original_earlier_part_a_review_body_and_time']
fullunits={u['source_unit_key']:u for u in full['material_units']}
assert set(fullunits)=={'lyapunov-mpc.html::node-'+str(k) for k in (1393,1397,1399,1401,1403)}
for key,u in fullunits.items():
 assert u['entire_inventory_record']==units[key] and u['whole_unit_approved'] is True and u['missing_clauses']==u['remaining_gaps']==[]
assert full['exercise_records'][0]['entire_inventory_record']==exs['lyapunov-mpc.html::exercise-19']
# Entire-candidate reverse, rather than comparing a handful of fields.
r=copy.deepcopy(c);rb=r.pop('future26_composed_candidate_binding')
ex19i=next(i for i,e in enumerate(r['exercises']) if e['inventory_key']=='lyapunov-mpc.html::exercise-19')
ex18i=next(i for i,e in enumerate(r['exercises']) if e['inventory_key']=='lyapunov-mpc.html::exercise-18')
e19=r['exercises'][ex19i];prior19=e19['prior_source53_partial_exercise_body_preserved26']
assert prior19['status']=='partial' and len(prior19['claims'])==13 and prior19['claims'][0]['status']=='pending'
assert e19['status']=='complete_math' and e19['claims'][:12]==prior19['claims'][1:] and len(e19['claims'])==16
assert e19['entire_original_complete_exercise_review_record']==full['exercise_records'][0]
assert e19['entire_original_complete_exercise_review_body_and_time']==full and e19['independent_whole_source_review26']==b['whole_source_review']
for actual,part in zip(e19['claims'][12:],full['exercise_records'][0]['components']):
 assert actual['original_review_component']==part and actual['lean_declarations']==part['lean_declarations'] and actual['hypotheses']==part['hypotheses']
 assert actual['correspondence']==part['per_component_reason'] and actual['remaining_gaps']==[] and actual['scope_limits']==full['scope_limits']
 assert actual['independent_review']=={'source':b['whole_source_review']['file'],'sha256':b['whole_source_review']['sha256'],'original_review_time':full['reviewed_at_utc']}
 assert actual['statement_in_prose']==part.get('source_question_text',units[part['answer_source_unit_key']]['source_text'])
r['exercises'][ex19i]=copy.deepcopy(prior19)
# Check the exact original MPC peer chain, including embedded body/time and archived TMP originals.
mpc=checkref(b['new_proof_sources'][0]['readiness']);cur=checkref(mpc['original_full_source_peer']);curref=mpc['original_full_source_peer'];expectedgroups=[]
chainkeys={'preserved_original25_component_review','preserved_original_eighteen_component_review','preserved_original_fifteen_component_review','preserved_original_thirteen_component_review','preserved_original_seven_component_review'}
while True:
 assert cur['errors']==[] and cur['whole_exercise_approved'] is False
 for u in cur['material_units']:
  if u['source_unit_key']=='lyapunov-mpc.html::node-1387':
   for component in u['components']:
    assert component['missing_clauses']==[] and component['decision'].startswith('approved')
    expectedgroups.append({'original_component':component,'original_review':curref,'original_review_time':cur['reviewed_at_utc']})
 links=[v for k,v in cur.items() if k in chainkeys and isinstance(v,dict) and 'entire_original_body_and_time' in v and 'record' in v]
 if not links:break
 assert len(links)==1
 curref=links[0]['record'];cur=links[0]['entire_original_body_and_time']
 rr=mpc['original_TMP_byte_copies'][curref['file']] if curref['file'].startswith('/tmp/') else curref
 assert rr['sha256']==curref['sha256'] and checkref(rr)==cur
assert expectedgroups==b['original_mpc_component_groups'] and len(expectedgroups)==30
assert len({n for g in expectedgroups for n in g['original_component']['lean_declarations']})==30
assert len(r['material_claims'])==4177 and len(label['material_claims'])==4147
e18=r['exercises'][ex18i];assert e18['status']=='partial'
for i,(g,claim,material) in enumerate(zip(expectedgroups,e18['claims'][-30:],r['material_claims'][-30:])):
 co=g['original_component'];reason=co.get('reason',co.get('per_component_reason'))
 assert claim['original_review_component']==co and claim['lean_declarations']==co['lean_declarations'] and claim['hypotheses']==co['hypotheses'] and claim['correspondence']==reason
 assert claim['independent_review']=={'source':g['original_review']['file'],'sha256':g['original_review']['sha256'],'original_review_time':g['original_review_time']}
 assert claim['id']=='core26-mpc-conditional-component-'+str(i) and claim['remaining_gaps']==[] and claim['status']=='proved'
 expected=copy.deepcopy(claim);expected.update(id='lyapunov-mpc.html::node-1387::core26-conditional-component-'+str(i),source_unit_keys=['lyapunov-mpc.html::node-1387'],source='SafeLearning/lyapunov-mpc.html',source_sha256=units['lyapunov-mpc.html::node-1387']['source_sha256'],text_sha256=units['lyapunov-mpc.html::node-1387']['text_sha256'],source_text=units['lyapunov-mpc.html::node-1387']['source_text'])
 assert material==expected
 del expected
r['material_claims']=r['material_claims'][:-30];e18['claims']=e18['claims'][:-30]
assert set(b['new_whole_material_unit_keys'])=={'lyapunov-mpc.html::node-1393','lyapunov-mpc.html::node-1397'}
for key in b['new_whole_material_unit_keys']:
 ix=next(i for i,x in enumerate(r['material_claims']) if x['id']==key+'::semantic-review' and x['source_unit_keys']==[key]);row=r['material_claims'][ix];u=fullunits[key]
 assert row['status']=='proved' and row['original_complete_literal_review_record']==u and row['lean_declarations']==u['lean_declarations'] and row['hypotheses']==u['hypotheses'] and row['correspondence']==u['reason'] and row['remaining_gaps']==[]
 assert row['independent_review']['original_review_time']==full['reviewed_at_utc']
 prior=row['original_source53_entire_pending_material_row'];expected=copy.deepcopy(prior)
 expected.update(kind='independently_reviewed_literal_material_unit',status='proved',lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['reason'],remaining_gaps=[],independent_review={'source':b['whole_source_review']['file'],'sha256':b['whole_source_review']['sha256'],'original_review_time':full['reviewed_at_utc']},original_complete_literal_review_record=u,original_source53_entire_pending_material_row=prior)
 assert row==expected;r['material_claims'][ix]=copy.deepcopy(prior)
assert len(b['existing_whole_bcd_current53_binding_supplements'])==3
for sup in b['existing_whole_bcd_current53_binding_supplements']:
 key=sup['source_unit_key'];row=next(x for x in r['material_claims'] if x['id']==key+'::semantic-review' and x['source_unit_keys']==[key])
 assert row==sup['exact_existing_whole_row_body_and_original_review_time'] and row['status']=='proved'
 assert sup['fresh_current53_entire_literal_decision']==fullunits[key] and sup['fresh_review']==b['whole_source_review'] and sup['fresh_review_time']==full['reviewed_at_utc']
# All source53 outer updates must be explicitly reversible and justified by actual current records.
seen=set();changed=set()
for item in h['entire_row_history']:
 kind,index=item['kind'],item['index'];assert (kind,index) not in seen;seen.add((kind,index))
 seq=r['exercises'] if kind=='exercise' else r['material_claims'];origseq=label['exercises'] if kind=='exercise' else label['material_claims']
 before=item['entire_original_source52_row'];after=item['entire_current53_outer_rebased_row']
 assert before==origseq[index] and seq[index]==after
 expected=copy.deepcopy(before)
 key=before['inventory_key'] if kind=='exercise' else before['source_unit_keys'][0];record=exs[key] if kind=='exercise' else units[key]
 assert before['source']=='SafeLearning/lyapunov-mpc.html'
 if kind=='exercise':
  expected.update({k:record[k] for k in ('source_sha256','text_sha256','source_text')})
  if item['text_changed']:
   assert key=='lyapunov-mpc.html::exercise-18'
   for claim in expected['claims']:
    if claim['status']=='pending' and claim.get('statement_in_prose')==before['source_text']:
     claim['statement_in_prose']=record['source_text'];gap='Generic Assumptions1–4 robust replanning/constraint tightening must derive the explicit robustOneStepCertificate; the conditional actual switching lemmas do not supply that derivation.'
     if gap not in claim['remaining_gaps']:claim['remaining_gaps']=claim['remaining_gaps']+[gap]
 else:
  if 'source_sha256' in expected:expected['source_sha256']=record['source_sha256']
  if item['text_changed']:
   assert expected['status']=='pending';changed.add(key)
   expected.update({k:record[k] for k in ('source_text','text_sha256')})
   if expected.get('statement_in_prose')==before['source_text']:expected['statement_in_prose']=record['source_text']
 assert after==expected
 seq[index]=copy.deepcopy(before)
assert changed==set(h['changed_material_keys'])=={'lyapunov-mpc.html::node-'+str(k) for k in (753,755,866,868,1387)}
assert len(b['new_proof_sources'])==4 and sum(s['public_count'] for s in b['new_proof_sources'])==48
actualrefs=[];newnames=[]
for source in b['new_proof_sources']:
 sr=source['source'];canonical(sr['file']);assert sha(sr['file'])==sr['sha256']==sha(source['source_snapshot']['file'])
 body=path(sr['file']).read_text();names=re.findall(r'^(?:theorem|lemma)\s+(\w+)',body,re.M);assert len(names)==source['public_count'];newnames+=names
 readiness=checkref(source['readiness']);assert len(source['pair'])==2
 kinds=[]
 for pair in source['pair']:
  rr=pair.get('record',pair);d=checkref(rr);zero(d);actualrefs.append(rr)
  if 'entire_original_actual_record' in pair:assert d==pair['entire_original_actual_record']
  assert d['source']==sr['file'] and d['source_sha256_before']==d['source_sha256_after']==sr['sha256'] and d['source_unchanged'] is True
  assert d['actual_workdir']==str(ROOT/'verification/lean') and sha(d['log'])==d['log_sha256']
  rel=sr['file'].removeprefix('verification/lean/');module=rel.removesuffix('.lean').replace('/','.')
  if d['command']==['lake','env','lean',rel]:kinds.append('standalone')
  elif d['command']==['lake','build',module]:kinds.append('named')
  else:raise AssertionError(d['command'])
 assert sorted(kinds)==['named','standalone']
 assert sr['file'] not in old['proof_files'] and r['proof_files'].pop(sr['file'])==sr['sha256']
for k in ('source_sha256','current_inventory','current_inventory_sha256','counts','generated_at_utc'):r[k]=copy.deepcopy(label[k])
assert r==label,'entire composed candidate reverse differs from fixed label candidate'
# The original48 label changes are the only differences from the installed Core25 body.
reverse_label=copy.deepcopy(label);lb=reverse_label.pop('future26_label_material_candidate_binding')
assert checkref(lb['prior_isolated_owner25_candidate'])==old and label['exercises']==old['exercises'] and label['proof_files']==old['proof_files']
labelchanges=[]
for i,(a,z) in enumerate(zip(old['material_claims'],reverse_label['material_claims'])):
 if a!=z:
  assert a['status']=='pending' and z['status']=='not_a_formal_claim' and z['original_source52_entire_pending_material_row']==a
  labelchanges.append(i);reverse_label['material_claims'][i]=copy.deepcopy(a)
assert len(labelchanges)==48
# The label preparer may have its own preparation timestamp only.
reverse_label['generated_at_utc']=old['generated_at_utc']
assert reverse_label==old,'entire label candidate reverse differs from installed owner'
for rr in [lb['original_full118_label_peer']]:checkref(rr)
for execution in ['reports/full-coverage/root-core26-composed-candidate-execution-v1.json','reports/full-coverage/root-core26-composed-candidate-execution-v2.json']:
 d=read(execution);expected=1 if execution.endswith('-v1.json') else 0
 assert type(d['actual_exit_code'])is int and d['actual_exit_code']==expected
 assert d['actual_workdir']==str(ROOT) and sha(d['log'])==d['log_sha256']
 assert d['helper_sha256_before']==d['helper_sha256_after']
 for name,digest in d['helper_sha256_before'].items():assert sha(name)==digest
assert read('reports/full-coverage/root-core26-composed-candidate-execution-v2.json')['actual_command']==['python3',HELP]
# Genuine preserved baseline sources and current asset/owner guards; no full audit execution inferred.
sel=read(SEL);man=read(MAN);assert len(sel['proof_files'])==sel['proof_file_count']==1156
for n,v in sel['proof_files'].items():assert sha(n)==v['sha256']
assetcount=0
for n,digest in man['working_inputs_sha256'].items():
 if n.startswith('SafeLearning/') or n in {'book/coverage/'+o+'.json' for o in ('core','foundations','applied','modules','applied-promotions')}:
  if n=='SafeLearning/lyapunov-mpc.html':digest='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
  assert sha(n)==digest
  if n.startswith('SafeLearning/'):assetcount+=1
assert assetcount==31
integrity=read('book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-integrity-v1.json')
assert integrity['errors']==[] and integrity['candidate']==ref(C) and integrity['new_source_count']==4 and integrity['new_public_theorem_count']==48 and integrity['new_actual_canonical_records']==8 and integrity['exercise18_status']=='partial' and integrity['exercise19_status']=='complete_math' and integrity['live_owner_written'] is False
assert sha(C)==CS and sha(OLD)==OS and sha(INV)==IS
report={'status':'independent_full_core26_composed_candidate_mechanics_passed','errors':[],'reviewer':'independent_foundations_agent','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(C),'original_owner':ref(OLD),'identity_history':b['source53_identity_and_original_row_history'],'integrity':ref('book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-integrity-v1.json'),'actual_candidate_builder':ref('reports/full-coverage/root-core26-composed-candidate-execution-v2.json'),'original_actual_composer_failure':ref('reports/full-coverage/root-core26-composed-candidate-execution-v1.json'),'original_semantic_full_exercise19_peer':b['whole_source_review'],'original_semantic_review_time':full['reviewed_at_utc'],'entire_candidate_and_label_inverse_passed':True,'entire_original92_exercise_bodies_and_4147_material_baseline_rows_reversible':True,'earlier_twelve_exercise19_component_bodies_reasons_hypotheses_times_preserved':True,'new_complete_exercise19_parts':4,'new_whole_physical_units':b['new_whole_material_unit_keys'],'three_existing_bcd_whole_bodies_and_times_unchanged':True,'exact_original_mpc_component_bodies_and_times':30,'separately_reviewed_nonformal_labels':48,'new_source_count':4,'new_public_export_count':48,'actual_canonical_record_count':8,'canonical_records':actualrefs,'full_original_TMP_review_byte_alias_count':len(b['original_full_exercise19_review_TMP_byte_aliases']),'all1156_selected_baseline_sources_exact':True,'all31_current_assets_only_authorized_source53_Lyap_delta':True,'all_five_installed25_owner_bytes_exact':True,'exercise18_remains_partial':True,'coverage_complete':False,'no_live_owner_source_selection_publication_or_compiler_execution':True,'scope':'Mechanical binding and exact full-body/time preservation only. Fresh mathematical approvals are the original independent whole Exercise19 review; original conditional MPC and nonformal label decisions are unchanged. Actual eight standalone/named records are reused, with warnings/failures retained; no aggregate26 or deployment claim.'}
assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','report':ref(str(OUT))}))
