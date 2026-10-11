from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import json,hashlib,copy,re
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/core27-current55-eleven-component-draft-v1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':str(n),'sha256':sha(path(n))}
def check(r):assert sha(path(r['file']))==r['sha256'],r;return read(r['file'])
def zero(x):
 vals=[x[k] for k in ('actual_exit_code','exit_code') if k in x];assert vals and all(type(v)is int and v==0 for v in vals)
n=B/'core27-current55-eleven-component-readiness-draft-v1.json';assert sha(n)=='eafe5b010a9afda1bb152c0d0562f49ee2ccb644a19ad9b0bc6395435a64901e';p=read(n);d=check(p['candidate']);i=check(p['identity']);o=check(p['entire_original_ledger']);iv=check(p['current_inventory'])
assert p['candidate']['sha256']=='3107125ebded9e79bdc84be0b9601263ed8d8a184e3490e66e664dd6d411d2ed' and p['identity']['sha256']=='38016b54239e2c911a6d6e23b0776a806ac15ae08b517f1921d937c25394377e'
assert sha(R/'book/coverage/core.json')==p['entire_original_ledger']['sha256']=='1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38' and o==read('book/coverage/core.json')
assert p['current_inventory']['sha256']=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf' and sha(R/'book/coverage/inventory.json')==p['current_inventory']['sha256']
assert i['original']==p['entire_original_ledger'] and i['candidate']==p['candidate'] and i['inverse_restores_entire_original_body_and_all_times'] is True
restored=copy.deepcopy(d)
for row in reversed(i['exact_field_changes']):
 z=restored
 for k in row['path'][:-1]:z=z[k]
 k=row['path'][-1]
 if row.get('operation')=='append':
  assert z[k][row['original_length']:]==row['appended'];z[k]=z[k][:row['original_length']]
 else:
  assert (k in z if isinstance(z,dict) else k<len(z))==row['after_present'];assert z[k]==row['after']
  if row['before_present']:z[k]=row['before']
  else:del z[k]
assert restored==o
assert {k for k in d if d[k]!=o.get(k)}=={'current_inventory','current_inventory_sha256','source_sha256','exercises','material_claims','counts'}
assert d['proof_files']==o['proof_files'] and len(d['proof_files'])==181 and d['generated_at_utc']==o['generated_at_utc']
assert d['counts']==o['counts']|{'material_claims':4210};assert len(d['exercises'])==len(o['exercises'])==92;assert len(d['material_claims'])==4210 and len(o['material_claims'])==4177
old_iv=read(o['current_inventory']);assert sha(path(o['current_inventory']))==o['current_inventory_sha256']
em={x['key']:x for x in iv['exercises']};oe={x['key']:x for x in old_iv['exercises']};um={x['key']:x for x in iv['material_source_units']};ou={x['key']:x for x in old_iv['material_source_units']}
components=[];peers=[]
for idx,row in enumerate(p['original_full_component_peers']):
 q=check(row);assert q==row['entire_original_body_and_time'] and q['errors']==[] and q['reviewed_at_utc'];assert q['whole_exercise_approved'] is False and q['whole_material_unit_approved'] is False;peers.append(q)
 groups=q['components'] if idx<2 else q['two_new_precise_components'] if idx==2 else [q['new_component']]
 for c in groups:
  assert c['missing_clauses']==[];cid=c.get('component_id',c.get('id'));names=c.get('lean_declarations',c.get('declarations'));reason=c.get('per_component_reason',c.get('reason'));assert cid and names and reason
  components.append({'id':'core27-mpc-precise-component-'+cid,'kind':'independently_reviewed_precise_mathematical_component','status':'proved','statement_in_prose':cid,'lean_declarations':names,'hypotheses':c['hypotheses'],'correspondence':reason,'remaining_gaps':[],'independent_review':{'source':row['file'],'sha256':row['sha256'],'original_review_time':q['reviewed_at_utc']},'original_review_component':copy.deepcopy(c),'scope_limits':['Exact reviewed components only. Whole Assumptions1–4 robust replanning, Exercise18(d), and source units737/739/1387 remain pending.']})
assert len(components)==11;names=[n for c in components for n in c['lean_declarations']];assert len(names)==len(set(names))==11
src=path(p['exact_tmp_source']['file']);assert sha(src)==p['exact_tmp_source']['sha256']=='09fc59984a9e53f86e8ddfa82b2bee79f163aeffd5dc173b88eb6d8fc9c8000c';assert src.read_text()==peers[3]['entire_source'];assert set(names)==set(peers[3]['all_public_theorem_names']);assert len(re.findall(r'^theorem\s+',src.read_text(),re.M))==11
assert p['planned_canonical_source'] not in d['proof_files']
if (R/p['planned_canonical_source']).exists():assert sha(R/p['planned_canonical_source'])==p['exact_tmp_source']['sha256']
assert p['new_public_theorem_count']==11 and p['canonical_pair_execution_count']==0 and p['eligible_for_owner_integration_or_selection'] is False and p['coverage_complete'] is False and i['canonical_pair_execution_count']==0 and i['canonical_or_owner_write_claimed'] is False
assert p['whole_exercise18_and_material737_739_1387_pending'] is True and p['all92_exercise_statuses_unchanged'] is True and p['old181_proof_mapping_unchanged'] is True
for a,b in zip(o['exercises'],d['exercises']):
 key=a['inventory_key'];oa=copy.deepcopy(oe[key]);na=copy.deepcopy(em[key]);oa.pop('source_sha256');na.pop('source_sha256');assert oa==na
 expected=copy.deepcopy(a);expected['source_sha256']=iv['source_sha256'][a['source']];assert b['source_text']==em[key]['source_text'] and b['text_sha256']==em[key]['text_sha256'] and b['status']==a['status']
 if key=='lyapunov-mpc.html::exercise-18':expected['claims']+=copy.deepcopy(components);assert b['status']=='partial'
 assert b==expected
assert Counter(x['status'] for x in d['exercises'])==Counter(x['status'] for x in o['exercises'])
changed=[]
for a,b in zip(o['material_claims'],d['material_claims'][:4177]):
 expected=copy.deepcopy(a)
 if a.get('source') in iv['source_sha256']:expected['source_sha256']=iv['source_sha256'][a['source']]
 keys=a['source_unit_keys'];changes=[k for k in keys if ou[k]['source_text']!=um[k]['source_text']]
 if changes:
  assert len(keys)==1 and keys[0] in {'lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739'} and a['status']=='pending' and a['lean_declarations']==[]
  u=um[keys[0]];assert a['statement_in_prose']==a['source_text']==ou[keys[0]]['source_text'];expected.update(source_text=u['source_text'],statement_in_prose=u['source_text'],text_sha256=u['text_sha256']);changed.append(a['id'])
 assert b==expected
assert changed==i['changed_pending_literal_rows'] and set(changed)=={'lyapunov-mpc.html::node-737::semantic-review','lyapunov-mpc.html::node-739::semantic-review'}
expected_rows=[]
for k in ['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739','lyapunov-mpc.html::node-1387']:
 assert any(k in x['source_unit_keys'] and x['status']=='pending' for x in d['material_claims'][:4177]);u=um[k]
 for c in components:
  x=copy.deepcopy(c);x['id']=k+'::'+x['id'];x.update(source_unit_keys=[k],source=u['source'],source_sha256=u['source_sha256'],text_sha256=u['text_sha256'],source_text=u['source_text']);expected_rows.append(x)
assert d['material_claims'][4177:]==expected_rows
for n,h in o['source_sha256'].items():assert d['source_sha256'][n]==(iv['source_sha256'][n] if n.startswith('SafeLearning/') else h)
actual_name='reports/full-coverage/core27-current55-eleven-component-draft-preparation-execution-v1.json';actual=read(actual_name);zero(actual);helper=check(p['prepared_by']) if p['prepared_by']['file'].endswith('.json') else path(p['prepared_by']['file']).read_text();assert sha(path(p['prepared_by']['file']))==p['prepared_by']['sha256']=='87c0fc7653b7b12360f039043e852a18775a245a477891b1b63c7bf8cdbd760f'
producer_relative=str(path(p['prepared_by']['file']).relative_to(R))
assert actual['actual_command']==['python3',producer_relative] and actual['actual_workdir']==str(R) and actual['helper_sha256_before']==actual['helper_sha256_after']=={producer_relative:p['prepared_by']['sha256']} and sha(path(actual['log']))==actual['log_sha256']
sel=read('reports/full-coverage/checkpoint-26-selection.json');assert len(sel['proof_files'])==1167
assets={n:h for n,h in read('reports/full-coverage/checkpoint-26-manifest.json')['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
app=read('reports/full-coverage/source54-55-corrections-application-v1.json')
for row in app['applications']:assets[row['source_after']['file']]=row['source_after']['sha256']
protected={n:r['sha256'] for n,r in sel['proof_files'].items()}|assets
owners={'core':'1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38','foundations':'60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a','applied':'a0e087260288c8e8abc45eb0806eb3b09d17da463f5e918966c3a0686f3976a6','modules':'c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231','applied-promotions':'fa58595aacac0b82f9cd9d3bfe41718365113a2ebf76879001edcf3ab4b68fcb'}
protected.update({'book/coverage/'+n+'.json':h for n,h in owners.items()});protected['book/coverage/inventory.json']=p['current_inventory']['sha256'];protected['book/coverage/material-corrections.json']='21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
for n,h in protected.items():assert sha(R/n)==h,n
result={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Root authored isolated component composer','readiness':ref(B/'core27-current55-eleven-component-readiness-draft-v1.json'),'candidate':p['candidate'],'identity':p['identity'],'actual_preparation_execution':ref(actual_name),'original_preparer':p['prepared_by'],'original_component_peers':[{'file':x['file'],'sha256':x['sha256'],'entire_original_body_and_time':x['entire_original_body_and_time']} for x in p['original_full_component_peers']],'mechanics':{'whole_candidate_inverse_restores_original_source53_core_ledger':True,'all92_exercise_statuses_unchanged':True,'all181_old_proof_metadata_unchanged':True,'all_old_claims_and_review_bodies_times_preserved':True,'changed_pending_literal_rows':changed,'fresh_precise_exercise_components':11,'fresh_material_component_rows':33,'unique_new_public_exports':11,'source55_identity_updates_only':True,'selected26_sources_exact':1167,'current55_assets_exact':31,'installed26_owners_exact':5},'whole_exercise18_and_units737_739_1387_approved':False,'canonical_pair_execution_count':0,'integration_or_selection_approved':False,'new_semantic_decision_or_retiming':False,'scope':'Read-only exact isolated draft mechanics and original four-peer correspondence. Eleven previously reviewed local first-successor/norm/convexity components retain explicit domain, continuity, positive lambda and tightening hypotheses. All old exercise decisions remain; full robust shifted-horizon/terminal recursion and the entire printed guarantees remain pending. No fresh mathematical, canonical-pair or live/global approval.'}
O=Path('/tmp/core27-current55-eleven-component-draft-independent-foundations-check-result-v3.json');assert not O.exists();O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','components':11,'material_component_rows':33,'old_exercise_statuses':92,'old_proof_rows':181,'canonical_pairs':0}))
