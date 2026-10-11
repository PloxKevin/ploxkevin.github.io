from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');O=Path('/tmp/core28-current60-identity-v1/core28-current60-identity-offer-draft-v2.json');OUT=Path('/tmp/core28-current60-identity-independent-foundations-findings-v1.json')
def p(n):
 q=Path(n);return q if q.is_absolute()else R/q
def h(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def j(n):return json.loads(p(n).read_bytes())
def ref(n):
 q=p(n);return {'file':str(q.relative_to(R))if q.is_relative_to(R)else str(q),'sha256':h(q)}
def ck(a):assert h(a['file'])==a['sha256'],a['file'];return p(a['file'])
def zero(d):
 ks=[k for k in ['actual_exit_code','exit_code','actual_runner_exit_code']if k in d];assert ks and all(type(d[k])is int and d[k]==0 for k in ks)
def aliases(d,ks,value):
 present=[k for k in ks if k in d];assert present and all(d[k]==value for k in present)
started=datetime.now(timezone.utc).isoformat();assert not OUT.exists()
assert h(O)=='dc93c3139da0d07d4708f50de1805e59cd8b3f0607b90fa3ef7556fb258e83a8';offer=j(O);assert offer['errors']==[]and offer['coverage_complete']is False
ready=j('book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json');protected=ready['protected_inputs_sha256']
def guard():
 for n,s in protected.items():assert h(n)==s,n
guard()
closed={str(O):h(O)}
for n,s in offer['required_evidence_artifacts_sha256'].items():assert h(n)==s,n;closed[n]=s
for k in ['candidate','identity_sidecar','identity_integrity','candidate_builder','actual_isolated_candidate_preparation','actual_candidate_preparation_raw_log','actual_candidate_preparation_runner','original_unexecuted_offer_draft','base_selection']:
 q=ck(offer[k]);closed[str(q)]=h(q)
assert h(offer['candidate_builder']['file'])=='9b678b163fb4136ea513d51bdf2acbb8e5509690a6f7402a30b48de0e060024b'
candidate=j(offer['candidate']['file']);side=j(offer['identity_sidecar']['file']);integrity=j(offer['identity_integrity']['file'])
assert side['errors']==integrity['errors']==[]
original=ck(side['original_installed27_exact_bytes']);old=j(original)
assert h(original)==h('book/coverage/core.json')=='0bf99e01c47c7b9fa18488fdc3104c189e3977597c15f1c7e20253afad1245c0'
oldinv=j(ck(side['historical_inventory']));newinv=j(ck(side['current_inventory']))
assert h(side['current_inventory']['file'])==h('book/coverage/inventory.json')==offer['inventory_sha256']=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert offer['inventory']=='book/coverage/inventory-after-correction60.json'
assert offer['proof_files']=={}and offer['new_actual_paired_records']==[]and offer['new_material_keys']==[]
assert offer['source_sha256']==candidate['source_sha256'] and offer['counts']==candidate['counts']==old['counts']
assert len(old['exercises'])==92 and len(old['material_claims'])==4210 and len(old['proof_files'])==182
assert candidate['proof_files']==old['proof_files']
page='SafeLearning/lyapunov-mpc.html';keys={'lyapunov-mpc.html::node-'+str(n)for n in [735,737,739]};scope=set(old['scope_pages'])
assert {s for s in scope if oldinv['source_sha256'][s]!=newinv['source_sha256'][s]}=={page}
maps={}
for field,count in [('exercises',92),('material_source_units',3982)]:
 a={x['key']:x for x in oldinv[field]if x['source']in scope};b={x['key']:x for x in newinv[field]if x['source']in scope};assert len(a)==len(b)==count and set(a)==set(b)
 changed={k for k in a if {f:v for f,v in a[k].items()if f!='source_sha256'}!={f:v for f,v in b[k].items()if f!='source_sha256'}}
 assert changed==(set()if field=='exercises'else keys)
 maps[field]=(a,b)
oldunits,newunits=maps['material_source_units']
assert side['entire_three_original_and_current_physical_records']=={k:{'original55':oldunits[k],'current60':newunits[k]}for k in sorted(keys)}
expected=copy.deepcopy(old);expected['source_sha256'][page]=newinv['source_sha256'][page];expected['current_inventory']='book/coverage/inventory-after-correction60.json';expected['current_inventory_sha256']=offer['inventory_sha256']
rebound={};changedrows=[]
for field in ['exercises','material_claims']:
 count=0
 for row in expected[field]:
  if row.get('source')==page:assert row['source_sha256']==oldinv['source_sha256'][page];row['source_sha256']=newinv['source_sha256'][page];count+=1
 rebound[field]=count
for index,row in enumerate(expected['material_claims']):
 hit=set(row.get('source_unit_keys',[]))&keys
 if not hit:continue
 assert len(hit)==1 and len(row['source_unit_keys'])==1;k=next(iter(hit));before=old['material_claims'][index]
 assert row['source_text']==oldunits[k]['source_text']and row['text_sha256']==oldunits[k]['text_sha256']
 row['source_text']=newunits[k]['source_text'];row['text_sha256']=newunits[k]['text_sha256']
 if row['id']==k+'::semantic-review':assert row['status']=='pending'and row['lean_declarations']==[];row['statement_in_prose']=newunits[k]['source_text']
 else:assert row['status']=='proved'
 changedrows.append({'claim_id':row['id'],'unit_key':k,'status_unchanged':row['status'],'original_exact_claim_body':before})
assert rebound==side['rebound_direct_source_identity_counts']=={'exercises':20,'material_claims':577}
assert len(changedrows)==25 and side['entire_original_changed_claim_bodies']==changedrows
assert sum(r['status_unchanged']=='pending'for r in changedrows)==3 and sum(r['status_unchanged']=='proved'for r in changedrows)==22
binding=candidate['source60_core_identity_binding'];assert binding['inventory']==side['current_inventory']and binding['identity_sidecar']==offer['identity_sidecar']and binding['original_installed27_core']==side['original_installed27_exact_bytes']and binding['new_proofs']==binding['new_status_promotions']==0 and binding['whole_exercise18_still_partial']is True
expected['source60_core_identity_binding']=binding;assert candidate==expected
inverse=copy.deepcopy(candidate);inverse.pop('source60_core_identity_binding');inverse['source_sha256']=copy.deepcopy(old['source_sha256']);inverse['current_inventory']=old['current_inventory'];inverse['current_inventory_sha256']=old['current_inventory_sha256']
for field in ['exercises','material_claims']:
 for row in inverse[field]:
  if row.get('source')==page:row['source_sha256']=oldinv['source_sha256'][page]
restore={r['claim_id']:r['original_exact_claim_body']for r in changedrows};inverse['material_claims']=[copy.deepcopy(restore.get(r['id'],r))for r in inverse['material_claims']]
assert inverse==old
for field in ['exercises','material_claims']:
 for before,after in zip(old[field],candidate[field]):
  assert before['status']==after['status']
  if before.get('source')!=page:assert before==after
for n,s in candidate['source_sha256'].items():assert h(n)==s,n
for n,s in candidate['proof_files'].items():
 assert type(s)is str and n in ready['protected_inputs_sha256'] and s==h(n)==ready['protected_inputs_sha256'][n]
for r in changedrows:
 c=r['original_exact_claim_body']
 if c['status']=='proved':
  q=c['independent_review'];assert h(q['source'])==q['sha256'];closed[q['source']]=q['sha256']
  assert c['remaining_gaps']==[]and c['scope_limits'] and all('pending'in x for x in c['scope_limits'])
actual=j(offer['actual_isolated_candidate_preparation']['file']);zero(actual)
assert actual['status']=='passed_actual_isolated_core_identity_preparation'
aliases(actual,['command','actual_command'],['/home/oxrexkevin/.local/oss-cad-suite/bin/tabbypy3','/tmp/prepare-core28-current60-identity-candidate-v1.py'])
aliases(actual,['cwd','working_directory','actual_workdir'],str(R))
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={offer['candidate_builder']['file']:offer['candidate_builder']['sha256']}
assert h(actual['log'])==actual['log_sha256']==offer['actual_candidate_preparation_raw_log']['sha256']
assert actual['compiler_or_live_owner_written']is False
app=j(ck(side['actual_source56_to60_application']));assert app['status']=='passed_actual_source56_to60_corrections_full29_inventory_owner_identity_rebase_pending' and app['five_installed27_owner_ledgers_unchanged']is True and app['selected27_proof_sources_unchanged']==1175
appactual=j(ck(side['actual_source56_to60_execution']));zero(appactual);assert h(appactual['log'])==appactual['log_sha256'];assert appactual['helper_sha256_before']==appactual['helper_sha256_after']
assert integrity['candidate']==offer['candidate']and integrity['identity_sidecar']==offer['identity_sidecar']and integrity['exact_inverse_restores_installed27_entire_core']is True and integrity['new_proof_sources']==integrity['new_counts_or_status_promotions']==0
assert side['new_proofs_or_counts_or_status_promotions']==0 and side['whole_exercise18_or_whole737_739_approved']is False
guard()
out={'status':'passed_independent_exact_forward_inverse_core28_current60_identity_mechanics','errors':[],'reviewer':'/root/foundations_recovery28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reader_started_at_utc':started,'candidate':offer['candidate'],'offer':ref(O),'identity_sidecar':offer['identity_sidecar'],'identity_integrity':offer['identity_integrity'],'actual_author_preparation':offer['actual_isolated_candidate_preparation'],'original_installed27_core':side['original_installed27_exact_bytes'],'inventory':ref('book/coverage/inventory-after-correction60.json'),'full_code_and_all25_original_component_context_rows_read':True,'all92_exercises_4210_claims182_proof_rows_same_status_counts_and_math':True,'exact_forward_current60_inventory_binding':True,'exact_inverse_restores_entire_installed27_core':True,'changed_pending_whole_rows':3,'proved_component_context_rows_updated':22,'source_sha_rebindings':rebound,'new_proof_sources':0,'new_status_promotions':0,'whole_exercise18_or_whole737_739_approved':False,'closed_refs_sha256':closed,'scope':'Exact metadata identity mechanics only. The original semantic decision bodies/hypotheses/declarations/gaps/times remain unchanged. Original three full literal pending rows adopt already independently approved actual source56/source60 corrections; no new whole MPC or broader evolution/validation approval. No compiler or live/canonical owner/source mutation.'}
with OUT.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'status':out['status'],'candidate':offer['candidate'],'closed_refs':len(closed)}))
