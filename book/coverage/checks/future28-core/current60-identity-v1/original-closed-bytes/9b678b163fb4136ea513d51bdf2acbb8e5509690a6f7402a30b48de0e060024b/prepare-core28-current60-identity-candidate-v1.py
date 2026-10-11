"""TMP-only zero-proof Core identity rebase after actual source56--60."""
from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/core28-current60-identity-v1')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_bytes());ref=lambda p:{'file':str(p),'sha256':H(p)}
def put(p,d):
 with p.open('x')as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
C=R/'book/coverage/core.json';assert H(C)=='0bf99e01c47c7b9fa18488fdc3104c189e3977597c15f1c7e20253afad1245c0';c=J(C)
OLD=R/'book/coverage/inventory-after-correction55.json';NEW=R/'book/coverage/inventory-after-correction60.json';assert H(OLD)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf';assert H(NEW)==H(R/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
old,new=J(OLD),J(NEW);scope=set(c['scope_pages']);page='SafeLearning/lyapunov-mpc.html';assert {n for n in scope if old['source_sha256'][n]!=new['source_sha256'][n]}=={page}
changedkeys={'lyapunov-mpc.html::node-'+str(i)for i in [735,737,739]};maps={}
for section,count in [('exercises',92),('material_source_units',3982)]:
 a={r['key']:r for r in old[section]if r['source']in scope};b={r['key']:r for r in new[section]if r['source']in scope};assert set(a)==set(b)and len(a)==count
 changed={k for k in a if {f:v for f,v in a[k].items()if f!='source_sha256'}!={f:v for f,v in b[k].items()if f!='source_sha256'}};assert changed==(set()if section=='exercises'else changedkeys);maps[section]=(a,b)
assert len(c['exercises'])==92 and len(c['material_claims'])==4210 and len(c['proof_files'])==182
APP=R/'reports/full-coverage/source56-60-corrections-application-v1.json';assert H(APP)=='a5eb7ae4f866ef3af5c95bb71e7246a381f7c49dca53b28aa8b9e00e21dd667f';app=J(APP);assert app['status']=='passed_actual_source56_to60_corrections_full29_inventory_owner_identity_rebase_pending' and app['five_installed27_owner_ledgers_unchanged']is True and app['selected27_proof_sources_unchanged']==1175
ACT=R/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json';assert H(ACT)=='7b33553ee1f7c2ce5ebbe3c7393aefe59a4cf894fc370a09f0271e2f5897e3fe';act=J(ACT);assert type(act['actual_exit_code'])is int and act['actual_exit_code']==0 and H(R/act['log'])==act['log_sha256']
PEERS=[Path('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-review-v2.json'),Path('/tmp/mpc-source60-row-definitions-independent-foundations28-v2.json')]
assert H(PEERS[0])=='37ff22c2f37201bdef612feb6ce3b1fc47748b1db94305c9df36ba1888ff2dcc' and H(PEERS[1])=='e37a5d04c72dd58ea826472a739f7a4ef2a6f7c40479dfe315a4da3f0b19a4e5'
for p in PEERS:assert J(p).get('errors')==[]
SEL=R/'reports/full-coverage/checkpoint-27-selection.json';assert H(SEL)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd';sel=J(SEL);assert len(sel['proof_files'])==1175
INT=R/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json';integ=J(INT);assert integ['applied']is True;owners={r['destination']:r['candidate']['sha256']for r in integ['exact_replacements']};assert len(owners)==5 and owners['book/coverage/core.json']==H(C)
BIND=R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json';assets=dict(J(BIND)['exact_current55_safelearning_assets_sha256']);assets.update(new['source_sha256']);assert len(assets)==31
protected={n:r['sha256']for n,r in sel['proof_files'].items()};protected.update(assets);protected.update(owners)
for p in [OLD,NEW,APP,ACT,R/act['log'],SEL,INT,BIND,R/'book/coverage/material-corrections.json',R/'book/coverage/inventory.json']:
 protected[str(p.relative_to(R))]=H(p)
helper_before=H(Path(__file__))
def guard():
 for n,h in protected.items():assert H(R/n)==h,n
 assert H(Path(__file__))==helper_before
 for p in PEERS:assert H(p)==peer_hashes[str(p)]
peer_hashes={str(p):H(p)for p in PEERS};guard();B.mkdir(exist_ok=False);original=B/'original-installed27-core.json'
with original.open('xb')as f:f.write(C.read_bytes())
assert H(original)==H(C)
out=copy.deepcopy(c);out['source_sha256'][page]=new['source_sha256'][page];out['current_inventory']='book/coverage/inventory-after-correction60.json';out['current_inventory_sha256']=H(NEW)
rebound={'exercises':0,'material_claims':0};changed_rows=[]
oldunits,newunits=maps['material_source_units']
for section in rebound:
 for r in out[section]:
  if r.get('source')==page:
   assert r['source_sha256']==old['source_sha256'][page];r['source_sha256']=new['source_sha256'][page];rebound[section]+=1
for row in out['material_claims']:
 keys=set(row.get('source_unit_keys',[]))&changedkeys
 if not keys:continue
 assert len(keys)==1 and len(row['source_unit_keys'])==1;k=next(iter(keys));originalrow=next(r for r in c['material_claims']if r['id']==row['id'])
 assert row['text_sha256']==oldunits[k]['text_sha256'] and row['source_text']==oldunits[k]['source_text']
 row['text_sha256']=newunits[k]['text_sha256'];row['source_text']=newunits[k]['source_text']
 if row['id']==k+'::semantic-review':
  assert row['status']=='pending'and row['lean_declarations']==[] and row['statement_in_prose']==oldunits[k]['source_text'];row['statement_in_prose']=newunits[k]['source_text']
 else:
  assert row['status']=='proved';assert row['statement_in_prose']==originalrow['statement_in_prose']and row['hypotheses']==originalrow['hypotheses']and row['lean_declarations']==originalrow['lean_declarations']
 changed_rows.append({'claim_id':row['id'],'unit_key':k,'status_unchanged':row['status'],'original_exact_claim_body':originalrow})
assert rebound=={'exercises':20,'material_claims':577}and len(changed_rows)==25
SIDE=B/'core28-current60-exact-identity-and-three-pending-literal-binding-v1.json'
put(SIDE,{'status':'passed_actual_isolated_core_current55_to60_exact_identity_rebase','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_installed27_exact_bytes':ref(original),'historical_inventory':ref(OLD),'current_inventory':ref(NEW),'actual_source56_to60_application':ref(APP),'actual_source56_to60_execution':ref(ACT),'independent_narrow_source56_60_semantic_peers':[ref(p)for p in PEERS],'entire_three_original_and_current_physical_records':{k:{'original55':oldunits[k],'current60':newunits[k]}for k in sorted(changedkeys)},'entire_original_changed_claim_bodies':changed_rows,'rebound_direct_source_identity_counts':rebound,'all92_exercise_literals_unchanged':True,'all3979_other_physical_literals_unchanged':True,'all182_old_proof_metadata_rows_unchanged':True,'new_proofs_or_counts_or_status_promotions':0,'whole_exercise18_or_whole737_739_approved':False,'scope':'Current60 source identity and literal context bindings only. Three pending whole semantic rows stay pending. Twenty-two already-proved component statements, hypotheses, declarations, semantic review bodies/times and pending whole gaps retain their exact original meaning. Adoption of partial-domain reading does not infer broader RPI or full MPC completion.'})
assert 'source60_core_identity_binding'not in out
out['source60_core_identity_binding']={'inventory':ref(NEW),'identity_sidecar':ref(SIDE),'original_installed27_core':ref(original),'new_proofs':0,'new_status_promotions':0,'whole_exercise18_still_partial':True,'scope':'Exact source60 rebase; all original mathematical claims, hypotheses, declarations, independent review bodies/times and counts preserved. Only source SHA/text identity bindings and three still-pending full literal prose rows adopt actual corrections.'}
reverse=copy.deepcopy(out);reverse.pop('source60_core_identity_binding');reverse['source_sha256']=copy.deepcopy(c['source_sha256']);reverse['current_inventory']=c['current_inventory'];reverse['current_inventory_sha256']=c['current_inventory_sha256']
for section in rebound:
 for r in reverse[section]:
  if r.get('source')==page:r['source_sha256']=old['source_sha256'][page]
oldrows={r['claim_id']:r['original_exact_claim_body']for r in changed_rows}
reverse['material_claims']=[copy.deepcopy(oldrows.get(r['id'],r))for r in reverse['material_claims']];assert reverse==c
CAND=B/'core28-current60-identity-candidate-v1.json';put(CAND,out)
NATIVE=B/'core28-current60-identity-candidate-integrity-v1.json';put(NATIVE,{'status':'passed_actual_isolated_core28_current60_identity_candidate_mechanics','errors':[],'candidate':ref(CAND),'identity_sidecar':ref(SIDE),'exact_inverse_restores_installed27_entire_core':True,'new_proof_sources':0,'new_counts_or_status_promotions':0,'whole_exercise18_approved':False,'live_owner_written':False,'current60_assets31_proofs1175_five27owners_guarded':True})
refs={str(p.relative_to(R))if p.is_relative_to(R)else str(p):H(p)for p in [OLD,NEW,APP,ACT,R/act['log'],SEL,INT,BIND,original,SIDE,NATIVE,Path(__file__),*PEERS]}
OFFER=B/'core28-current60-identity-offer-draft-v1.json';put(OFFER,{'schema_version':1,'status':'isolated_core28_current60_identity_candidate_awaiting_independent_mechanics','errors':[],'candidate':ref(CAND),'mapped_ledger':str(CAND),'mapped_ledger_sha256':H(CAND),'identity_sidecar':ref(SIDE),'identity_integrity':ref(NATIVE),'candidate_builder':ref(Path(__file__)),'actual_isolated_candidate_preparation':None,'final_independent_candidate_mapping_peer':None,'inventory':'book/coverage/inventory-after-correction60.json','inventory_sha256':H(NEW),'base_selection':ref(SEL),'source_sha256':out['source_sha256'],'counts':out['counts'],'proof_files':{},'new_actual_paired_records':[],'new_material_keys':[],'required_evidence_artifacts_sha256':refs,'coverage_complete':False,'scope':'TMP identity rebase of installed Core27 only. No new proof selection, material status/count promotion, owner/source/PUB/Git write. Broader MPC certificate and full Exercise18 remain separate pending work.'})
guard();print(json.dumps({'offer':ref(OFFER),'candidate':ref(CAND),'identity':ref(SIDE),'integrity':ref(NATIVE),'new_proofs':0,'new_promotions':0}))
