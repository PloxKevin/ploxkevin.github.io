"""Prepare a TMP-only Applied current60 candidate without a new proof decision."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/applied28-source60-identity-v1')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def P(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):return {'file':str(p),'sha256':H(p)}
def put(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def zero(d):
 a=[d[k]for k in ('actual_exit_code','exit_code')if k in d];assert a and all(type(v)is int and v==0 for v in a)
C=R/'book/coverage/applied.json';Q=R/'book/coverage/applied-promotions.json'
assert H(C)=='31b6af21c8ba9d214380ba5c116046bf7587eba3d736e1a536266c5fbfe61e68'
assert H(Q)=='72ee23132c02823bc13fa513d2892e79d748b6617b0d3fe52b3de7e29735a5a2'
c,q=J(C),J(Q)
OLD=R/'book/coverage/inventory-after-correction55.json';NEW=R/'book/coverage/inventory-after-correction60.json'
assert H(OLD)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert H(NEW)==H(R/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
old,new=J(OLD),J(NEW);page='SafeLearning/primer-probability.html';unitkey='primer-probability.html::node-386'
oldsha=old['source_sha256'][page];newsha=new['source_sha256'][page]
assert oldsha=='02779ca8a2499c347f73c0365000522e36ee93961bc68cf9d9fcff26a55e0a99' and newsha=='eeb3a23fe5a574b25e1e2e82adc149c51a8dcfadebf57ee4fa7b8d5f7ca13ea0'
scope=set(c['scope_pages']);assert len(scope)==3 and c['source_sha256']=={n:old['source_sha256'][n]for n in scope}
assert {n for n in scope if old['source_sha256'][n]!=new['source_sha256'][n]}=={page}
units={}
for section,count in [('exercises',128),('material_source_units',2059)]:
 a={r['key']:r for r in old[section]if r['source']in scope};b={r['key']:r for r in new[section]if r['source']in scope};assert set(a)==set(b) and len(a)==count
 changed=[]
 for k in a:
  z=copy.deepcopy(b[k]);z['source_sha256']=a[k]['source_sha256']
  if z!=a[k]:changed.append(k)
 assert changed==([] if section=='exercises' else [unitkey]),(section,changed)
 units[section]=(a,b)
a,b=units['material_source_units'];oldu,newu=a[unitkey],b[unitkey]
oldlast='change any of them and every probability changes.'
newlast='changes to those inputs can change the trajectory law and probabilities computed from it.'
assert newu['source_text']==oldu['source_text'].replace(oldlast,newlast) and hashlib.sha256(newu['source_text'].encode()).hexdigest()==newu['text_sha256']
assert len(c['exercises'])==128 and sum(len(e['claims'])for e in c['exercises'])==468 and len(c['material_claims'])==1954 and len(c['proof_files'])==312
claim=next(r for r in c['material_claims']if r['id']=='material.'+unitkey)
assert claim['status']=='pending' and claim['lean_declarations']==[] and claim['text_sha256']==oldu['text_sha256'] and claim['statement_in_prose']==oldu['source_text']
assert unitkey not in q['material']
O=R/'book/coverage/checks/applied-future27/current55-identity-v1/applied27-current55-identity-offer-canonical-v1.json';assert H(O)=='0be877c77792c53e548054a3abb7222c02b2df89d42e425fc4cbfc1f2be7648a';o=J(O)
assert o['candidate']['sha256']==H(C) and J(P(o['candidate']['file']))==c and o['candidate_promotions']['sha256']==H(Q) and J(P(o['candidate_promotions']['file']))==q
inherited=dict(o['required_evidence_artifacts_sha256']);assert len(inherited)==192
for n,h in inherited.items():assert H(P(n))==h,n
APP=R/'reports/full-coverage/source56-60-corrections-application-v1.json';assert H(APP)=='a5eb7ae4f866ef3af5c95bb71e7246a381f7c49dca53b28aa8b9e00e21dd667f';app=J(APP)
assert app['status']=='passed_actual_source56_to60_corrections_full29_inventory_owner_identity_rebase_pending' and [r['correction_id']for r in app['applications']]==[56,57,58,59,60]
assert app['selected27_proof_sources_unchanged']==1175 and app['five_installed27_owner_ledgers_unchanged']is True and app['coverage_complete']is False
receipt57=next(r for r in app['applications']if r['correction_id']==57);assert receipt57['source_after']=={'file':page,'sha256':newsha} and receipt57['changed_exercises']==[] and receipt57['changed_material_units']==[unitkey]
ACT=R/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json';assert H(ACT)=='7b33553ee1f7c2ce5ebbe3c7393aefe59a4cf894fc370a09f0271e2f5897e3fe';act=J(ACT);zero(act)
assert act['actual_command']==['python3','book/coverage/checks/root_apply_source56_60_v2.py','--closure-sha256','43bdd1aaa2f93b358a0697ffeb4ae29ffa5c2d18784834cf9cc370929924d71d','--apply']
assert act['helper_sha256_before']==act['helper_sha256_after'] and H(P(act['log']))==act['log_sha256']
SEL=R/'reports/full-coverage/checkpoint-27-selection.json';assert H(SEL)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd';sel=J(SEL);assert sel['proof_file_count']==len(sel['proof_files'])==1175
INT=R/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json';assert H(INT)=='5b6c87b7cc5e385f1e45d78dbd2340cdfa93f44d54989ef05fcd5a1ff77aa75b';integ=J(INT);assert integ['applied']is True
owners={r['destination']:r['candidate']['sha256']for r in integ['exact_replacements']};assert len(owners)==5 and owners['book/coverage/applied.json']==H(C) and owners['book/coverage/applied-promotions.json']==H(Q)
BIND=R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json';assert H(BIND)=='e5d0884b4b60fca8bf0f63e4fe2cc09bd63ceea19a417bcc3e8adf0ab3389560';assets=dict(J(BIND)['exact_current55_safelearning_assets_sha256']);assets.update(new['source_sha256']);assert len(assets)==31
pinned={str(p.relative_to(R)):H(p)for p in (OLD,NEW,O,APP,ACT,SEL,INT,BIND,R/'book/coverage/inventory.json',R/'book/coverage/material-corrections.json')}
pinned.update(act['helper_sha256_after']);pinned[act['log']]=act['log_sha256']
protected={n:r['sha256']for n,r in sel['proof_files'].items()};protected.update(assets);protected.update(owners);protected.update(pinned)
def guard():
 for n,h in protected.items():assert H(P(n))==h,n
 for n,h in inherited.items():assert H(P(n))==h,n
 assert H(Path(__file__))==helper_before
helper_before=H(Path(__file__));guard();B.mkdir(exist_ok=False);ORIG=B/'original-installed27';ORIG.mkdir()
for name,src in [('applied.json',C),('applied-promotions.json',Q)]:
 with (ORIG/name).open('xb')as f:f.write(src.read_bytes())
 assert H(ORIG/name)==H(src)
out=copy.deepcopy(c);outq=copy.deepcopy(q);out['source_sha256'][page]=newsha
rebound={'exercises':0,'material_claims':0}
for section in rebound:
 for row in out[section]:
  if row.get('source')==page:
   assert row['source_sha256']==oldsha;row['source_sha256']=newsha;rebound[section]+=1
assert rebound=={'exercises':44,'material_claims':596}
newclaim=next(r for r in out['material_claims']if r['id']==claim['id'])
newclaim['text_sha256']=newu['text_sha256'];newclaim['statement_in_prose']=newu['source_text']
for field in ('source_clauses','remaining_gaps'):
 newclaim[field]=[s.replace(oldlast,newlast)for s in claim[field]]
assert newclaim['source_clauses'][-1]==newlast and newclaim['status']=='pending' and newclaim['lean_declarations']==[]
SIDE=B/'applied-owned-source55-to60-identity-and-pending386-binding-v1.json'
side={'status':'passed_actual_isolated_applied_owned_source55_to60_identity_and_corrected_pending_literal','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_installed27_exact_bytes':{'ledger':ref(ORIG/'applied.json'),'promotions':ref(ORIG/'applied-promotions.json')},'original_reviewed55_offer':ref(O),'historical_inventory':ref(OLD),'current_inventory':ref(NEW),'source_sha256_before':c['source_sha256'],'source_sha256_after':{n:new['source_sha256'][n]for n in scope},'unchanged_owned_literal_counts':{'exercises':128,'physical_units':2058,'exercise_claims':468,'other_material_claims':1953,'unpruned_proof_metadata_rows':312},'direct_probability_page_hash_bindings_rebased':rebound,'only_changed_physical_unit':unitkey,'entire_original_pending386_claim_body':claim,'entire_current_pending386_claim_body':newclaim,'original_physical386_record':oldu,'current_physical386_record':newu,'exact_actual_source57_receipt':receipt57,'source56_to60_native_application':ref(APP),'source56_to60_actual_execution':ref(ACT),'installed27_owner_sha256':owners,'protected_current60_asset_sha256':assets,'inverse_recipe':'Remove current60_owner_identity from both candidates; reset ledger top probability source hash and every direct probability exercise/material source_sha256 to original source55 hash; replace entire pending386 claim with the original body saved here. All remaining keys/arrays/bodies retain their original order/content. Promotion ledger has only the new identity overlay.','new_proof_sources':0,'new_exercise_or_material_decisions':0,'coverage_complete':False,'scope':'Only current source identity and a correction of an already-pending literal. No mathematical proof/status/hypothesis/review time is promoted or redecided.'}
put(SIDE,side)
overlay={'inventory':str(NEW.relative_to(R)),'inventory_sha256':H(NEW),'identity_sidecar':ref(SIDE),'original_installed27_ledger':ref(ORIG/'applied.json'),'original_installed27_promotions':ref(ORIG/'applied-promotions.json'),'original_reviewed_source55_offer':ref(O),'changed_pending_unit':unitkey,'new_proof_sources':0,'new_material_or_exercise_decisions':0,'scope':'Source60 identity bindings; only pending386 adopts actual correction57, retaining its pending status and complete original claim history. Every earlier proof, promotion, hypothesis, semantic review body/time and every other literal is preserved.'}
assert 'current60_owner_identity'not in out and 'current60_owner_identity'not in outq
out['current60_owner_identity']=copy.deepcopy(overlay);outq['current60_owner_identity']=copy.deepcopy(overlay)
rev=copy.deepcopy(out);revq=copy.deepcopy(outq);rev.pop('current60_owner_identity');revq.pop('current60_owner_identity');rev['source_sha256'][page]=oldsha
for section in rebound:
 for row in rev[section]:
  if row.get('source')==page:row['source_sha256']=oldsha
rev['material_claims'][next(i for i,r in enumerate(rev['material_claims'])if r['id']==claim['id'])]=copy.deepcopy(claim)
assert rev==c and revq==q
CAND=B/'applied28-source60-identity-candidate-v1.json';PROM=B/'applied-promotions28-source60-identity-candidate-v1.json';put(CAND,out);put(PROM,outq)
NATIVE=B/'applied28-source60-identity-candidate-integrity-v1.json'
put(NATIVE,{'status':'passed_actual_isolated_applied28_source60_identity_candidate_mechanics','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(CAND),'candidate_promotions':ref(PROM),'identity_sidecar':ref(SIDE),'exact_inverse_recovers_installed27_entire_ledger_and_promotions':True,'new_proof_sources':0,'new_mathematical_promotions':0,'coverage_complete':False,'live_owner_written':False,'guards':{'selected27_proofs':1175,'current60_assets':31,'installed27_owner_ledgers':5}})
refs=dict(inherited)
for p in (O,OLD,NEW,APP,ACT,P(act['log']),SEL,INT,BIND,SIDE,NATIVE,ORIG/'applied.json',ORIG/'applied-promotions.json',Path(__file__)):
 n=str(p.relative_to(R))if p.is_relative_to(R)else str(p);h=H(p);assert n not in refs or refs[n]==h;refs[n]=h
OFFER=B/'applied28-source60-identity-additions-draft-v1.json'
put(OFFER,{'schema_version':1,'status':'isolated_applied28_current60_identity_candidate_awaiting_independent_mechanics','errors':[],'inventory':str(NEW.relative_to(R)),'inventory_sha256':H(NEW),'base_selection':str(SEL.relative_to(R)),'base_selection_sha256':H(SEL),'mapped_ledger':str(CAND),'mapped_ledger_sha256':H(CAND),'mapped_promotions':str(PROM),'mapped_promotions_sha256':H(PROM),'candidate':ref(CAND),'candidate_promotions':ref(PROM),'candidate_builder':ref(Path(__file__)),'identity_sidecar':ref(SIDE),'identity_integrity':ref(NATIVE),'original_reviewed_source55_offer':ref(O),'source_sha256':copy.deepcopy(out['source_sha256']),'proof_files':{},'new_actual_paired_records':[],'new_material_keys':[],'counts':copy.deepcopy(c['counts']),'baseline27_owner_sha256':owners,'required_evidence_artifacts_sha256':refs,'final_independent_candidate_mapping_peer':None,'actual_isolated_candidate_preparation':None,'coverage_complete':False,'scope':'Bounded TMP-only identity/correction offer. All128 exercise literal texts/468 claims, 1953 other material bodies,312 proof metadata and every original semantic review/time stay exact. Direct probability page source hashes rebind and only already-pending386 adopts actual corrected text. Promotion decisions remain exact. No installed owner/proof/source/PUB/Git mutation.'})
guard();print(json.dumps({'offer':ref(OFFER),'candidate':ref(CAND),'promotions':ref(PROM),'sidecar':ref(SIDE),'native_integrity':ref(NATIVE),'inherited_evidence_count':len(inherited),'closed_evidence_count':len(refs),'new_proofs':0,'new_mathematical_decisions':0}))
