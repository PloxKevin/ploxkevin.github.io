from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(p):
 p=Path(p);return p if p.is_absolute() else R/p
def read(p):return json.loads(P(p).read_text())
def ref(p):
 p=P(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':H(p)}
def checkref(p):assert H(P(p['file']))==p['sha256'],p['file'];return read(p['file'])
B='book/coverage/checks/future23-core/'
offerp=B+'core-audit23-candidate-source51-additions-v1.json';assert H(P(offerp))=='1621763e99296daf587f7d7a60d2fb8aa0431b46d79e4a1abbb13cd50bb0260d';offer=read(offerp)
cp=offer['mapped_ledger'];assert H(P(cp))==offer['mapped_ledger_sha256']=='1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a';c=read(cp)
basep='reports/full-coverage/checkpoint-22/book/coverage/core.json';assert H(P(basep))=='3e7c69fb9a0978c914df20835bed3b2aee2b742702bb07caa6d9d582a16251f7';base=read(basep)
pkt=checkref(offer['candidate_packet']);integ=checkref(offer['candidate_integrity']);ident=checkref(c['source51_core_identity_binding']);inv=read(offer['current_inventory']);assert H(P(offer['current_inventory']))==H(P('book/coverage/inventory.json'))==offer['current_inventory_sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
oldinv=read('book/coverage/inventory-after-correction48.json');ix={k:{r['key']:r for r in inv[k]} for k in ['exercises','material_source_units']};oldix={k:{r['key']:r for r in oldinv[k]} for k in ix}
reviews=[]
for key in ['monitoring_review','lyapunov_identity_component_review','lyapunov_whole_review']:
 r=checkref(pkt[key]);assert 'passed' in r['status'] and not r.get('errors',[]);reviews.append((r,pkt[key]))
assert reviews[0][1]['sha256']=='472f235026c8755b8add8f5c30f10b1dddaf2d47f0fd2687b38814d7d4d8a572'
whole={};adds=[];ergroups={}
for i,(r,rref) in enumerate(reviews):
 for u in r['material_units']:
  key=u['source_unit_key'];assert u['entire_inventory_record']==ix['material_source_units'][key]
  if u.get('whole_unit_approved'):assert u['material_status']=='proved' and not u['missing_clauses'];whole[key]=(u,r,rref)
  if i<2:
   for j,q in enumerate(u.get('components',[])):adds.append((f'{key}::proof23-review{i}-component{j}',key,q,u,r,rref))
 ers=r.get('records',[]) if i==0 else [r['exercise']] if i==1 else []
 for e in ers:
  assert e['whole_exercise_approved'] is False and e['entire_inventory_record']==ix['exercises'][e['exercise_key']]
  ergroups[e['exercise_key']]=(e,r,rref)
assert set(whole)=={'cmdp.html::node-1138','lyapunov-mpc.html::node-1399','lyapunov-mpc.html::node-1401','lyapunov-mpc.html::node-1403'}
assert set(ergroups)=={'cmdp.html::exercise-21','lyapunov-mpc.html::exercise-19'}
assert len(adds)==27
be={e['inventory_key']:e for e in base['exercises']};ce={e['inventory_key']:e for e in c['exercises']};assert be.keys()==ce.keys() and len(be)==92
for key,old in be.items():
 e=ce[key];v=ix['exercises'][key]
 if key not in ergroups:
  z=copy.deepcopy(e);del z['source51_literal_identity'];z['source_sha256']=old['source_sha256'];assert z==old,key;continue
 assert e['original_source48_entire_exercise_row']==old and e['source_text']==v['source_text'] and e['text_sha256']==v['text_sha256'] and e['source_sha256']==v['source_sha256'] and e['status']=='partial'
 rr,r,rref=ergroups[key];gaps=rr.get('remaining_gaps',rr.get('missing_clauses'));assert gaps
 originalclaims=e['claims'][:len(old['claims'])]
 for oc,nc in zip(old['claims'],originalclaims):
  if oc['status']!='pending':assert nc==oc
  else:
   assert nc['original_source48_entire_pending_claim']==oc and nc['statement_in_prose']==v['source_text'] and nc['remaining_gaps']==gaps
   z=copy.deepcopy(nc);del z['original_source48_entire_pending_claim']
   for field in ['statement_in_prose','remaining_gaps','correspondence']:z[field]=oc[field]
   assert z==oc
 groups=rr.get('reviewed_components',rr.get('approved_component_groups',[]));assert len(e['claims'])==len(old['claims'])+len(groups)
 for j,(q,a) in enumerate(zip(groups,e['claims'][len(old['claims']):])):
  assert a['id']==f'{key}::proof23-component{j}' and a['original_review_component']==q and a['lean_declarations']==q['lean_declarations'] and a['hypotheses']==q.get('hypotheses',[]) and not a['remaining_gaps'] and a['status']=='proved'
  assert a['independent_review']['source']==rref['file'] and a['independent_review']['sha256']==rref['sha256']
  assert a['independent_review']['original_review_time']==q.get('original_reviewed_at_utc',r.get('reviewed_at_utc',r.get('checked_at_utc')))
  assert a['correspondence']==q.get('per_component_reason',q.get('reason'))
bm=base['material_claims'];cm=c['material_claims'];assert len(cm)==len(bm)+27
mc={r['original_claim_id']:r for r in reviews[0][0]['historical41_material_row_compatibility']};ec={r['original_claim_id']:r for r in reviews[0][0]['historical46_exercise_claim_compatibility']};assert len(mc)==41 and len(ec)==46
for old,n in zip(bm,cm[:len(bm)]):
 key=old['source_unit_keys'][0];v=ix['material_source_units'][key]
 assert n['source_unit_keys']==old['source_unit_keys'] and n['source_text']==v['source_text'] and n['text_sha256']==v['text_sha256'] and n['source_sha256']==v['source_sha256']
 z=copy.deepcopy(n);del z['source51_literal_identity']
 if 'original_source48_entire_material_row' in z:assert z.pop('original_source48_entire_material_row')==old
 if 'fresh_source51_historical_semantic_compatibility' in z:
  assert old['id'] in mc and mc[old['id']]['entire_original_claim']==old;del z['fresh_source51_historical_semantic_compatibility']
 if key in whole and old['status']=='pending':
  u,r,rref=whole[key]
  assert z['status']=='proved' and z['lean_declarations']==u['lean_declarations'] and z['hypotheses']==u.get('hypotheses',[]) and z['correspondence']==u['per_unit_reason'] and not z['remaining_gaps']
  assert z['original_complete_literal_review_record']==u;del z['original_complete_literal_review_record'];assert z['independent_review']=={'source':rref['file'],'sha256':rref['sha256'],'original_review_time':r.get('reviewed_at_utc')};del z['independent_review']
  for field in ['kind','status','lean_declarations','hypotheses','correspondence','remaining_gaps']:z[field]=old[field]
 for field in ['source_sha256','source_text','text_sha256','statement_in_prose']:z[field]=old[field]
 assert z==old,old['id']
for a,(cid,key,q,u,r,rref) in zip(cm[len(bm):],adds):
 v=ix['material_source_units'][key];assert a['id']==cid and a['original_review_component']==q and a['lean_declarations']==q['lean_declarations'] and a['hypotheses']==q.get('hypotheses',[]) and not a['remaining_gaps'] and a['status']=='proved'
 assert a['source_unit_keys']==[key] and a['source_text']==v['source_text'] and a['text_sha256']==v['text_sha256'] and a['source_sha256']==v['source_sha256'] and a['parent_remaining_gaps']==u.get('missing_clauses',[])
 assert a['correspondence']==q.get('per_component_reason',q.get('reason')) and a['independent_review']=={'source':rref['file'],'sha256':rref['sha256'],'original_review_time':q.get('original_reviewed_at_utc',r.get('reviewed_at_utc',r.get('checked_at_utc')))}
for key in whole:
 a=[n for o,n in zip(bm,cm) if o['source_unit_keys']==[key] and o['status']=='pending'];assert len(a)==1 and a[0]['statement_in_prose']==ix['material_source_units'][key]['source_text']
assert c['counts']==offer['counts'] and c['counts']['exercise_statuses']=={'complete_math':88,'partial':4}
ready=checkref(pkt['actual_proof_readiness']);assert len(ready['proof_files'])==offer['proof_file_count']==9 and ready['public_theorem_count']==offer['local_theorem_count']==88 and offer['proof_files']==ready['proof_files']
assert set(c['proof_files'])-set(base['proof_files'])==set(ready['proof_files'])
for k,v in base['proof_files'].items():assert c['proof_files'][k]==v
names=set();selected=read('reports/full-coverage/checkpoint-22-selection.json');assert len(selected['proof_files'])==1113
for n,p in selected['proof_files'].items():assert H(P(n))==p['sha256'];names.update(d['name'] for d in declarations(P(n).read_text()))
for n,p in ready['proof_files'].items():
 assert H(P(n))==p['sha256']==c['proof_files'][n]
 actualpub=[d for d in declarations(P(n).read_text()) if d.get('kind') in ['theorem','lemma']];assert len(actualpub)==offer['public_theorems_by_source'][n]
 names.update(d['name'] for d in declarations(P(n).read_text()))
 for ep,h in p['evidence_sha256'].items():assert H(P(ep))==h,ep
for a in cm[len(bm):]:assert set(a['lean_declarations'])<=names
for u,r,rref in whole.values():assert set(u['lean_declarations'])<=names
for ep,h in offer['required_evidence_artifacts_sha256'].items():assert H(P(ep))==h,ep
for ep,h in offer['review_sha256'].items():assert H(P(ep))==h
for ep,h in offer['source_sha256'].items():assert H(P(ep))==h
for ep,h in offer['baseline22_owner_assets'].items():assert H(P(ep))==h
actual=read(offer['actual_builder']);assert H(P(offer['actual_builder']))==offer['actual_builder_sha256'] and actual['actual_exit_code']==0 and H(P(actual['log']))==actual['log_sha256']
for ep,h in actual['helper_sha256_before'].items():assert H(P(ep))==h==actual['helper_sha256_after'][ep]
assert H(P('book/coverage/core_source51_candidate23_v2.py'))==offer['builder_sha256']
oldobs=checkref(offer['original_failure_history'][0]);assert oldobs['status']=='candidate_v1_not_ready_literal_statement_consistency_failed'
for key in ergroups:assert not reviews[0][0]['records'][0]['whole_exercise_approved']
report={'status':'passed_independent_isolated_core23_source51_final_candidate_mechanics','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[],'helper':ref('book/coverage/core_source51_candidate23_v2.py'),'offer':ref(offerp),'candidate':ref(cp),'packet':offer['candidate_packet'],'candidate_integrity':offer['candidate_integrity'],'baseline22_core':ref(basep),'actual_builder':ref(offer['actual_builder']),'actual_builder_raw_log':ref(actual['log']),'four_whole_material_units':sorted(whole),'new_component_material_rows':27,'new_proof_sources':9,'new_public_theorems':88,'all_original166_proof_rows_exact':len(base['proof_files'])==166,'all_92_exercise_original_rows_and_oldclaims_archived_or_restored_exact':True,'historical41_material_and46_exercise_claim_bodies_hypotheses_review_times_exact':True,'all_existing_material_bodies_restored_except_explicit_current_literal_metadata_and_four_approved_whole_decisions':True,'fresh_review_hypotheses_reasons_declarations_parent_gaps_times_mapped_exact':True,'complete_math_exercise_count':88,'partial_exercise_count':4,'monitoring_and_lyapunov_whole_exercises_remain_partial':True,'five_stale_full_literal_statement_v1_fields_corrected_in_v2':True,'original_v1_not_ready_observation':offer['original_failure_history'][0],'all_required_evidence_artifacts_checked':len(offer['required_evidence_artifacts_sha256']),'protected_selected22_source_count':1113,'working22_owner_assets_unchanged':offer['baseline22_owner_assets'],'actual_checker':ref(__file__),'scope':'Independent mapping/mechanics only; existing full semantic reviews retain their original bodies and times. No live owner installation, fresh mathematical compilation, global validator or aggregate23 audit is claimed.'}
out=Path('/tmp/core23-source51-final-candidate-independent-applied-confirmation-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':ref(out),'status':'passed','counts':c['counts']}))
