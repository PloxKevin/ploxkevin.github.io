from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future23/source51';O=R/'book/coverage/checks/modules-future23/source50'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(p):
 p=Path(p);return p if p.is_absolute() else R/p
def read(p):return json.loads(P(p).read_text())
def ref(p):
 p=P(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':H(p)}
oldp=O/'modules23-candidate-source50-identity-v1.json';newp=B/'modules23-candidate-source51-identity-v1.json';offerp=O/'modules-audit23-candidate-source50-additions-v2-reviewed.json';prior=O/'modules23-source50-identity-independent-applied-confirmation-v2.json'
assert H(oldp)=='8cb3ecf6c7f4f82da069c3c0d862297e7bbcbc6468d8550e11b2335ecc1cf8d1';assert H(newp)=='65e7566b3f3c315ae4cc2297606fe74f8a7136e28d0d4a47ca9cd46fe1b41fbd';assert H(offerp)=='444f4a5eaf2e159e7b21eaa08abad326aba562420a5b1ab50d8dd328d47f0e54';assert H(prior)=='01def97eceb62e65e172da12ba8b7d8ab759ddbd8568b514b26ef379ed13c26a'
old,new,offer=read(oldp),read(newp),read(offerp);z=copy.deepcopy(new)
for e in z['exercises']:del e['source51_unchanged_literal_identity']
for e in z['material_claims']:del e['source51_unchanged_literal_identity']
for k in ['current_inventory','current_inventory_sha256','current_identity_binding_validation']:z[k]=copy.deepcopy(old[k])
del z['inventory_identity_rebase51'];assert z==old
sidep=B/'unchanged-owned-literal-identity-v1.json';guardp=B/'candidate-identity-binding-integrity-v1.json';side,guard=read(sidep),read(guardp)
invold=read('book/coverage/inventory-after-correction50.json');invnew=read('book/coverage/inventory-after-correction51.json');assert H(P('book/coverage/inventory-after-correction51.json'))==H(P('book/coverage/inventory.json'))=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
scope=set(old['scope_pages']);assert len(scope)==11
atom=lambda r:hashlib.sha256(json.dumps(r,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
for kind,count in [('exercises',217),('material_source_units',4977)]:
 a={r['key']:r for r in invold[kind]};b={r['key']:r for r in invnew[kind]};assert a.keys()==b.keys()
 owned={k:r for k,r in a.items() if r['source'] in scope};assert owned=={k:r for k,r in b.items() if r['source'] in scope} and len(owned)==count
 rows={r['key']:r for r in side['unchanged_owned_literals'][kind]};assert set(rows)==set(owned)
 for k,r in owned.items():
  s=rows[k];assert s['entire_inventory_record_sha256']==atom(r)
  for field in ['source','line','locator','text_sha256','source_sha256']:assert s[field]==r[field]
 changed=[k for k in a if a[k]!=b[k]];literal=[k for k in a if {n:v for n,v in a[k].items() if n!='source_sha256'}!={n:v for n,v in b[k].items() if n!='source_sha256'}]
 assert changed==side['changed_other_owner_entire_record_keys'][kind] and literal==side['changed_other_owner_literal_text_or_structure_keys'][kind]
 assert all(a[k]['source']=='SafeLearning/cmdp.html' for k in changed)
 assert literal==(['cmdp.html::exercise-21'] if kind=='exercises' else ['cmdp.html::node-1138'])
for k,v in old['source_sha256'].items():assert H(P(k))==v==invold['source_sha256'][k]==invnew['source_sha256'][k]
for k,v in old['chapter_fragment_sha256'].items():assert H(P(k))==v
for k,v in offer['required_evidence_artifacts_sha256'].items():assert H(P(k))==v,k
actualp=B/'modules23-candidate-source51-identity-actual-execution-v3.json';actual=read(actualp);assert H(actualp)=='e6927560c14849733680c98def8d390e89882cca95970a615d8c368e4404b404' and actual['actual_exit_code']==0
assert H(P(actual['log']))==actual['log_sha256'];helper=P(actual['actual_command'][1]);assert H(helper)==actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']==new['current_identity_binding_validation']['validator_sha256']
assert new['current_identity_binding_validation']['validator']==str(helper.relative_to(R)) and new['current_identity_binding_validation']['sha256']==H(guardp)
root=read('reports/full-coverage/source51-apply-execution-v1.json');post=read('book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json');assert root['actual_exit_code']==post['actual_exit_code']==0 and H(P(root['log']))==root['log_sha256']
for k,v in guard['protected_live22_ledgers_sha256'].items():assert H(P(k))==v
m=read('reports/full-coverage/checkpoint-22-manifest.json');assert len(m['proof_files'])==1113
for k,v in m['proof_files'].items():assert H(P(k))==v['sha256']
for k,v in new['proof_files'].items():assert H(P(k))==v['sha256']
history=[]
for i in [1,2]:
 p=B/f'modules23-candidate-source51-identity-actual-execution-v{i}.json';d=read(p);assert d['actual_exit_code']==1 and H(P(d['log']))==d['log_sha256'];history.append({'actual_record':ref(p),'actual_raw_log':ref(d['log']),'entire_actual_failure_record':d})
report={'status':'passed_independent_source51_identity_only_module23_candidate_mechanics','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[],'original_reviewed_source50_offer':ref(offerp),'original_source50_candidate':ref(oldp),'new_source51_candidate':ref(newp),'original_source50_full_identity_peer':ref(prior),'entire_original_source50_candidate_recovered_by_exact_reverse_normalization':True,'identity_sidecar':ref(sidep),'candidate_integrity':ref(guardp),'actual_isolated_identity_execution':ref(actualp),'actual_isolated_identity_raw_log':ref(actual['log']),'actual_isolated_helper':ref(helper),'all217_owned_exercise_and4977_owned_material_records_exact':True,'all_candidate_claims_statuses_hypotheses_semantic_bodies_proof_rows_and_original_review_times_unchanged':True,'unchanged_candidate_exercises':len(new['exercises']),'unchanged_candidate_material_claims':len(new['material_claims']),'unchanged_proof_rows':len(new['proof_files']),'all104_active_source50_required_evidence_hashes_verified':len(offer['required_evidence_artifacts_sha256']),'changed_other_owner_literal_keys':side['changed_other_owner_literal_text_or_structure_keys'],'all1113_selected22_sources_and_live_owner_assets_exact':True,'original_source51_v1_v2_failed_execution_history':history,'actual_checker':ref(__file__),'scope':'Mechanical identity binding only. No fresh semantic review, mathematical compilation, live installation, global validator or aggregate23 claim.'}
out=Path('/tmp/modules23-source51-identity-independent-applied-confirmation-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':ref(out),'status':'passed','proof_rows':len(new['proof_files'])}))
