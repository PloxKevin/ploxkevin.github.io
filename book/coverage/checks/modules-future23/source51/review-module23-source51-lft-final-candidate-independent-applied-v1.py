from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,sys,collections
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(p):
 p=Path(p);return p if p.is_absolute() else R/p
def read(p):return json.loads(P(p).read_text())
def ref(p):
 p=P(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':H(p)}
B='book/coverage/checks/modules-future23/source51/'
offerp=B+'modules-audit23-candidate-source51-lft-additions-v2.json';assert H(P(offerp))=='f307aae18834b25b845968c714c4f65b0349a4d40866a80efc8bdb2e9c137d5c';offer=read(offerp)
oldp=B+'modules23-candidate-source51-identity-v1.json';assert H(P(oldp))=='65e7566b3f3c315ae4cc2297606fe74f8a7136e28d0d4a47ca9cd46fe1b41fbd';old=read(oldp)
newp=offer['module_ledger'];assert H(P(newp))==offer['module_ledger_sha256']=='448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367';new=read(newp)
inp=read(B+'lft/lft-source51-input-bindings-v1.json');assert H(P(B+'lft/lft-source51-input-bindings-v1.json'))=='ef9aa484215f8d5358de7968a851ba79d857b69157b7cd33cf6cbf7077c42c83'
rv=inp['entire_original_review_body_and_time'];rr=inp['original_review'];assert read(rr['path'])==rv and H(P(rr['path']))==rr['sha256']=='54e1f8c16c4228601bc1e2afd711ddb69abbcbbc51ea66bdd891ff1060a2b10c';assert rv['reviewed_at_utc']==rr['original_review_time'] and rv['whole_exercise_approved'] and not rv['remaining_gaps'] and not rv['errors']
inv=read(inp['inventory']);assert H(P(inp['inventory']))==H(P('book/coverage/inventory.json'))==inp['inventory_sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
ix={k:{r['key']:r for r in inv[k]} for k in ['exercises','material_source_units']};key=inp['whole_exercise_key'];assert key=='nn-in-the-loop.html::exercise-15' and rv['entire_original_exercise_record']==ix['exercises'][key]
be={e['inventory_key']:e for e in old['exercises']};ce={e['inventory_key']:e for e in new['exercises']};assert be.keys()==ce.keys() and len(be)==217
reviewref={'file':rr['path'],'sha256':rr['sha256'],'reviewer':rr['reviewer'],'original_review_time':rr['original_review_time']}
for k,e in be.items():
 if k!=key:assert ce[k]==e,k
row=ce[key];assert row['status']=='complete_math' and row['independent_whole_source_review']==reviewref and row['claims'][:-1]==[c for c in be[key]['claims'] if c['status'] in ['proved','not_a_formal_claim']]
a=row['claims'][-1];assert a['statement_in_prose']==ix['exercises'][key]['source_text'] and a['status']=='proved' and a['lean_declarations']==rv['lean_declarations'] and a['hypotheses']==rv['hypotheses'] and a['correspondence']==rv['correspondence'] and not a['remaining_gaps'] and a['scope_limits']==rv['limits'] and a['source_unit_keys']==inp['material_unit_keys'] and a['independent_source_review']==reviewref
bm={c['id']:c for c in old['material_claims']};cm={c['id']:c for c in new['material_claims']};assert bm.keys()==cm.keys()
units={u['source_unit_key']:u for u in rv['material_units']};assert set(units)==set(inp['material_unit_keys']) and len(units)==6
for cid,c in bm.items():
 n=cm[cid];k=cid.removesuffix('::claim-review')
 if k not in units:assert n==c,cid;continue
 u=units[k];assert u['whole_unit_approved'] and u['material_status']=='proved' and not u['missing_clauses'] and u['entire_inventory_record']==ix['material_source_units'][k]
 assert n['prior_source51_claim_body_preserved']==c and n['statement_in_prose']==u['entire_inventory_record']['source_text'] and n['status']=='proved' and n['lean_declarations']==u['lean_declarations'] and n['hypotheses']==u['hypotheses'] and n['correspondence']==u['per_unit_reason'] and n['independent_source_review']==reviewref and not n['remaining_gaps'] and n['scope_limits']==rv['limits']
 z=copy.deepcopy(n);del z['prior_source51_claim_body_preserved'];z.pop('independent_source_review',None);z.pop('scope_limits',None)
 for field in ['statement_in_prose','status','kind','lean_declarations','hypotheses','correspondence','remaining_gaps']:z[field]=c[field]
 if 'independent_source_review' in c:z['independent_source_review']=c['independent_source_review']
 if 'scope_limits' in c:z['scope_limits']=c['scope_limits']
 assert z==c,cid
aliases=read(inp['canonical_path_aliases']['file'])['aliases'];assert H(P(inp['canonical_path_aliases']['file']))==inp['canonical_path_aliases']['sha256']
for o,p in aliases.items():assert H(P(p['path']))==p['sha256']
newpaths={p['source'] for p in inp['proof_files']};assert len(newpaths)==2 and set(new['proof_files'])-set(old['proof_files'])==newpaths and len(new['proof_files'])==475
assert {k:p for k,p in new['proof_files'].items() if k not in newpaths}==old['proof_files'];assert new['declarations'][:len(old['declarations'])]==old['declarations']
newnames=[];pairrefs=[]
for p in inp['proof_files']:
 n=p['source'];assert H(P(n))==p['sha256']==new['proof_files'][n]['sha256'];actualpub=[d['name'] for d in declarations(P(n).read_text()) if d['kind'] in ['theorem','lemma']];assert actualpub==p['public_declarations'];newnames+=actualpub
 for pair,mode in zip(p['actual_paired_records'],['lean_standalone','named_lean_module_build']):
  d=read(pair['actual_record']['path']);assert H(P(pair['actual_record']['path']))==pair['actual_record']['sha256'] and d['actual_exit_code']==0 and d['kind']==mode and d['source_unchanged']
  assert d['source_sha256_before']==d['source_sha256_after']==H(P(n));assert H(P(pair['raw_log']['path']))==pair['raw_log']['sha256']==d['log_sha256'];assert H(P(pair['source_snapshot']['path']))==pair['source_snapshot']['sha256']==H(P(n));assert aliases[d['log']]['path']==pair['raw_log']['path'] and aliases[d['source_snapshot']]['path']==pair['source_snapshot']['path'];pairrefs.append(pair['actual_record'])
assert len(newnames)==len(set(newnames))==16 and len(new['declarations'])==len(old['declarations'])+16
assert [d['name'] for d in new['declarations'][len(old['declarations']):]]==newnames
assert len(offer['proof_files'])==6 and offer['counts']['new_public_theorems']==64 and offer['counts']['new_whole_exercises']==8 and offer['counts']['new_distinct_physical_units']==48
for k,p in offer['proof_files'].items():assert H(P(k))==p['sha256']
for ep,h in offer['required_evidence_artifacts_sha256'].items():assert H(P(ep))==h,ep
for ep,h in offer['required_external_import_dependencies'].items():assert H(P(ep))==h,ep
for ep,h in inp['protected_selected22_and_owner_sha256'].items():assert H(P(ep))==h,ep
actual=read(offer['actual_builder']['file']);assert H(P(offer['actual_builder']['file']))==offer['actual_builder']['sha256'] and actual['actual_exit_code']==0
assert H(P(actual['log']))==actual['log_sha256']==offer['actual_builder_raw_log']['sha256'];assert H(P(offer['module_builder']))==offer['module_builder_sha256']==actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']
expected={'exercises':217,'exercise_status':dict(collections.Counter(e['status'] for e in new['exercises'])),'exercise_claim_status':dict(collections.Counter(q['status'] for e in new['exercises'] for q in e['claims'])),'material_claim_status':dict(collections.Counter(q['status'] for q in new['material_claims'])),'new_declarations':len(new['declarations'])};assert new['counts']==expected
assert new['counts']['exercise_status']=={'complete_math':179,'pending':24,'partial':14}
prior=B+'modules23-source51-identity-independent-applied-confirmation-v1.json';assert H(P(prior))=='1ffa742014825773202863faae9ddbaab24ca074aeff3a81f7aeedee019e3e4b'
for ep,h in offer['source_sha256'].items():assert H(P(ep))==h==inv['source_sha256'][ep]
report={'status':'passed_independent_isolated_module23_source51_combined_lft_candidate_mechanics','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[],'offer':ref(offerp),'candidate':ref(newp),'helper':ref(offer['module_builder']),'actual_isolated_builder':offer['actual_builder'],'actual_isolated_builder_raw_log':offer['actual_builder_raw_log'],'original_source51_identity_candidate':ref(oldp),'entire_prior_source51_identity_peer':read(prior),'original_full_lft_semantic_review':rr,'original_full_lft_semantic_body_and_time_preserved':True,'fresh_canonical_binding_peer':offer['lft23_canonical_binding_peer'],'entire_input_bindings':ref(B+'lft/lft-source51-input-bindings-v1.json'),'one_new_whole_exercise_key':key,'six_new_whole_material_unit_keys':inp['material_unit_keys'],'other216_exercise_and5177_material_bodies_exact':True,'all473_old_proof_rows_and3079_prefix_except16_new_names_exact':True,'new_sources':2,'new_public_theorems':16,'actual_four_passing_pair_records':pairrefs,'final_offer_counts':offer['counts'],'all178_required_evidence_hashes_and_import_dependencies_exact':len(offer['required_evidence_artifacts_sha256']),'all_selected22_sources_and_live_owner_assets_match_input_protection':True,'current_source51_inventory':ref(inp['inventory']),'actual_checker':ref(__file__),'scope':'Narrow final delta mechanics only. Original full semantic decisions and times retained. No new semantic review, compiler execution, live owner installation, global validator or aggregate23 claim.'}
out=Path('/tmp/modules23-source51-lft-final-candidate-independent-applied-confirmation-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':ref(out),'status':'passed','combined_counts':offer['counts']}))
