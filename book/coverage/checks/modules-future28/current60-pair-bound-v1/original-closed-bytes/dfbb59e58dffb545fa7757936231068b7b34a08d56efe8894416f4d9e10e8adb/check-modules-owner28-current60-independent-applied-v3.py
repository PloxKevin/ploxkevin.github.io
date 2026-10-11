from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,collections,re
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_bytes());ref=lambda p:{'file':str(p),'sha256':H(p)}
REPORT=Path('/tmp/modules-current60-owner28-candidate-v2/modules-current60-owner28-candidate-preparation-v2.json');assert H(REPORT)=='c7d4125e655be934067bfcbabe6d19e8eaf04a90b7cad7a4ecf1ed6eb2e245b0';report=J(REPORT);C=Path(report['candidate']['file']);assert H(C)==report['candidate']['sha256']=='e1d7dc6ecbd108df97d891852c2bb64d1913c563e4cdf5c1656d921fb1e01c5a';c=J(C)
BASE=Path(report['original_owner']['file']);assert H(BASE)==H(R/'book/coverage/modules.json')=='7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487';b=J(BASE)
OLDREPORT=Path(report['original_v1_preparation']['file']);orpt=J(OLDREPORT);PLAN=Path(orpt['approved_scope_plan']['file']);assert H(PLAN)==orpt['approved_scope_plan']['sha256'];plan=J(PLAN)
ID=Path(report['identity']['file']);assert H(ID)==report['identity']['sha256'];identity=J(ID);I=R/'book/coverage/inventory.json';assert H(I)=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a';inv=J(I);oldinv=J(R/'book/coverage/inventory-after-correction55.json')
selected=J(R/'reports/full-coverage/checkpoint-27-selection.json');assert len(selected['proof_files'])==1175
owners={'book/coverage/core.json':'0bf99e01c47c7b9fa18488fdc3104c189e3977597c15f1c7e20253afad1245c0','book/coverage/foundations.json':'b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55','book/coverage/applied.json':'31b6af21c8ba9d214380ba5c116046bf7587eba3d736e1a536266c5fbfe61e68','book/coverage/applied-promotions.json':'72ee23132c02823bc13fa513d2892e79d748b6617b0d3fe52b3de7e29735a5a2','book/coverage/modules.json':'7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487'}
assets=dict(J(R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']);assets.update(inv['source_sha256']);protected={n:x['sha256']for n,x in selected['proof_files'].items()};protected.update(assets);protected.update(owners);protected['book/coverage/inventory.json']=H(I)
def guard():
 for n,h in protected.items():assert H(R/n)==h,n
 guard_assertions=None
guard();started=datetime.now(timezone.utc).isoformat();exmap={r['key']:r for r in inv['exercises']};unitmap={r['key']:r for r in inv['material_source_units']};oldex={r['key']:r for r in oldinv['exercises']};oldu={r['key']:r for r in oldinv['material_source_units']}
assert set(identity['owned_exercises'])=={k for k,x in exmap.items()if x['source']in b['scope_pages']} and len(identity['owned_exercises'])==217
assert set(identity['owned_material_units'])=={k for k,x in unitmap.items()if x['source']in b['scope_pages']} and len(identity['owned_material_units'])==4977
for section,newmap,oldmap in [('owned_exercises',exmap,oldex),('owned_material_units',unitmap,oldu)]:
 for k,row in identity[section].items():assert row['original55_text_sha256']==oldmap[k]['text_sha256'] and row['actual60_text_sha256']==newmap[k]['text_sha256'] and row['unchanged_literal']is(row['original55_text_sha256']==row['actual60_text_sha256'])
assert {k for k,r in identity['owned_exercises'].items()if not r['unchanged_literal']}=={'lipsdp.html#book-m12-b1'}
assert {k for k,r in identity['owned_material_units'].items()if not r['unchanged_literal']}=={'verification.html::node-193','lipsdp.html::node-998'}
for k,row in identity['exact_changed_full_inventory_records'].items():assert row['original55']==(oldex if k in oldex else oldu)[k] and row['actual60']==(exmap if k in exmap else unitmap)[k]
assert c['source_sha256']=={n:inv['source_sha256'][n]for n in b['scope_pages']}
# True whole-review body/time pointers are checked exactly; no semantic redecision.
refs={str(REPORT):H(REPORT),str(C):H(C),str(BASE):H(BASE),str(OLDREPORT):H(OLDREPORT),str(PLAN):H(PLAN),str(ID):H(ID),'book/coverage/inventory.json':H(I)}
peer_paths={r['whole_peer']['file']:r['whole_peer']['sha256']for r in plan['exercise_scope']+plan['material_scope']};peer_paths[report['independent_full17_commissioning_peer']['file']]=report['independent_full17_commissioning_peer']['sha256']
for n,h in peer_paths.items():assert H(n)==h and J(n).get('errors')==[];refs[n]=h
assert len(plan['exercise_scope'])==4 and len(plan['material_scope'])==24
exscope={r['inventory_key']:r for r in plan['exercise_scope']};mat_scope={r['inventory_key']:r for r in plan['material_scope']};comm=J(report['independent_full17_commissioning_peer']['file']);assert comm['public_theorem_count']==17
for row in comm['material_units']:
 assert row['whole_unit_approved']is True and row['missing_clauses']==[] and row['entire_current60_inventory_record']==unitmap[row['inventory_key']];mat_scope[row['inventory_key']]=row
assert len(mat_scope)==26
for key,row in exscope.items():
 e=next(x for x in c['exercises']if x['inventory_key']==key);old=next(x for x in b['exercises']if x['inventory_key']==key)
 assert e['status']=='complete_math' and e['entire_literal_closure28']['whole_exercise_approved']is True and e['entire_literal_closure28']['remaining_gaps']==[]
 assert e['source_text_sha256']==exmap[key]['text_sha256'] and e['entire_literal_closure28']['unchanged_original_semantic_peer']==row['whole_peer']
 for oc,nc in zip(old['claims'],e['claims']):
  assert oc['id']==nc['id'] and oc['statement_in_prose']==nc['statement_in_prose']
  if oc['status']!='pending':assert oc==nc
  else:
   assert nc['status']in ['proved','not_a_formal_claim'] and nc['remaining_gaps']==[] and nc['independent_source_review']==row['whole_peer']
   if nc['status']=='proved':assert nc['lean_declarations']
# Reverse whole source60 identities and exactly the approved old-pending transitions.
rev=copy.deepcopy(c)
for e,old in zip(rev['exercises'],b['exercises']):
 assert e['inventory_key']==old['inventory_key'];assert e['source60_literal_identity']==report['identity'];e.pop('source60_literal_identity');e['source_sha256']=old['source_sha256'];e['source_text_sha256']=old['source_text_sha256']
 if e['inventory_key']in exscope:
  e.pop('entire_literal_closure28');e['status']=old['status'];e['claims']=copy.deepcopy(old['claims'])
 assert e==old
for cl,old in zip(rev['material_claims'],b['material_claims']):
 assert cl['id']==old['id'] and cl['source60_literal_identity']==report['identity']
 key=cl['source_unit_keys'][0]if len(cl['source_unit_keys'])==1 else None
 if key in mat_scope and cl['id']==key+'::claim-review':
  assert old['status']=='pending' and cl['status']=='proved' and cl['remaining_gaps']==[] and cl['whole_current60_source_unit_approved']is True and cl['actual_current60_text_sha256']==unitmap[key]['text_sha256']
  assert cl['statement_in_prose']==unitmap[key]['source_text'] and cl['lean_declarations']
  cl.clear();cl.update(copy.deepcopy(old))
 else:cl.pop('source60_literal_identity');assert cl==old
assert len(c['declarations'])-len(b['declarations'])==153 and c['declarations'][:len(b['declarations'])]==b['declarations'];rev['declarations']=copy.deepcopy(b['declarations'])
newproofs=set(c['proof_files'])-set(b['proof_files']);assert len(newproofs)==5
names=[]
for n in newproofs:
 m=c['proof_files'][n];assert m['standalone_compile_status']=='pending_actual_root_canonical_pairs' and m['canonical_paired_evidence_not_yet_available']is True
 p=Path(m['original_tmp_source']['file']);assert H(p)==m['sha256']==m['original_tmp_source']['sha256'];names+=m['declarations'];trial=Path(m['original_tmp_trial']['file']);t=J(trial);assert type(t['actual_exit_code'])is int and t['actual_exit_code']==0 and t['protection_errors']==[];assert H(t['raw_log'])==t['raw_log_sha256'] and t['source_sha256_before']==t['source_sha256_after']==m['sha256'] and t['source']==str(p) and t['actual_command']==['lake','env','lean',str(p)];assert H(t['source_snapshot'])==m['sha256'];refs[str(p)]=H(p);refs[str(trial)]=H(trial);refs[t['raw_log']]=t['raw_log_sha256'];refs[t['source_snapshot']]=m['sha256'];rev['proof_files'].pop(n)
assert len(names)==len(set(names))==153 and set(names)=={r['name']for r in c['declarations'][len(b['declarations']):]}
for n,v in b['proof_files'].items():assert rev['proof_files'][n]==v
for k in set(rev)-set(b):rev.pop(k)
for k in ['source_sha256','chapter_fragment_sha256','current_inventory','current_inventory_sha256','generated_at_utc','status','counts','current_identity_binding_validation']:rev[k]=copy.deepcopy(b[k])
assert rev==b
counts={'exercises':len(c['exercises']),'exercise_status':dict(collections.Counter(e['status']for e in c['exercises'])),'exercise_claim_status':dict(collections.Counter(x['status']for e in c['exercises']for x in e['claims'])),'material_claim_status':dict(collections.Counter(x['status']for x in c['material_claims'])),'new_declarations':len(c['declarations'])};assert counts==c['counts']==report['counts']
for i in [1,2]:
 native=Path(f'/tmp/modules-current60-owner28-candidate-preparation-actual-v{i}.json');n=J(native);assert type(n['actual_exit_code'])is int and n['actual_exit_code']==0 and n['protection_errors']==[];assert n['source_owner_selection_bytes_unchanged']is True and n['protected_selected_proof_sources']==1175 and n['actual_command']==['python3',f'/tmp/prepare-modules-current60-owner28-candidate-v{i}.py'];refs[str(native)]=H(native)
 for key in ['raw_log','helper','runner','proposal']:
  rr=n[key];assert H(rr['file'])==rr['sha256'];refs[rr['file']]=rr['sha256']
for n,h in refs.items():assert H(Path(n)if Path(n).is_absolute()else R/n)==h
guard()
out={'status':'passed_independent_isolated_modules28_current60_pending_pair_candidate_mechanics','errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'started_at_utc':started,'candidate':ref(C),'request':ref(REPORT),'original_installed27_owner':ref(BASE),'current60_owned_identity':ref(ID),'entire_candidate_inverse_restores_installed27_owner_exact':True,'scope_counts':{'owned_exercises':217,'owned_physical_units':4977,'unchanged_exercise_literals':216,'unchanged_material_literals':4975,'proposed_whole_exercises':4,'proposed_whole_units':26,'new_sources':5,'new_public_declarations':153,'old_proof_metadata':len(b['proof_files']),'original_declaration_prefix':len(b['declarations'])},'whole_semantic_peer_bodies_times_preserved':list(peer_paths),'counts':counts,'all_five_actual_canonical_pairs_still_pending_in_this_candidate':True,'commissioning_whole976_or_other_scope_approved':False,'closed_evidence_sha256':refs,'protected_inputs_sha256':protected,'scope':'Read-only exact mechanics, approved literal-to-claim mapping and identity inverse. Pending-pair draft approval does not authorize installation or infer compiler/kernel/canonical success. Every original nonpending claim, proof metadata, prior declaration prefix and history field is exact. Source60 literal changes are explicitly bound to already-independent full58/59 semantic peers, without modifying their review bodies/times.'}
P=Path('/tmp/modules28-current60-pending-candidate-independent-applied-confirmation-v3.json');assert not P.exists();P.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(P),'status':out['status'],'counts':out['scope_counts']}))
