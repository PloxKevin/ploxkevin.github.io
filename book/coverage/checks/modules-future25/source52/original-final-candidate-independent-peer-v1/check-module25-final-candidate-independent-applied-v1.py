from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,collections,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def H(n):return sha(ROOT/n)
def J(n):return json.loads((ROOT/n).read_text())
def checkref(r):assert set(r)>={'file','sha256'} and H(r['file'])==r['sha256'];return J(r['file']) if r['file'].endswith('.json') else None
base='book/coverage/checks/modules-future25/source52/'
offerpath=base+'modules-audit25-candidate-source52-additions-draft-v1.json';assert H(offerpath)=='161a23a6393758503822b47ffc68147f4480bb0e1c60e5614ec995c75916e9fe'
o=J(offerpath);assert o['live_owner_assets_mutated'] is False and o['coverage_complete'] is False
cp=o['module_ledger'];assert H(cp)==o['module_ledger_sha256']=='9f3736a26e2c729b138fd4cc10b3376d67d475b1e759e4fe56fb393c27e08a63';c=J(cp)
old=checkref(o['baseline24_module_ledger']);inp=checkref(o['candidate_input_bindings']);integrity=checkref(o['candidate_binding_integrity']);assert integrity['errors']==[] and 'passed' in integrity['status']
assert H('book/coverage/modules.json')==o['baseline24_module_ledger']['sha256']=='1d4395c5b7cb9dc18217b0c4236a04868f67a2445d0ffed18f3a77215d3b2c90'
assert H(o['current_inventory'])==H('book/coverage/inventory.json')==o['current_inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';inv=J(o['current_inventory'])
units={u['key']:u for u in inv['material_source_units']};exs={e['key']:e for e in inv['exercises']}
for n,h in inp['protected_live_owner_inventory_sha256'].items():assert H(n)==h,n
protected=copy.deepcopy(inp['protected_live_owner_inventory_sha256'])
assert o['source_sha256']==old['source_sha256']==c['source_sha256']
for n,h in o['source_sha256'].items():assert H(n)==h==inv['source_sha256'][n]
for n,h in o['required_evidence_artifacts_sha256'].items():assert H(n)==h,n
assert len(o['required_evidence_artifacts_sha256'])==83
assert H(o['module_builder'])==o['module_builder_sha256']=='b0475081fe0f4adad151bea4a0b13b34094d75d495f6593b3c013d0ecb6777fd'
actual=checkref(o['actual_builder']);checkref(o['actual_builder_raw_log']);assert actual['actual_exit_code']==0
assert actual['actual_command'][1]==o['module_builder'] and actual['helper_sha256_before']==actual['helper_sha256_after']==o['module_builder_sha256']
assert actual['raw_log_sha256']==o['actual_builder_raw_log']['sha256']
whole=inp['entire_original_whole_answer_b_review_body_and_time'];supp=inp['entire_selected_generic_order_evidence_supplement_body_and_time'];temporal=inp['entire_original_temporal_component_review_body_and_time']
for r,body in zip(o['original_full_or_precise_source_reviews'],[whole,supp,temporal]):assert checkref(r)==body
assert supp['entire_original_peer_body_decisions_and_time']==whole
binding=checkref(o['canonical_original_body_binding_peer']);assert binding['errors']==[] and 'passed' in binding['status'];assert binding['entire_original_component_peer_body_and_time']==temporal
assert checkref(inp['canonical_temporal_binding_peer'])==binding and inp['canonical_temporal_binding_peer']==o['canonical_original_body_binding_peer']
ready=checkref(inp['canonical_readiness']);b=whole['material_units'][0];t=temporal['material_units'][0]
assert b['entire_inventory_record']==units[b['key']] and t['entire_inventory_record']==units[t['key']]
assert b['whole_mathematical_unit_approved'] is True and t['whole_source_unit_approved'] is False
exkey='nn-in-the-loop.html::exercise-20';assert temporal['exercise']['entire_inventory_record']==exs[exkey]
bkey='nn-in-the-loop.html::node-1260';tkey='nn-in-the-loop.html::node-1262';assert b['key']==bkey and t['key']==tkey
aliases=inp['explicit_namespace_prefix_aliases'];assert aliases=={'SafeLearning.CompleteModulesNNDoublyHyperdominant24':'SafeLearning.CompleteModulesNNDoublyHyperdominant25','SafeLearning.CompleteModulesNNTemporalDiagonal24':'SafeLearning.CompleteModulesNNTemporalDiagonal25'}
def mapped(names):return [next((name.replace(a,b,1) for a,b in aliases.items() if name.startswith(a+'.')),name) for name in names]
assert len(t['components'])==3
oldex=next(e for e in old['exercises'] if e['inventory_key']==exkey);newex=next(e for e in c['exercises'] if e['inventory_key']==exkey)
assert newex['status']==oldex['status']=='partial' and newex['claims'][:len(oldex['claims'])]==oldex['claims']
assert len(newex['claims'])==len(oldex['claims'])+4
wholenames=list(dict.fromkeys(b['lean_declarations']+supp['selected_lean_declarations']));wholehyp=b['hypotheses']+supp['hypotheses'];wholereason=b['per_component_reason']+' '+supp['binding_reason']
wholeatom=newex['claims'][len(oldex['claims'])]
assert wholeatom['id']==exkey+'::source52-reviewed25-whole-answer-b' and wholeatom['status']=='proved'
assert wholeatom['statement_in_prose']==units[bkey]['source_text'] and wholeatom['lean_declarations']==wholenames and wholeatom['hypotheses']==wholehyp and wholeatom['correspondence']==wholereason
assert wholeatom['entire_original_unit_review_body_and_time']==b and wholeatom['remaining_gaps']==[]
oldmat={m['id']:m for m in old['material_claims']};newmat={m['id']:m for m in c['material_claims']}
mb=newmat[bkey+'::claim-review'];mt=newmat[tkey+'::claim-review']
assert mb['prior_source52_pending_claim_body_preserved']==oldmat[mb['id']] and mb['entire_original_whole_unit_review_body_and_time']==whole
assert mb['status']=='proved' and mb['lean_declarations']==wholenames and mb['hypotheses']==wholehyp and mb['correspondence']==wholereason and mb['remaining_gaps']==[]
assert mt['status']=='pending' and mt['remaining_gaps']==t['remaining_gaps'] and mt['prior_source52_claim_body_preserved25']==oldmat[mt['id']]
newatoms=newex['claims'][len(oldex['claims'])+1:];newmats=c['material_claims'][len(old['material_claims']):]
assert len(newmats)==len(newatoms)==3
for g,a,m in zip(t['components'],newatoms,newmats):
 assert g['missing_clauses']==[] and a['status']==m['status']=='proved'
 assert a['entire_original_component_body_and_time_preserved']==g and a['original_component_review_time']==temporal['reviewed_at_utc']
 assert a['lean_declarations']==mapped(g['lean_declarations']) and a['hypotheses']==g['hypotheses']
 assert a['correspondence']==a['statement_in_prose']==g['per_component_reason'] and a['source_unit_keys']==[tkey]
 assert a['remaining_gaps']==[] and a['explicit_namespace_prefix_aliases']==aliases
 aa=copy.deepcopy(a);aa['id']=exkey+'::material-source52-reviewed25-temporal-component-'+g['component_id'];assert aa==m
# Independent inverse: restoring archived rows and removing exactly the reviewed additions recovers every old byte-decoded semantic field.
r=copy.deepcopy(c);r['generated_at_utc']=old['generated_at_utc'];r['counts']=old['counts'];r.pop('reviewed_work_integration25_candidate')
ri=next(i for i,e in enumerate(r['exercises']) if e['inventory_key']==exkey);r['exercises'][ri]=copy.deepcopy(oldex)
r['material_claims']=r['material_claims'][:len(old['material_claims'])]
for i,m in enumerate(r['material_claims']):
 if m['id'] in [mb['id'],mt['id']]:r['material_claims'][i]=copy.deepcopy(oldmat[m['id']])
chain=inp['selected24_reused_order_source']['file'];assert chain not in old['proof_files'];assert len(o['proof_files'])==2
for n in list(o['proof_files'])+[chain]:r['proof_files'].pop(n)
r['declarations']=r['declarations'][:len(old['declarations'])]
assert r==old,'exact inverse failed'
assert len(old['proof_files'])==478 and len(c['proof_files'])==481 and len(old['declarations'])==3095 and len(c['declarations'])==3107
assert len(old['material_claims'])==5195 and len(c['material_claims'])==5198 and len(old['exercises'])==len(c['exercises'])==217
names=[]
for n,p in o['proof_files'].items():
 assert H(n)==p['sha256']==c['proof_files'][n]['sha256']
 public=[d['name'] for d in declarations((ROOT/n).read_text()) if d['kind'] in ('theorem','lemma')];assert public==p['declarations']==c['proof_files'][n]['declarations'];names+=public
 assert c['proof_files'][n]['actual_paired_records']==p['actual_paired_records']
 pairs=p['actual_paired_records'];assert len(pairs)==2
 for pair,kind in zip(pairs,['standalone','named-build']):
  ar=checkref(pair['actual_record']);checkref(pair['raw_log']);checkref(pair['source_snapshot']);assert pair['source']=={'file':n,'sha256':H(n)}
  assert ar['actual_exit_code']==pair['actual_exit_code']==0 and pair['kind']==kind
  assert ar['source']==n and ar['source_sha256_before']==ar['source_sha256_after']==ar['source_snapshot_sha256']==H(n)==pair['source_snapshot']['sha256']
  assert ar['raw_log_sha256']==pair['raw_log']['sha256'] and ar['raw_log']==pair['raw_log']['file'] and ar['source_snapshot']==pair['source_snapshot']['file']
  expected=['lake','env','lean',n.removeprefix('verification/lean/')] if kind=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
  assert ar['actual_command']==expected and ar['actual_workdir']==str(ROOT/'verification/lean')
  assert datetime.fromisoformat(ar['started_at_utc'])<datetime.fromisoformat(ar['finished_at_utc']) and ar['elapsed_seconds']>0
  assert H(ar['actual_runner'])==ar['actual_runner_sha256']
  for k,h in p['evidence_sha256'].items():assert H(k)==h
assert len(names)==9 and set(names)==set(sum([a['lean_declarations'] for a in newatoms],[]))
assert o['new_proof_file_count']==2 and o['new_theorem_or_lemma_count']==9
sr=supp['actual_original_standalone'];legacy=checkref(sr['canonical_record']);checkref(sr['canonical_raw_log']);checkref(sr['canonical_source_snapshot'])
assert legacy['exit_code']==0 and legacy['source']==chain and legacy['source_sha256_before']==legacy['source_sha256_after']==legacy['preserved_source_sha256']==H(chain)
assert legacy['log_sha256']==sr['canonical_raw_log']['sha256'];assert H(chain)==o['reused_selected24_proof_sources_sha256'][chain]
chainnames=[d['name'] for d in declarations((ROOT/chain).read_text()) if d['kind'] in ('theorem','lemma')]
assert set(supp['selected_lean_declarations'])<=set(chainnames) and c['proof_files'][chain]['declarations']==chainnames
assert c['declarations'][:len(old['declarations'])]==old['declarations']
appended=c['declarations'][len(old['declarations']):];assert [d['name'] for d in appended]==names+supp['selected_lean_declarations']
for d in appended:
 parsed={q['name']:q for q in declarations((ROOT/d['file']).read_text())};assert d['name'] in parsed
 assert d['statement'].startswith('theorem '+d['name'].rsplit('.',1)[1]) or d['statement'].startswith('lemma '+d['name'].rsplit('.',1)[1])
counts={'exercises':217,'exercise_status':dict(collections.Counter(e['status'] for e in c['exercises'])),'exercise_claim_status':dict(collections.Counter(a['status'] for e in c['exercises'] for a in e['claims'])),'material_claim_status':dict(collections.Counter(m['status'] for m in c['material_claims'])),'new_declarations':len(c['declarations'])}
assert counts==c['counts']==o['counts']
assert o['fresh_whole_exercise_keys']==[] and o['fresh_partial_exercise_keys']==[exkey] and o['fresh_whole_material_unit_keys']==[bkey] and o['fresh_precise_material_unit_keys']==[tkey]
manifest=J('reports/full-coverage/checkpoint-24-manifest.json');assert len(manifest['proof_files'])==1144 and len(manifest['frozen_inputs_sha256'])==40485
assert H(o['base_selection'])==o['base_selection_sha256']=='9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'
for n,row in manifest['proof_files'].items():assert H(n)==row['sha256']
assert chain in manifest['proof_files'] and manifest['proof_files'][chain]['sha256']==H(chain)
for n,h in manifest['frozen_inputs_sha256'].items():assert sha(ROOT/manifest['snapshot']/n)==h
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert H(n)==h
for n,h in protected.items():assert H(n)==h
out={'status':'passed_independent_isolated_module25_candidate_mapping_and_evidence_mechanics','errors':[],'reviewer':'applied_next','checked_at_utc':datetime.now(timezone.utc).isoformat(),'offer':{'file':offerpath,'sha256':H(offerpath)},'candidate':{'file':cp,'sha256':H(cp)},'exact_inverse_restores_entire_installed24_ledger':True,'original_full_b_review_and_selected_generic_supplement_body_times_preserved':True,'original_three_temporal_groups_hypotheses_reasons_gaps_times_preserved_with_explicit_namespace_aliases':True,'whole_unit1260_only_approved':True,'whole_c_and_exercise_remain_partial_pending':True,'old_proof_rows':478,'old_declaration_prefix':3095,'other_exercises_exact':216,'other_material_bodies_exact':5193,'new_sources':2,'new_public_exports':9,'actual_new_canonical_records':4,'selected24_generic_order_source_reused_not_new':chain,'required_closed_artifacts_rehashed':83,'selected24_sources_rehashed':1144,'frozen24_inputs_rehashed':40485,'current52_assets_rehashed':31,'live_owner_inventory_sha256_before_after_exact':protected,'counts':counts,'scope':'Read-only final mapping/evidence mechanics; original full semantic bodies and times are evidence. No semantic rerun, compiler, live mapping, whole-c/exercise, aggregate25 or delivery claim.'}
p=Path('/tmp/module25-final-candidate-independent-applied-findings-v1.json')
with p.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'sources':2,'exports':9,'old_proof_rows':478,'other_exercises':216,'other_material':5193}))
