"""NEW isolated Module26 candidate: reviewed Landscape and Gaussian smoothing wholes.

Only Wind4 and cumulative Smoothing44 are Module-owned new sources. Applied
explicitly supplies cumulative CVaR8. Original semantic bodies/times and earlier
positive atoms remain exact. No installed ledger/HTML/inventory writes.
"""
from pathlib import Path
from datetime import datetime,timezone
import collections,copy,hashlib,json,re,sys
from lean_names import declarations
R=Path(__file__).resolve().parents[2];B='book/coverage/checks/modules-future26/source52'
LC='book/coverage/checks/modules-future26/landscape/modules26-landscape-candidate-source52-v1.json'
READY='book/coverage/checks/modules-future26/smoothing/modules-smoothing44-canonical-paired-readiness26-v1.json';READY_SHA='24f5a46e732dc763cd34170619c692efefe91c4a565ee5756f0b73998246933a'
LIVE='book/coverage/modules.json';LIVE_SHA='9f3736a26e2c729b138fd4cc10b3376d67d475b1e759e4fe56fb393c27e08a63';INV='book/coverage/inventory-after-correction52.json';INV_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';EX='verification.html#practice-medium-3'
def P(n):return Path(n)if Path(n).is_absolute()else R/n
def H(n):return hashlib.sha256(P(n).read_bytes()).hexdigest()
def J(n):return json.loads(P(n).read_text())
def ref(n):return {'file':n,'sha256':H(n)}
def put(n,d):
 p=P(n);assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def zero(d):
 cs=[d[k]for k in['actual_exit_code','exit_code']if k in d];assert cs and all(type(x)is int and x==0 for x in cs)
def names(n):return [d['name']for d in declarations(P(n).read_text())if d['kind']in['theorem','lemma']]
def add_decl(out,n,ds):
 seen={d['name']for d in out['declarations']};text=P(n).read_text()
 for name in ds:
  if name in seen:continue
  m=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert m,name
  out['declarations'].append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip()});seen.add(name)
def main():
 assert H(LIVE)==LIVE_SHA and H(INV)==H('book/coverage/inventory.json')==INV_SHA and H(READY)==READY_SHA
 old=J(LIVE);lc=J(LC);integ=lc['reviewed_work_integration26_landscape_candidate'];assert integ['baseline25_module_ledger']['sha256']==LIVE_SHA and H(integ['baseline25_module_ledger']['file'])==LIVE_SHA
 ready=J(READY);peer=J(ready['original_full_source_peer']['file']);assert H(ready['original_full_source_peer']['file'])==ready['original_full_source_peer']['sha256']=='f2c3ae9788f2249e0479a08089922a757ca6d6df6cb77444676174d59b761c63';assert peer==ready['entire_original_full_source_peer_body_and_time']and peer['whole_exercise_approved']is True and peer['errors']==[] and peer['remaining_full_literal_bridges']==[]
 selection=J('reports/full-coverage/checkpoint-25-selection.json');assert len(selection['proof_files'])==1156
 protected=ready['protected_input_sha256']
 for n,h in protected.items():assert H(n)==h,n
 for n,row in selection['proof_files'].items():assert H(n)==row['sha256']
 iv=J(INV);em={e['key']:e for e in iv['exercises']};um={u['key']:u for u in iv['material_source_units']};assert peer['entire_exercise_record']==em[EX]
 units=peer['material_units'];keys=[u['source_unit_key']for u in units];assert len(keys)==len(set(keys))==6 and set(keys)=={'verification.html::node-'+str(n)for n in[1034,1035,1041,1045,1047,1049]}
 for u in units:assert u['entire_inventory_record']==um[u['source_unit_key']]and u['whole_unit_approved']is True and u['missing_clauses']==[]
 source=ready['source']['file'];digest=ready['source']['sha256'];assert H(source)==H(ready['source_snapshot']['file'])==digest and source not in selection['proof_files'] and source not in old['proof_files'] and len(names(source))==44
 aliases=ready['original_TMP_byte_copies']
 for original,r in aliases.items():assert P(original).read_bytes()==P(r['file']).read_bytes()and H(r['file'])==r['sha256']
 out=copy.deepcopy(lc);e=next(e for e in out['exercises']if e['inventory_key']==EX);prior=copy.deepcopy(e);assert e['status']=='pending';e['claims']=[]
 for i,g in enumerate(peer['components'],1):
  assert g['missing_clauses']==[]and g['component_approved']is True
  e['claims'].append({'id':EX+'::source52-reviewed26-complete-clause-'+str(i),'statement_in_prose':g['group'],'kind':'independently_reviewed_complete_smoothed_classifier_clause','status':'proved','lean_declarations':copy.deepcopy(g['lean_declarations']),'hypotheses':copy.deepcopy(g['hypotheses']),'correspondence':g['reason'],'remaining_gaps':[],'source_unit_keys':[k for k in keys if k!='verification.html::node-1035'],'independent_source_review':ready['original_full_source_peer'],'entire_original_component_body_and_review_time':copy.deepcopy(g),'original_whole_review_time':peer['reviewed_at_utc']})
 e.update(status='complete_math',prior_source52_pending_exercise_body_preserved26=prior,independent_whole_source_review26=ready['original_full_source_peer'],entire_original_whole_review_body_and_time_preserved26=peer)
 for u in units:
  k=u['source_unit_key'];row=next(c for c in out['material_claims']if c['id']==k+'::claim-review');assert row['status']=='pending';priorrow=copy.deepcopy(row)
  row.update(statement_in_prose=um[k]['source_text'],kind='independently_reviewed_complete_mathematical_source_unit'if u['material_status']=='proved'else'individually_reviewed_navigation_instruction',status='proved'if u['material_status']=='proved'else'not_a_formal_claim',lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_unit_reason'],remaining_gaps=[],source_unit_keys=[k],independent_source_review=ready['original_full_source_peer'],entire_original_literal_decision_and_review_time=copy.deepcopy(u),original_full_review_time=peer['reviewed_at_utc'],prior_source52_pending_claim_body_preserved26=priorrow)
 ns=names(source);pairs=[];ev={ready['source_snapshot']['file']:digest}
 for raw,kind in zip(ready['actual_canonical_pair'],['standalone','named-build']):
  a=J(raw['file']);assert H(raw['file'])==raw['sha256'];zero(a);assert a['source']==source and a['source_sha256_before']==a['source_sha256_after']==digest and H(a['log'])==a['log_sha256'];want=['lake','env','lean',source.removeprefix('verification/lean/')]if kind=='standalone'else['lake','build','SafeLearning.'+Path(source).stem];assert a['command']==want
  pairs.append({'source':ref(source),'kind':kind,'actual_record':ref(raw['file']),'raw_log':ref(a['log']),'source_snapshot':ready['source_snapshot'],'actual_exit_code':0,'entire_original_actual_record_and_time':a});ev.update({raw['file']:raw['sha256'],a['log']:a['log_sha256']})
 assert len(pairs)==2
 stand=pairs[0];compile_ev={'file':source,'sha256':digest,'exit_code':0,'source_unchanged':True,'compiler_manifest':stand['actual_record']['file'],'compiler_manifest_sha256':stand['actual_record']['sha256'],'log':stand['raw_log']['file'],'log_sha256':stand['raw_log']['sha256']}
 own={'sha256':digest,'declarations':ns,'actual_paired_records':pairs,'evidence_sha256':ev}
 out['proof_files'][source]={'sha256':digest,'proof_selection_owner':'Modules26','selection_scope':'independently_whole_reviewed_current52_smoothing_classifier_cumulative44_only','standalone_compile_status':'passed','standalone_compile_evidence':compile_ev,'actual_paired_records':pairs,'declarations':ns};add_decl(out,source,ns)
 for u in units:assert set(u['lean_declarations'])<=set(ns)
 out['generated_at_utc']=datetime.now(timezone.utc).isoformat();ownproofs=copy.deepcopy(integ['Module_owned_new_proofs']);ownproofs[source]=own;assert len(ownproofs)==2 and sum(len(r['declarations'])for r in ownproofs.values())==48
 inp=B+'/modules26-combined-source52-input-bindings-v1.json';candidate=B+'/modules26-combined-candidate-source52-v1.json';integrity=B+'/modules26-combined-source52-candidate-integrity-v1.json'
 out['reviewed_work_integration26_combined_candidate']={'baseline25_module_ledger':integ['baseline25_module_ledger'],'landscape_isolated_candidate':ref(LC),'landscape_builder_actual_execution':ref('book/coverage/checks/modules-future26/landscape/modules26-landscape-isolated-candidate-builder-actual-v2.json'),'current_inventory':ref(INV),'smoothing_canonical_readiness':ref(READY),'original_smoothing_whole_review':ready['original_full_source_peer'],'entire_original_smoothing_full_body_and_review_time':peer,'original_closed_smoothing_TMP_byte_aliases':aliases,'Module_owned_new_proofs':ownproofs,'explicit_cross_owner_required_proofs':integ['explicit_cross_owner_required_proofs'],'fresh_whole_exercise_keys':['landscape.html::exercise-15',EX],'fresh_physical_unit_keys':integ['fresh_physical_unit_keys']+keys,'whole_smoothed_classifier_domain':'deterministic or independently fixed-law randomized base; sample confidence given its true probability-bound premise; strict perturbation ball only','Module_new_source_count':2,'Module_new_public_export_count':48,'cross_owner_new_source_count':1,'cross_owner_new_public_export_count':8,'old37_source_duplicate_selected':False,'old_quantile1_source_duplicate_selected':False,'live_owner_assets_mutated':False}
 out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(e['status']for e in out['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status']for e in out['exercises']for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status']for c in out['material_claims'])),'new_declarations':len(out['declarations'])}
 for e0,e1 in zip(lc['exercises'],out['exercises']):
  if e0['inventory_key']!=EX:assert e0==e1
 for c0,c1 in zip(lc['material_claims'],out['material_claims']):
  if c0['id']not in[k+'::claim-review'for k in keys]:assert c0==c1
 for n,row in lc['proof_files'].items():assert out['proof_files'][n]==row
 assert out['declarations'][:len(lc['declarations'])]==lc['declarations']
 for n,h in protected.items():assert H(n)==h,n
 bindings={'status':'passed_exact_two_whole_current52_exercises_and_nine_physical_decisions_bound','errors':[],'baseline25_module_ledger':integ['baseline25_module_ledger'],'current_inventory':ref(INV),'landscape_input_bindings':ref('book/coverage/checks/modules-future26/landscape/modules26-landscape-source52-input-bindings-v1.json'),'smoothing_canonical_readiness':ref(READY),'original_smoothing_whole_review':ready['original_full_source_peer'],'entire_original_smoothing_whole_review_body_and_time':peer,'smoothing_physical_literal_decisions':units,'Module_owned_new_proofs':ownproofs,'explicit_cross_owner_required_proofs':integ['explicit_cross_owner_required_proofs'],'protected_input_sha256':protected,'old37_source_duplicate_selected':False,'old_quantile1_source_duplicate_selected':False}
 put(inp,bindings);put(candidate,out);put(integrity,{'status':'passed_isolated_combined26_candidate_mapping','errors':[],'candidate':ref(candidate),'input_bindings':ref(inp),'baseline25_module_ledger':integ['baseline25_module_ledger'],'inventory':ref(INV),'fresh_whole_exercise_keys':['landscape.html::exercise-15',EX],'fresh_physical_unit_keys':integ['fresh_physical_unit_keys']+keys,'old_other_exercise_bodies_exact':215,'old_material_bodies_exact_except_seven_prior_pending_rows':len(old['material_claims'])-7,'old_proof_rows_exact':len(old['proof_files']),'old_declaration_prefix_exact':True,'own_new_sources':2,'own_new_public_exports':48,'cross_owner_new_sources':1,'cross_owner_new_public_exports':8,'coverage_complete':False,'live_owner_assets_mutated':False})
 print(json.dumps({'candidate':ref(candidate),'input_bindings':ref(inp),'integrity':ref(integrity),'counts':out['counts']}))
if __name__=='__main__':main()
