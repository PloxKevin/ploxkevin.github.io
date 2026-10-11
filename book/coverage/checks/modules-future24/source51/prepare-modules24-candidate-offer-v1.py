"""Bind closed genuine candidate/compiler evidence in a new immutable draft."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[5]
B='book/coverage/checks/modules-future24/source51'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
J=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def put(n,d):
 p=R/n;assert not p.exists(),n;p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def main():
 # For this helper's placement, root is the sixth parent (source51 -> repository).
 assert (R/'book/coverage/modules.json').is_file()
 inpname=B+'/tanh24-source51-input-bindings-v1.json';inp=J(inpname)
 candidate=B+'/modules24-candidate-source51-v1.json';assert H(candidate)=='27a36bb3e324ce88a2122625b580af4bfde662b9ac50bce78e95850b2bbf18d2'
 cand=J(candidate);assert H(inp['baseline23_live_module_ledger']['file'])==inp['baseline23_live_module_ledger']['sha256']
 actual=B+'/modules24-candidate-builder-actual-execution-v2.json';a=J(actual)
 assert a['actual_exit_code']==0 and a['execution_kind']=='actual_isolated_candidate_preparation'
 builder='book/coverage/build_modules24_candidate_source51_v2.py'
 assert H(builder)==a['actual_helper_sha256_before']==a['actual_helper_sha256_after']
 assert H(a['raw_log'])==a['raw_log_sha256']
 aliases=copy.deepcopy(J(inp['canonical_original_path_aliases']['file'])['aliases']);artifacts={}
 for x in aliases.values():assert H(x['file'])==x['sha256'];artifacts[x['file']]=x['sha256']
 for row in inp['proof_files'].values():
  for pair in row['actual_paired_records']:
   ar=J(pair['actual_record']['file']);assert ar['actual_exit_code']==0
   for k in ['actual_record','raw_log','source_snapshot']:
    r=pair[k];assert H(r['file'])==r['sha256'];artifacts[r['file']]=r['sha256']
   old=Path(ar['actual_runner']);assert old.is_file()
   target=B+'/original-canonical-pair-runners/'+old.name;p=R/target;p.parent.mkdir(parents=True,exist_ok=True)
   if p.exists():assert p.read_bytes()==old.read_bytes()
   else:p.write_bytes(old.read_bytes())
   assert H(target)==ar['actual_runner_sha256'];aliases[str(old)]=ref(target);artifacts[target]=H(target)
 for n in [inpname,candidate,B+'/modules24-source51-candidate-integrity-v1.json',
  inp['baseline23_module_ledger']['file'],inp['canonical_original_path_aliases']['file'],inp['readiness']['file'],
  builder,'book/coverage/build_modules24_candidate_source51_v1.py',
  B+'/modules-isolated-candidate-actual-runner24-v1.py',
  B+'/modules24-candidate-builder-actual-execution-v1.json',B+'/modules24-candidate-builder-actual-execution-v1.log',
  actual,a['raw_log']]:artifacts[n]=H(n)
 aliasname=B+'/modules24-candidate-offer-original-path-aliases-v1.json'
 put(aliasname,{'status':'exact_original_source_trial_semantic_review_and_canonical_pair_runner_aliases','aliases':aliases,
  'original_absolute_paths_json_bodies_commands_times_unchanged':True})
 artifacts[aliasname]=H(aliasname)
 for n,h in inp['protected_owner_inventory_and31_asset_sha256'].items():assert H(n)==h
 proofs=copy.deepcopy(inp['proof_files']);assert len(proofs)==3
 names=[n for p in proofs.values() for n in p['declarations']];assert len(names)==len(set(names))==16
 offer=B+'/modules-audit24-candidate-source51-additions-draft-v1.json'
 put(offer,{'schema_version':1,'status':'isolated_source51_module24_candidate_draft_requires_independent_final_mechanics',
  'created_at_utc':datetime.now(timezone.utc).isoformat(),'current_inventory':inp['current_inventory']['file'],
  'current_inventory_sha256':inp['current_inventory']['sha256'],'module_ledger':candidate,'module_ledger_sha256':H(candidate),
  'module_builder':builder,'module_builder_sha256':H(builder),'actual_builder':ref(actual),
  'actual_builder_raw_log':ref(a['raw_log']),'proof_files':proofs,'proof_selection_owner':'Modules24',
  'baseline23_module_ledger':inp['baseline23_module_ledger'],'baseline23_selection':ref('reports/full-coverage/checkpoint-23-selection.json'),
  'candidate_input_bindings':ref(inpname),'candidate_binding_integrity':ref(B+'/modules24-source51-candidate-integrity-v1.json'),
  'source_sha256':cand['source_sha256'],'original_full_or_precise_source_reviews':inp['original_source_reviews'],
  'canonical_original_body_binding_peer':inp['canonical_binding_peer'],'canonical_path_aliases':ref(aliasname),
  'explicit_old_to_new_three_declaration_names':inp['explicit_old_to_new_three_declaration_names'],
  'fresh_whole_exercise_keys':[],'fresh_partial_exercise_keys':[inp['partial_exercise_key']],
  'fresh_material_unit_keys':inp['whole_material_unit_keys'],'fresh_partial_material_unit_keys':inp['partial_material_unit_keys'],
  'required_external_import_dependencies':inp['required_safelearning_import_sha256'],
  'required_evidence_artifacts_sha256':artifacts,'counts':{'new_sources':3,'new_distinct_public_theorems':16,
   'actual_paired_records':6,'approved_precise_component_groups':12,'new_whole_exercises':0,'new_partial_exercises':1,
   'new_whole_material_units':1,'reviewed_partial_material_units':3},
  'independent_final_candidate_mapping_peer_pending':True,'live_owner_assets_mutated':False,
  'requires_fresh_live_global_integrity_after_root_release':True,'coverage_complete':False,
  'scope_limits':['All original source51 mathematical decisions, hypotheses, reasons and review times are preserved.',
   'Original 12-body TMP source consists of the same nine original bodies and only three distinct new bodies; new canonical companion selects those three with explicit namespace aliases.',
   'Only answer(a), node1258, is whole approved. Exercise14.6 remains partial, and original source51 answers(b)/(c) and question remain whole pending.',
   'Six false exact decimal equalities and general repeated/local/temporal multiplier clauses remain explicit gaps; the separate approved Source52 proposal is unapplied.',
   'No future25 temporal source, live owner installation, source correction, fresh aggregate or publication claim follows from this isolated candidate.']})
 print(json.dumps({'offer':ref(offer),'candidate':ref(candidate),'artifacts':len(artifacts),'counts':J(offer)['counts']}))
if __name__=='__main__':main()
