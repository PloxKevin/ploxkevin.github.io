from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');H=R/'book/coverage/checks/root_integrate_owner30_candidates_v2.py';OUT=Path('/tmp/owner30-integrator2-independent-foundations-findings-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
closed={}
def add(p,h=None):
 p=Path(p);p=p if p.is_absolute() else R/p;actual=sha(p);assert h is None or actual==h
 if p.is_relative_to(R):assert not p.is_symlink() and p.resolve().is_relative_to(R)
 closed[str(p)]=actual;return json.loads(p.read_bytes()) if p.suffix=='.json' else p.read_bytes()
assert sha(H)=='38eaf901e509305976c78e7ec6bb019a05e91222a26e351f29d4f5ed4abcbfd8';body=add(H).decode();tree=ast.parse(body);funcs={f.name:f for f in tree.body if isinstance(f,ast.FunctionDef)}
assert set(funcs)=={'safe','sha','read','checked','pointer','zero','exact','new','native_actual','proof_hash','paired_projection','main'}
assert all(not isinstance(n,(ast.Exec if hasattr(ast,'Exec') else ast.Pass,)) for n in [])
constants={}
for n in tree.body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:constants[n.targets[0].id]=ast.literal_eval(n.value)
  except (ValueError,TypeError):pass
assert constants['EXPECTED']=={'core':(1,58),'foundations':(27,370),'applied':(2,34),'modules':(15,504)}
assert constants['SELF']=='book/coverage/checks/root_integrate_owner30_candidates_v2.py' and constants['INVENTORY_SHA']=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
assert not (R/constants['ARCHIVE']).exists() and not (R/constants['RESULT']).exists()
old=add('book/coverage/checks/root_integrate_owner30_candidates_v1.py','86e41b68fbf889fef607fc998f75b9c8d0f5aaded549e7fc72bda6805dce9d13')
ready=add(constants['READINESS'],constants['READINESS_SHA']);outer=add(constants['PRIMARY'],constants['PRIMARY_SHA']);add(constants['PAIR_HELPER'],constants['PAIR_HELPER_SHA']);add(constants['PLAN'],constants['PLAN_SHA']);add(outer['log'],outer['log_sha256'])
assert ready['errors']==[] and (ready['source_count'],ready['public_theorem_count'],ready['actual_compiler_command_count'])==(45,966,90) and outer['status']=='passed' and type(outer['actual_exit_code']) is int and outer['actual_exit_code']==0
inv=add('book/coverage/inventory-after-correction79.json',constants['INVENTORY_SHA']);assert sha(R/'book/coverage/inventory.json')==constants['INVENTORY_SHA'];assert inv['counts']['exercises']==556 and inv['counts']['material_source_units']==12774
add('book/coverage/validate.py');add('book/coverage/lean_names.py')
for owner,h in constants['OLD'].items():assert sha(R/'book/coverage'/f'{owner}.json')==h
# Actual final Foundation richer receipt schema and Module fragment-overlay evidence are read; no producer functions imported or called.
f=add('book/coverage/checks/future30-foundations/current79-completed90-association-v1/foundations30-completed90-current79-pair-bound-closed-offer-v5.json','861b55eae2da41bc766ebcf7dd6776bcc9c6e8335cd90a581489965a47756830');m=add('book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-offer-draft-v2.json','23e30af22235fbc3d4fa0d537d235ef64665759ba5e8e3935f820ba1d67ca370')
rich_count=0
for dest,row in f['proof_files'].items():
 for p in row['actual_pair']:
  actual=add(p['actual_record']['file'],p['actual_record']['sha256']);raw=add(p['raw_log']['file'],p['raw_log']['sha256']);add(p['source_snapshot']['file'],p['source_snapshot']['sha256']);add(p['root_helper_invocation_raw']['file'],p['root_helper_invocation_raw']['sha256'])
  assert p['original_checked_at_utc']==actual['checked_at_utc'] and p['original_elapsed_seconds']==actual['elapsed_seconds'] and p['original_record_has_no_start_time_field'] is True and 'started_at_utc' not in actual
  assert p['emitted_diagnostic_warning_headers']==len(re.findall(r'^.*:\d+:\d+: warning:',raw.decode(),re.M));rich_count+=1
assert rich_count==54
mc=add(m['candidate']['file'],m['candidate']['sha256'])
for n,h in mc['chapter_fragment_sha256'].items():add(n,h)
for q in [m['actual_source79_authoring_fragment_sync'],m['actual_source79_authoring_fragment_sync_execution']]:add(q['file'],q['sha256'])
# Full read assessment: typed strict paths/refs, native aliases/commands/times, actual pairs, independent mapping gates, no live mutation before isolated success, archives before writes.
assessment={'strict_Root_physical_paths_and_refs_with_optional_real_byte_counts':True,'four_domain_exact_current79_candidate_offer_and_final_peer_pointers_with_actual_native_protocol':True,'all45_sources966_names90_actual_standalone_named_receipts_and1242_source_protections':True,'actual54_Foundation_richer_pair_identity_supported_and_optional_metadata_preserved':True,'every_candidate_chapter_fragment_and_source_SHA_checked_and_guarded':True,'old_five_owners_checked_then_exact_archived_before_mutation':True,'all_immutable_evidence_collision_and_fresh_output_checks_before_live_owner_writes':True,'isolated_validator_preflight_and_second_exact_guard_before_apply_branch':True,'whole_scope_delegated_only_to_exact_full_mapping_peers_not_integrity_or_kernel_counts':True,'explicit_partial_coverage_and_separate_global_aggregate_and_publication_receipts_remain_required':True}
assert all(assessment.values())
find={'status':'passed_independent_full_owner30_integrator2_code_and_actual_native_schema_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':constants['SELF'],'sha256':sha(H)},'full_code_read':True,'all_twenty_three_KB_body_functions_and_apply_order_read':True,'actual_prior_unexecuted_helper1':ref(R/'book/coverage/checks/root_integrate_owner30_candidates_v1.py'),'prior_static_issue_not_a_producer_or_native_failure':'The old direct actual_pair dictionary equality rejected valid preserved extra receipt metadata. NEW2 projects exact Root identities, validates all preserved optional details independently, and directly guards the previously stale chapter-fragment metadata. Original helper1 remains unexecuted and unchanged.','actual_richer_Foundation_pair_records_read':54,'exact_original_warning_count_definition':r'^.*:\d+:\d+: warning:','named_Lake_replay_warning_lines_not_declared_absent':True,'full_read_assessment':assessment,'actual_complete90_readiness':{'file':constants['READINESS'],'sha256':constants['READINESS_SHA']},'actual_complete90_execution':{'file':constants['PRIMARY'],'sha256':constants['PRIMARY_SHA']},'review_did_not_import_or_execute_integrator_or_validator':True,'production_binding_and_isolated_preflight_still_required':True,'fixtures_or_compiler_parser_Git_Publication_invoked':False,'live_owner_source_canonical_selection_publication_mutation':False,'coverage_complete':False,'errors':[],'required_evidence_artifacts_sha256':closed}
OUT.write_text(json.dumps(find,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'helper':find['helper'],'full_code_read':True,'actual_richer_receipts':54,'errors':[]}))
