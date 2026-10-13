from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
Q=Path('/tmp/modules-NN143-genuine-numerical-precision-data-only-proposal-v1/NN14_3-entire-genuine-certified-precision-data-only-proposal-v1.json')
QH='59d02ba64d4763102d6eb91262783479ae4761149eff6748f753ab83a4d3169e'
N=R/'book/coverage/checks/future32-core/NN143-four-line-narrow-independent-foundations-v1/modules-NN143-four-line-full-literal-support-fresh-full29-parser-narrow-independent-foundations32-closed-peer-v1.json'
NH='7b3116733c036f6d46458cf0f75399925050ed6d5c3d62e345ee317621ae050e'
C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
O=Path('/tmp/modules-NN143-full-composition-static-bootstrap32-findings-v2.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def checked(r):
 p=path(r['file']);assert p.is_file()and sha(p)==r['sha256'],r
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 refs[str(p)]=r['sha256'];return p
assert not O.exists()and sha(Q)==QH and sha(N)==NH and sha(C)==CH
ctx=json.loads(C.read_bytes());old={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
I=R/'reports/full-coverage/owner32-recovery-integration-v1.json';IH='645c6a89d8a9b20022f95d7d64c4f1bb5cc8b836f690bc2f6162bbab627b2418'
A=R/'reports/full-coverage/install32-recovery-execution-v1.json';AH='e5580e0b1f5a2f827caa538e7801089d048cb2cbf905dd1ed931ac196036f5ae'
assert sha(I)==IH and sha(A)==AH;install=json.loads(I.read_bytes());an=json.loads(A.read_bytes());assert install['applied']is True and an['status']=='passed'and an['actual_exit_code']==0
assert an['actual_command']==['python3','book/coverage/checks/recovery32_install.py']and an['actual_workdir']==str(R)and an['helper_sha256_before']==an['helper_sha256_after']and sha(path(an['log']))==an['log_sha256']
changes={r['destination']:r for r in install['exact_replacements']};assert set(changes)=={'book/coverage/core.json','book/coverage/applied.json','book/coverage/foundations.json'}
observed={n:r['candidate']['sha256']for n,r in changes.items()}
for n,row in changes.items():assert old[n]==row['before']['sha256']==row['preserved_original']['sha256'];checked(row['preserved_original']);assert sha(path(n))==observed[n]and sha(checked(row['candidate']))==observed[n]
# This is a scoped static bootstrap input guard, not a released compiler/aggregate context.
def guard():
 assert sha(C)==CH and sha(I)==IH and sha(A)==AH
 for n,h in old.items():assert sha(path(n))==(observed[n]if n in observed else h),n
guard();refs.update({str(p):sha(p)for p in[Q,N,C,I,A,path(an['log'])]})
q=json.loads(Q.read_bytes());n=json.loads(N.read_bytes());assert n['errors']==[]and n['proposal']['sha256']==QH
before=checked(q['entire_current_source']).read_bytes();after=checked(q['entire_data_only_candidate']).read_bytes()
assert before==(R/'SafeLearning/nn-in-the-loop.html').read_bytes()and sha(checked(q['exact_current_installed31_raw_owner']))==old['book/coverage/modules.json']
assert n['current_Source81_NN']['sha256']==hashlib.sha256(before).hexdigest()and n['exact_prospective_candidate']['sha256']==hashlib.sha256(after).hexdigest()
# Read exact full requested clauses and the complete unchanged 14.4 context.
assert q['entire_current14_3_raw_HTML_block_lines977_995']==''.join(before.decode().splitlines(keepends=True)[976:995])
assert q['entire_proposed14_3_raw_HTML_block_same_lines977_995']==''.join(after.decode().splitlines(keepends=True)[976:995])
assert ''.join(before.decode().splitlines(keepends=True)[995:1012])==''.join(after.decode().splitlines(keepends=True)[995:1012])
inv=json.loads(checked(q['exact_current_Source81_inventory']).read_bytes());assert len(inv['exercises'])==556 and len(inv['material_source_units'])==12774
literal_pairs=n['entire_current_and_prospective_changed_inventory_literals'];assert set(literal_pairs)=={'nn-in-the-loop.html::exercise-17','nn-in-the-loop.html::node-1210','nn-in-the-loop.html::node-1217','nn-in-the-loop.html::node-1218','nn-in-the-loop.html::node-1220'}
for k,pair in literal_pairs.items():
 kind='exercises'if 'exercise-'in k else'material_source_units';assert pair['entire_current']==next(x for x in inv[kind]if x['key']==k)
 assert pair['entire_proposed']['source_sha256']==hashlib.sha256(after).hexdigest()
assert n['fresh_independent_system_TMP_BOTH_ROOT_and_OUT_full29_parser']['both_ROOT_and_OUT_strictly_TMP']is True
# Verify strict RFC6902 substitutions/inverse using actual full documents.
patch=json.loads(checked(q['exact_typed_forward_and_full_byte_inverse']).read_bytes());sys.path.insert(0,str(R/'book/coverage'));import lean_names
from copy import deepcopy
def pointer(root,ptr):
 parts=[s.replace('~1','/').replace('~0','~')for s in ptr.split('/')[1:]];node=root
 for part in parts[:-1]:node=node[int(part)]if isinstance(node,list)else node[part]
 return node,(int(parts[-1])if isinstance(node,list)else parts[-1])
def apply(doc,ops):
 doc=deepcopy(doc)
 for op in ops:
  parent,key=pointer(doc,op['path'])
  if op['op']=='test':assert parent[key]==op['value']
  elif op['op']=='replace':parent[key]=op['value']
  elif op['op']=='add':
   if isinstance(parent,list):parent.insert(key,op['value'])
   else:parent[key]=op['value']
  elif op['op']=='remove':del parent[key]
  else:raise AssertionError(op['op'])
 return doc
inputdoc=json.loads(checked(patch['input_document']).read_bytes());candidatedoc=json.loads(checked(patch['candidate_document']).read_bytes())
assert apply(inputdoc,patch['forward_jsonpatch'])==candidatedoc and apply(candidatedoc,patch['inverse_jsonpatch'])==inputdoc
assert ''.join(inputdoc['source_utf8_lines']).encode()==before and ''.join(candidatedoc['source_utf8_lines']).encode()==after
assert patch['forward_recovers_entire_candidate_UTF8_bytes']and patch['inverse_recovers_entire_original_UTF8_bytes']
# All62 prior bodies were independently reviewed in six exact authorities. No prior pending verdict is rewritten.
covered=[];authorities=[];prefixes=[]
for entry in n['all_six_existing_component_peers_and_body_times_unchanged']:
 pp=checked(entry['original_closed_peer']);p=json.loads(pp.read_bytes());assert p['errors']==[]
 for file,h in p['required_evidence_artifacts_sha256'].items():assert sha(path(file))==h
 assessments=next(v for k,v in p.items()if 'body_assessments'in k);assert all(x['entire_body_read']and x['exact_component_approved']for x in assessments)
 source_ref=next(v for k,v in p.items()if k.startswith('entire_final')and isinstance(v,dict));ps=checked(source_ref).read_bytes();prefixes.append(ps)
 for item in assessments:assert item['theorem']not in covered;covered.append(item['theorem'])
 authorities.append({'original_peer':ref(pp),'original_status':p['status'],'all_exact_new_component_bodies_approved':True,'covered_public_theorems':[x['theorem']for x in assessments],'original_pending_whole_findings_and_native_body_times_preserved':True})
assert len(covered)==62
origin=n['additional_origin3_complete_component_bodies_read_and_approved'];sourcep=checked(origin['source']);source=sourcep.read_text()
assert all(source.encode().startswith(b)for b in prefixes)and origin['exact_passed62_full_byte_prefix']is True
names=lean_names.declarations(source);th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==65 and len(names)==95
newth=[d['name']for d in origin['new_public_names']if d['kind']in ['theorem','lemma']];assert covered+newth==th and len(newth)==3
assert origin['generic_and_actual_HasDerivAt_no_desired_derivative_premise']and origin['actual_deriv_based_stable_tangent_orbit_geometric_decay_is_derived_not_nonlinear_global_claim']
assert not re.search(r'\b(?:sorry|axiom|admit|unsafe|native_decide)\b',lean_names.without_comments(source))
# Direct complete Origin3/private tangent proof reading plus its genuine source and standard-axiom natives.
for rn in [origin['actual_source_native'],origin['actual_all3_standard_axioms_native']]:
 p=checked(rn);d=json.loads(p.read_bytes());assert d['actual_exit_code']==d['actual_runner_exit_code']==0 and d['protection_errors']==[]and d['source_unchanged']
 sp=checked({'file':d['source'],'sha256':d['source_sha256_before']});ss=checked({'file':d['source_snapshot'],'sha256':d['source_snapshot_sha256']});lp=checked({'file':d['raw_log'],'sha256':d['raw_log_sha256']})
 assert sp.read_bytes()==ss.read_bytes()and d['source_sha256_before']==d['source_sha256_after']and d['actual_source81_installed_owner31_context']['sha256']==CH
 assert d['actual_command']==['lake','env','lean',str(sp)]and d['actual_workdir']==str(R/'verification/lean')
 if rn==origin['actual_all3_standard_axioms_native']:
  assert sp.read_text().startswith(source)and sp.read_text()[len(source):].count('#print axioms')==3
  axioms={name:[a.strip()for a in atoms.replace('\n',' ').split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",lp.read_text(),re.S)}
  assert list(axioms)==newth and all(set(x)<={'propext','Classical.choice','Quot.sound'}for x in axioms.values())
# Origin first true failure is preserved, never rewritten as a current bootstrap failure.
for pp in [Path('/tmp/modules-NNScalarOriginLinearization65-source81-installed-owner31-trial1.json'),Path('/tmp/CompleteModulesNNScalarOriginLinearization31-draft-v1.lean')]:refs[str(pp)]=sha(pp)
first=json.loads(Path('/tmp/modules-NNScalarOriginLinearization65-source81-installed-owner31-trial1.json').read_bytes());assert first['actual_exit_code']==1 and first['protection_errors']==[];refs[first['raw_log']]=first['raw_log_sha256']
SIM=R/'book/coverage/checks/future32-core/NN143-actual-scalar-trajectories-independent-modules-v1/modules-NN143-actual-two-source-initial-state-finite-scalar-trajectory-check-closed-receipt-v1.json';SH='c59570c24bbbd5ee028601cddf2cb8f9694d996d12c256d10a3d3323d3b0699e';assert sha(SIM)==SH;sim=json.loads(SIM.read_bytes());assert sim['errors']==[]
for f,h in sim['required_evidence_artifacts_sha256'].items():assert sha(path(f))==h
refs[str(SIM)]=SH
# Precise clause-to-genuine-theorem correspondence. Stored names must all be present, none are conclusion premises.
short=lambda name:'SafeLearning.CompleteModulesNNWalkthroughLocal31.'+name
clauses={
 'part_a_actual_composition_and_Step5_feasibility':['actual_source_scalar_plant_and_controller_composition','actual_source_LMI_is_the_energy_difference_plus_the_origin_sector_QC','actual_global_walkthrough_optimizer_matrix_is_negative_definite'],
 'part_a_unique_determinant_optimizer_exact_matrix_official_spectrum_and_rounded_cells':['actual_global_walkthrough_optimizer_matrix_and_determinant','actual_global_determinant_has_the_unique_exact_maximizing_multiplier','actual_global_walkthrough_has_the_complete_exact_official_spectrum','actual_global_optimizer_spectrum_has_the_true_six_decimal_rounding'],
 'part_a_full_positive_storage_and_unit_storage_admissibility_and_inner_interval':['actual_all_positive_storage_walkthrough_certificates_have_the_exact_multiplier_interval','actual_all_unit_storage_admissible_multipliers_are_exactly_between_the_roots','actual_displayed_global_inner_interval_is_sound_but_does_not_list_all_multipliers','actual_global_full_admissible_endpoints_have_the_true_six_decimal_rounding'],
 'part_a_positive_scaling_and_all_initial_true_global_exponential_loop':['actual_positive_rescaling_retains_the_source_LMI_identity','actual_every_global_physical_trajectory_has_an_all_time_geometric_bound','actual_every_global_physical_initial_state_converges_to_zero'],
 'part_b_global_infeasibility_and_genuine_local_origin_linearization':['actual_unstable_global_walkthrough_has_no_negative_definite_certificate','actual_scalar_plant_has_the_exact_origin_linearization','actual_physical_walkthrough_has_the_exact_stable_origin_derivative','actual_every_true_linearized_physical_initial_state_has_geometric_decay_and_converges'],
 'part_b_actual_root_bracket_open_basin_boundaries_and_exact_two_examples':['actual_unique_positive_critical_radius_exists_and_has_the_exact_rational_bracket','actual_physical_walkthrough_has_the_exact_open_basin_and_the_two_source_initial_states','actual_scalar_y_fixed_points_are_exactly_zero_and_the_two_critical_boundaries','actual_positive_exterior_y_has_geometric_escape_to_positive_infinity'],
 'part_b_derived_every_subcritical_strict_LMI_containment_and_exact_open_certificate_union':['actual_every_strictly_subcritical_radius_has_an_explicit_literal_LMI_and_containment_certificate','actual_literal_strict_certificate_radii_are_exactly_the_positive_radii_below_root','actual_union_of_literal_strict_certified_ellipsoids_equals_the_open_basin_and_excludes_root_box'],
 'part_c_exact_sector_transform_original_coordinate_rescaling_discriminant_and_optimizer':['actual_tanh_three_sector_has_the_required_ten_decimal_enclosure','actual_local_loop_transformation_optimizer_and_storage_rescaling_are_exact','actual_local_optimizer_discriminant_has_its_exact_positive_factorization','actual_local_determinant_has_the_unique_exact_maximizing_multiplier','actual_local_sector_transformed_coefficients_and_prime_multiplier_have_true_display_precision'],
 'part_c_actual_optimized_matrix_official_full_spectrum_and_all_display_rounding':['actual_optimized_local_unit_storage_matrix_has_the_true_six_decimal_entries','actual_local_optimized_unit_storage_has_the_complete_exact_official_spectrum','actual_local_optimized_official_spectrum_has_the_true_six_decimal_rounding','actual_local_optimized_multipliers_have_the_true_display_precision'],
 'part_c_full_admissible_interval_false_upper_multiplier_and_exact_box3_certificate':['actual_all_positive_storage_local_walkthrough_certificates_have_the_exact_multiplier_interval','actual_local_full_admissible_endpoints_have_the_true_six_decimal_rounding','actual_printed_upper_interval_contains_an_infeasible_multiplier','actual_exact_half_multiplier_is_strictly_feasible','actual_rescaled_box_three_multiplier_is_strictly_feasible','actual_box_three_containment_matrix_is_semidefinite_with_zero_determinant','actual_rescaled_sublevel_is_exactly_the_box_three_state_interval','actual_local_physical_loop_has_all_time_invariance_and_origin_decay']}
clauses={k:[short(x)for x in v]for k,v in clauses.items()};assert all(x in th for v in clauses.values()for x in v)
guard()
f={'status':'passed_independent_full_prospective_Exercise14_3_three_part_mathematical_composition','errors':[],'reviewer':'modules_finish28','full_current_and_prospective_Exercise14_3_three_parts_and_walkthrough_context_read':True,'all65_distinct_genuine_public_theorems_independently_covered_by_prior_six_complete_component_authorities_and_new_Origin3_complete_body_authority':True,'full_prior62_bodies_reused_by_exact_byte_prefix_and_prior_full_independent_math_decisions_not_relabelled_as_fresh_first_reads':True,'all3_new_Origin_complete_bodies_private_derivative_and_tangent_limit_used_provider_bodies_directly_read':True,'proposal':ref(Q),'exact_current_Source81_page':q['entire_current_source'],'exact_prospective_page':q['entire_data_only_candidate'],'strict_four_line_forward_and_entire_original_UTF8_inverse':q['exact_typed_forward_and_full_byte_inverse'],'independent_four_line_full_literal_parser_and_Origin3_component_authority':ref(N),'prior_six_original_component_authorities':authorities,'entire65_source':ref(sourcep),'all95_public_names':names,'public_theorem_count':65,'definition_count':30,'clause_to_genuine_public_theorem_correspondence':clauses,'entire_current_and_prospective_changed_inventory_literals':literal_pairs,'whole_exercise_decision':{'key':'nn-in-the-loop.html::exercise-17','entire_current_literal_read':True,'current_whole_semantic_approved':False,'current_missing_requirements':['Replace exact rounded spectral and transformed numerical equalities with certified exact expressions and approximation signs.','Use the full exact admissible multiplier endpoints and exclude the infeasible claimed upper multiplier.','Describe the supremal open union of strict local certificates; the critical boundary closed box is unattainable.'],'entire_prospective_literal_read':True,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact59d_four_line_application_and_current_literal_identity':True},'whole_four_changed_material_unit_decisions':{k:{'current_whole_semantic_approved':False,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact_application':True}for k in literal_pairs if '::node-'in k},'all_three_requested_part_requirements_satisfied_for_the_exact_prospective_exercise':{'part_a':True,'part_b':True,'part_c':True},'actual_finite_scalar_simulation_receipt':ref(SIM),'simulation_scope':'The current-source-extracted scalar dynamics and two exact initial constants were executed for200 floating steps, preserving all201 finite states. This is a finite observational check; the exact all-time convergence/divergence conclusions are separately derived by the genuine Basin10 proofs. No float-error bound or infinity theorem is attributed to simulation.','new_Origin3_standard_axioms':axioms,'original_all_component_scope_false_verdicts_and_genuine_failure_pass_axiom_body_times_remain_immutable':True,'actual_scope_domains':{'global':'Scalar a=.8,b1,W0=2,W1=-.6; all real initial states and positive scaling of genuine strict LMI pairs.','local':'Scalar a=1.3 with actual tanh loop. Every positive strictly subcritical sector box has explicit strict LMI+containment; the union is the exact open basin, excluding nonzero boundary equilibria.','box3':'Exact origin secant alpha=tanh3/3 and actual p1 local matrix. Full strict admissibility interval plus rescaled p4/9 certificate and actual containment equality.','linearization':'Derivative1/10 at0 and genuine derived tangent iteration only; no nonlinear global conclusion is inferred from the stable pole.'},'whole14_4_default2D_JS_or_generic_walkthrough_neighbor_promoted':False,'current_source_owner_canonical_selection_or_publication_mutation':False,'reader_invoked_compiler_or_parser':False,'source_number_reserved_or_applied':False,'coverage_complete':False,'bootstrap_input_guard':{'kind':'dedicated_read_only_static_input_guard_only_not_released_compiler_or_aggregate_context','historical_released0396_context':ref(C),'all_original1248_selected_Source81_site31_and_unchanged_Module31_inputs_held':True,'three_current_owner32_hashes_observed':observed,'exact_old31_owner_aliases_and_authentic_recovery32_install_record_checked_only_as_change_provenance':True,'recovery32_install_record':ref(I),'recovery32_actual_native':ref(A),'current_recovery32_math_mapping_or_audit_redecision':False,'no_new_context_release_or_old0396_current_status_claimed':True,'protection_errors':[]},'input_and_original_artifacts_sha256':refs}
failed=Path('/tmp/modules-NN143-full-composition-static-bootstrap32-actual-v1.json');fn=json.loads(failed.read_bytes());assert fn['actual_exit_code']==1
f['preserved_genuine_reader1_typed_document_reference_schema_failure']={'native':ref(failed),'raw_log':ref(path(fn['log'])),'helper':ref(Path('/tmp/review-modules-NN143-full-composition-static-bootstrap32-v1.py')),'wrapper':ref(Path('/tmp/run-modules-NN143-full-composition-static-bootstrap32-v1.py')),'original_body_times':{k:fn[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'only_repair':'Load and hash-check the typed input/candidate JSON document refs before applying strict patches.'}
with O.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'public_theorem_count':65,'all95_names':len(names),'current_whole':False,'prospective_whole':True,'distinct_changed_material_wholes':4,'errors':[]}))
