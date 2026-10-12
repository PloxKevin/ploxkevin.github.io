from pathlib import Path
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules-integral-tracking35-full-current-prospective31-v1')
assert not B.exists();B.mkdir()
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={};physical={}
def cp(p):
 p=Path(p);h=sha(p);q=B/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==h;physical[str(q)]=h;r={'file':str(q),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;return r
proof=Path('/tmp/CompleteModulesIntegralTrackingWhole30-draft-v15.lean');t=proof.read_text();decl=lean_names.declarations(t)
pub=[x['name']for x in decl if x['kind']in ['theorem','lemma']];defs=[x['name']for x in decl if x['kind']=='def']
assert len(pub)==35 and len(defs)==13 and sha(proof)=='384484a7fb9d48fcb00c76a52b004ae3bbf3697b4acc71b14c9f7c0f0f17fc9a'
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(t))
hist=[]
for i in range(1,13):
 p=Path(f'/tmp/modules-integral-tracking-whole30-owner29-trial{i}.json')if i<3 else Path(f'/tmp/modules-integral-tracking-whole30-owner30-trial{i}.json')if i<8 else Path(f'/tmp/modules-integral-tracking-whole31-owner30-trial{i}.json')
 n=json.loads(p.read_bytes());assert n['actual_exit_code']==[1,1,1,1,0,1,0,1,1,1,1,0][i-1]and n['protection_errors']==[]and n['source_unchanged']
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(n['source'])
 assert sha(n['source_snapshot'])==n['source_snapshot_sha256']and sha(n['raw_log'])==n['raw_log_sha256']
 assert n['actual_command']==['lake','env','lean',n['source']]
 raw=Path(n['raw_log']).read_text()
 h={'trial_ordinal':i,'native':cp(p),'source':cp(n['source']),'snapshot':cp(n['source_snapshot']),'raw_log':cp(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'actual_emitted_warning_headers':len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M))}
 for k in ['original_actual_runner','actual_source79_final_css_owner30_context','actual_source65_owner29_context','actual_source64_installed28_context','actual_source60_owner28_context']:
  if isinstance(n.get(k),dict)and 'file'in n[k]and Path(n[k]['file']).is_file():assert sha(n[k]['file'])==n[k]['sha256'];cp(n[k]['file'])
 hist.append(h)
assert proof.read_bytes().startswith(Path('/tmp/CompleteModulesIntegralTrackingWhole30-draft-v9.lean').read_bytes())
uncompiled=[cp(Path(f'/tmp/CompleteModulesIntegralTrackingWhole30-draft-v{v}.lean'))for v in [3,5,11]]
invpath=R/'book/coverage/inventory-after-correction79.json';inv=json.loads(invpath.read_bytes())
ownpath=R/'book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-candidate-v1.json';owner=json.loads(ownpath.read_bytes())
exercise=next(e for e in inv['exercises']if e['key']=='nn-in-the-loop.html::exercise-19')
owned=next(e for e in owner['exercises']if e['inventory_key']==exercise['key']);assert owned['status']=='pending'
keys=['nn-in-the-loop.html::node-'+str(k)for k in [1240,1244,1247,1249]]
units=[u for u in inv['material_source_units']if u['key']in keys];assert len(units)==4
rows=[r for r in owner['material_claims']if set(r.get('source_unit_keys',[]))&set(keys)]
proposal=Path('/tmp/modules-integral-tracking-precision-unnumbered31-v1/modules-integral-tracking-three-precision-phrases-unnumbered-full29-proposal31-v1.json');p=json.loads(proposal.read_bytes())
assert p['fresh_changed_literal_keys']=={'exercises':[exercise['key']],'material_source_units':['nn-in-the-loop.html::node-1247']}
def resolve(r):
 z=Path(r['file']);return z if z.is_absolute()else R/z
page=resolve(p['source']).read_text();newpage=resolve(p['proposed_source']).read_text()
selected={}
for name in ['CompleteModulesTanhChords','CompleteModulesChords','CompleteModulesTheory','CompleteModulesLipSDP','Modules','BookApplications']:
 selected[name]=cp(R/'verification/lean/SafeLearning'/f'{name}.lean')
mathlib=R/'verification/lean/.lake/packages/mathlib/Mathlib';primary={}
files=['Topology/MetricSpace/Contracting.lean','Analysis/Calculus/Deriv/MeanValue.lean','Analysis/SpecificLimits/Basic.lean','Analysis/Complex/Exponential.lean','Analysis/Complex/Trigonometric.lean','Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean','Analysis/Real/Sqrt.lean','Analysis/Calculus/FDeriv/Prod.lean','Analysis/Calculus/Deriv/Comp.lean','Analysis/Calculus/FDeriv/Add.lean','Analysis/Calculus/FDeriv/Mul.lean','Analysis/Calculus/ContDiff/Operations.lean','Analysis/Calculus/ContDiff/Comp.lean','LinearAlgebra/Matrix/Charpoly/Eigs.lean','LinearAlgebra/Matrix/Charpoly/Coeff.lean','Analysis/Complex/Norm.lean','Order/Filter/AtTopBot/Basic.lean']
for f in files:primary[f]=cp(mathlib/f)
remote=Path('/tmp/modules-integral-tracking-primary31-v1/actual-primary-retrieval-v1.json');pr=json.loads(remote.read_bytes());assert pr['HTTP_status']==200 and pr['actual_text_exit_code']==0
assert sha(pr['PDF_file'])==pr['PDF_sha256']and sha(pr['text_file'])==pr['text_sha256']
primary_remote={'primary_URL':pr['primary_URL'],'actual_retrieval_receipt':cp(remote),'actual_pdftotext_log':cp(pr['actual_text_log']),'offline_PDF_path':pr['PDF_file'],'original_PDF_sha256':pr['PDF_sha256'],'offline_full_text_path':pr['text_file'],'original_full_text_sha256':pr['text_sha256'],'full_remote_originals_offline_TMP_only':True,'actually_read_bounded_scope':'Section2.1 integrator dynamics and nonsingular steady-state assumption; Section3.1 Theorem1 and full proof; Section3.2 Theorem3/full proof; Section3.3 Theorem4/full proof.','bounded_primary_factual_assessment':'The actual plant-integrator controller has zero steady offset at an equilibrium without network-weight constraints. Theorem1 covers all initial states and references under a common strict slope-QC LMI. Theorem3 covers one reference on its certified ellipsoid, and Theorem4 covers a joint initial-state/reference set. Their hypotheses and convergence scopes are distinguished; no general robust-plant theorem is inferred.'}
np=Path('/tmp/modules-integral-tracking-precision-unnumbered31-preparation-actual-v1.json');pn=json.loads(np.read_bytes());assert pn['actual_exit_code']==0 and pn['protection_errors']==[]
for f,h in pn['helper_sha256_before'].items():assert sha(f)==h==pn['helper_sha256_after'][f];cp(f)
cp(pn['raw_log']);cp('/tmp/run-modules-integral-tracking-precision-unnumbered31-preparation-v1.py')
for r in [p['source'],p['proposed_source'],p['before_inventory'],p['original_installed_owner30_candidate']]:cp(resolve(r))
d={'status':'prepared_TMP_only_integral_tracking35_full_current_and_three_precision_phrases_prospective_whole_review_request','author':'/root/modules_finish28','final_actual_passed_source':cp(proof),'full35_public_theorem_names':pub,'public_theorem_count':len(pub),'actual_definition_names':defs,'entire_passed26_v9_bytes_retained':True,'prior_passed26_source':cp('/tmp/CompleteModulesIntegralTrackingWhole30-draft-v9.lean'),'entire_current_exercise':exercise,'entire_current_owned_exercise_body':owned,'entire_current_material_literals':units,'entire_original_owned_material_rows':rows,'full_current_context_lines1008_1030':''.join(page.splitlines(keepends=True)[1007:1030]),'full_prospective_context_lines1008_1030':''.join(newpage.splitlines(keepends=True)[1007:1030]),'full_current_Section4_lines384_460':''.join(page.splitlines(keepends=True)[383:460]),'current_inventory':cp(invpath),'current_installed_owner30_immutable_candidate':cp(ownpath),'current_page_immutable_original':cp(resolve(p['source'])),'prospective_page':cp(resolve(p['proposed_source'])),'precision_proposal':cp(proposal),'precision_author_actual_preparation':cp(np),'entire_prospective_exercise_and_changed_material':p['entire_current_and_proposed_literal_records'],'narrow_independent_peer_pending':True,'complete_selected_sources':selected,'complete_used_primary_files':primary,'actual_primary_Pauli_attribution_scope':primary_remote,'all12_genuine_compiler_histories':hist,'uncompiled_drafts_exact_and_not_claimed_native':uncompiled,'exact_clause_correspondence':{'nominal_network':'actual_nominal_network_has_exact_equilibrium_feedforward','actual_scalar_wrong_limits_offsets':'actual_two_perturbed_scalar_trajectories_have_unique_wrong_limits_with_printed_offsets','structural_parameter_independent_zero_offset':'actual_integrator_zero_offset_is_independent_of_every_plant_and_network_parameter','true_equilibrium_exists_without_weight_constraints':'actual_general_augmented_equilibrium_exists_without_network_weight_constraints','actual_all_reference_augmented_convergence':'actual_integral_controller_tracks_every_reference_from_every_initial_state','global_quadratic_certificate':'actual_uniform_quadratic_certificate_gives_true_global_exponential_convergence','actual_matrix_derivative_association':'actual_nonlinear_augmented_loop_has_the_printed_Frechet_linearization','matrix_action':'actual_linearization_matrix_represents_the_true_derivative_action','true_complex_spectrum_and_attained_radii':'actual_both_linearized_spectral_radii_are_exact_and_have_the_printed_rounding','continuously_differentiable':'actual_augmented_closed_loop_is_continuously_differentiable','printed_simulation_targets_actual_all_initial_trajectories':'actual_simulated_reference_targets_and_integrator_states_follow_from_the_true_loop','true_converging_integral_recurrence_needs_no_steady_map_constraint':'actual_convergence_of_a_true_integral_loop_forces_exact_output_tracking'},'requested_review':{'all35_entire_public_private_bodies_definitions':'Full actual source, all six selected sources and used primary proof bodies. Actual no-oracle kernel statements and all12 history metadata must be retained.','individual_current_whole_units':['nn-in-the-loop.html::node-1240','nn-in-the-loop.html::node-1244','nn-in-the-loop.html::node-1249'],'current_whole_exercise_and1247':False,'current_remaining_gap':'Three unqualified rounded numerical equalities in current1247: xi−.833 and two spectral radii.632/.616. Preserve current whole=false.','prospective_entire_Exercise14_5_and1247':'Only after reading all claims and exact three-phrase current/prospective correspondence. Treat the primary Theorem1/3/4 attribution as a bounded source dependency, with actual new35 convergence/structural results separate. No surrounding Section4 generic theorem promotion.'},'all_original_byte_aliases':aliases,'all_physical_original_inputs_sha256':physical,'current_context':cp('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json'),'current_whole_approved_by_author':False,'canonical_owner_source_selection_publication_mutations':False,'coverage_complete':False}
# Context added above is part of the alias/physical dictionaries through their shared references.
O=B/'modules-integral-tracking35-full-current-prospective-Exercise14_5-four-literals-review-request31-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request_file':str(O),'sha256':sha(O),'bytes':O.stat().st_size,'public':len(pub),'physical_refs':len(physical)}))
