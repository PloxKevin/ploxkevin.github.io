from pathlib import Path
import ast,hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/root31-canonical-and-Euler6-independent-foundations31-v1')
assert not OUT.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 return p
def read(p):return json.loads(path(p).read_bytes())
context=read('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
assert context['status']=='actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only'
audit=read(checked(context['actual_audit']));assert audit['status']=='passed' and audit['proof_file_count']==1242
held={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}
assert len(context['owners_sha256'])==5 and len(context['held_current_source_sha256'])==31
assert all(held[n]==h for n,h in audit['proof_sha256'].items())
helper=path('book/coverage/checks/run_root31_reviewed_canonical_pairs_v1.py')
assert sha(helper)=='72f545650bc5d4b0040935109676d10bf006819dc655288d14c5d1d72d76e224'
source=helper.read_text();ast.parse(source)
old=path('book/coverage/checks/run_root30_reviewed_canonical_pairs_v2.py').read_text();ast.parse(old)
assert source==old.replace('plan30_only','plan31_only').replace('future30-core','future31-core').replace(
 "current_source79_with_unchanged_historical_source65_owner29_for_tmp_trials_only",
 "actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only").replace(
 'aggregate_source79_verification_claimed','aggregate_source81_verification_claimed').replace(
 "audit['proof_file_count']==1197","audit['proof_file_count']==1242").replace(
 "**context['held_current_source_sha256']}","**context['held_current_source_sha256'],**context['owners_sha256']}").replace(
 'root30_canonical_names','root31_canonical_names').replace('reviewed30_canonical','reviewed31_canonical').replace(
 'actual-reviewed30-canonical','actual-reviewed31-canonical')
for name,digest in [('book/coverage/check_core_standalone.py','124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a'),('book/coverage/check_core_named_build.py','605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069')]:
 assert sha(name)==digest;ast.parse(path(name).read_text())
assert source.index('guard()\n    if not args.apply:')<source.index('aliases={};snapshots={}')
assert 'source-snapshots' in source and 'original-closed-bytes' in source
assert "new(dest,source.read_bytes())" in source
assert "['lake','env','lean','SafeLearning/'+name+'.lean']" in source
assert "['lake','build','SafeLearning.'+name]" in source
assert "assert len(pairs)==2*len(rows)" in source
assert 'if result.returncode:raise SystemExit(result.returncode)' in source
code={'status':'passed_independent_full_root31_canonical_runner_code_and_actual81_schema_review','errors':[],
 'full_code_read':True,'reviewed_helper':ref(helper),'full_standalone_and_named_helpers_read':True,
 'exact_old30_to_new31_code_delta_verified':True,'current81_context_and_historical_source79_owner30_1242_audit_domain_verified':True,
 'all_prewrite_source_declaration_name_collision_oracle_trial_snapshot_log_peer_and_output_collision_gates_read':True,
 'read_only_default_and_explicit_apply_with_real_two_commands_per_source_read':True,
 'every_actual_command_cwd_source_snapshot_rawlog_native_identity_and_real_failure_preservation_read':True,
 'bounded_leaf_archiving_no_old_snapshot_or_lake_tree_copy':True,
 'producer_or_helpers_imported_or_executed_by_reviewer':False,
 'independent_actual_plan_or_future_success_or_coverage_claimed':False,'coverage_complete':False,
 'direct_evidence':[ref(helper),ref('book/coverage/checks/run_root30_reviewed_canonical_pairs_v2.py'),ref('book/coverage/check_core_standalone.py'),ref('book/coverage/check_core_named_build.py'),ref('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json'),context['actual_audit']]}
requestp=path('/tmp/root-filippov-euler24-full-increment-independent-review-request31-v2.json')
assert sha(requestp)=='35f884fafd2532f94ae9ee3f1df1059ca77bbd6e9570511704485adcfde29674'
request=read(requestp);sourcep=checked(request['source']);actual=read(checked(request['actual_native']))
assert actual['actual_exit_code']==actual['actual_runner_exit_code']==0 and actual['protection_errors']==[]
assert actual['actual_command']==['lake','env','lean',str(sourcep)] and actual['actual_workdir']==str(ROOT/'verification/lean')
assert actual['source_sha256_before']==actual['source_sha256_after']==sha(sourcep)
assert checked(request['actual_source_snapshot']).read_bytes()==sourcep.read_bytes()
raw=checked(request['actual_raw_log']);assert sha(raw)==actual['raw_log_sha256']
warningcount=len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M));assert warningcount==6
priorp=checked(request['prior_entire18_source']);assert sourcep.read_bytes().startswith(priorp.read_bytes())
priorpeer=read(checked(request['prior_full18_closed_peer']));assert priorpeer['status'].startswith('passed_') and priorpeer['errors']==[]
draft1=checked(request['original_draft1']);assert draft1.read_bytes().replace(b'noncomputable def chosenVelocity',b'def chosenVelocity').replace(b'noncomputable def eulerNodes',b'def eulerNodes')==sourcep.read_bytes()
oldtrial=read(checked(request['original_trial1']));assert oldtrial['actual_exit_code']==0
assert sha(oldtrial['raw_log'])==oldtrial['raw_log_sha256']
spec=importlib.util.spec_from_file_location('read_only_existing_names',ROOT/'book/coverage/lean_names.py')
names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
decls=names.declarations(sourcep.read_text());assert decls==request['all_public_declarations'] and len(decls)==30
assert sum(d['kind'] in ['theorem','lemma'] for d in decls)==24
assert len(request['new_public_declarations'])==8 and request['new_theorem_lemma_count']==6
primary=[]
for name in ['verification/lean/SafeLearning/CompleteBarrierFilippovHalfspaces.lean','verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean','verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/MulAction.lean','verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean']:
 p=path(name);p.read_text();primary.append(ref(p))
math={'status':'passed_independent_full_Euler24_exact18_prefix_and_six_actual_discrete_Euler_components_review','errors':[],
 'request':ref(requestp),'source':request['source'],'actual_supporting_native':request['actual_native'],
 'all24_proof_bodies_and_six_definitions_read':True,'exact_prior18_prefix_and_original_peer_body_time_retained':True,
 'prior18_full_component_decisions_reused_without_scope_promotion':True,
 'new_six_full_bodies_and_two_actual_choice_recursion_definitions_read':True,
 'new_component_decisions':[
  {'declarations':[request['new_public_declarations'][0]['name'],request['new_public_declarations'][1]['name']], 'approved':True,'remaining_gaps':[], 'reason':'Classical choice is taken from previously proved actual nonempty essential-convexified velocities under ProperSpace, open-positive measure and the actual global bound. Choice specification gives genuine membership, with no solution or velocity-membership premise.'},
  {'declarations':[request['new_public_declarations'][2]['name']], 'approved':True,'remaining_gaps':[], 'reason':'The old actual norm bound is applied to that proved membership; no desired bound is assumed for the selector.'},
  {'declarations':[r['name'] for r in request['new_public_declarations'][3:6]], 'approved':True,'remaining_gaps':[], 'reason':'The actual natural recursion starts at x0 and adds h times the chosen actual velocity at the current node. Its exact increment follows from the recursion and additive cancellation, also for h=0.'},
  {'declarations':[request['new_public_declarations'][6]['name']], 'approved':True,'remaining_gaps':[], 'reason':'For h>=0, true norm_smul and the selector norm bound derive every one-step norm bound hM. Nonnegativity of M follows already from the global field bound at x0; no extra desired conclusion is a premise.'},
  {'declarations':[request['new_public_declarations'][7]['name']], 'approved':True,'remaining_gaps':[], 'reason':'Actual induction splits the displacement into the old displacement and one increment, uses the true norm triangle inequality and the one-step result, and normalizes the successor coefficient to (n+1)hM.'}],
 'all_six_new_components_approved':True,'new_component_missing_clauses':[],
 'measurability_or_continuity_of_arbitrary_selector_claimed':False,
 'Euler_polygon_or_limit_solution_derivative_or_integral_curve_existence_claimed':False,
 'whole_Exercise16_or_generic_Filippov_existence_approved':False,
 'actual24_theorems_30_public_declarations_and_six_emitted_warning_headers_preserved':True,
 'original_actual_trials_bodies_times_and_request1_retained':True,'compiler_or_current_owner_or_canonical_source_mutation_by_reviewer':False,'coverage_complete':False,
 'additional_complete_used_primary_files':primary,
 'direct_evidence':[ref(requestp),*[{**r} for k,r in request.items() if isinstance(r,dict) and {'file','sha256'}<=r.keys()],ref(oldtrial['raw_log']),ref(oldtrial['source_snapshot']),*primary]}
OUT.mkdir()
for name,d in [('canonical-code-peer-v1.json',code),('Euler24-six-increment-math-peer-v1.json',math)]:
 (OUT/name).write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'status':'passed','errors':[],'code_helper':code['reviewed_helper'],'six_Euler_components_approved':True,'actual_supporting_source':request['source'],'producer_or_compiler_invoked':False}))
