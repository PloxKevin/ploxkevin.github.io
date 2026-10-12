from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/basics12-full-scope-v1/foundations-Basics12-two-new-bodies-full-prospective916918-composition-independent-review-request32-v1.json';QH='5d56664b28c431c0080b6f10b42a43c686a8f4054602402b8339579cd778da5d';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-Basics12-independent-modules32-findings-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert p.is_file()and sha(p)==r['sha256'],r
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(C)==CH and sha(Q)==QH and not F.exists();ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH
 for n,h in g.items():assert sha(path(n))==h,n
 return []
guard();q=json.loads(Q.read_bytes());refs={Q.relative_to(R).as_posix():QH}
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str)and len(x['sha256'])==64:
   p=checked(x);refs[str(p)]=sha(p)
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(q)
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(path(n))==h;refs[n]=h
source=checked(q['final_genuine_passed_source']).read_text();sys.path.insert(0,str(R/'book/coverage'));import lean_names
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==12 and all(n['kind']=='theorem'for n in names)
assert [n['name']for n in names]==q['public_theorem_names']
old=json.loads(checked(q['exact_original10_full_request']).read_bytes());prefix=checked(old['final_actual_passed_source']).read_text();assert source.startswith(prefix)and source[len(prefix):].count('\ntheorem ')==2
oldpeer=json.loads(checked(q['original_full10_independent_component_peer']).read_bytes());assert oldpeer['status'].startswith('passed')and oldpeer['errors']==[]
assert checked(q['original_full10_independent_component_peer']).name=='foundations-Basics10-full-source-ten-exact-components-independent-modules32-closed-peer-v1.json'
masked=lean_names.without_comments(source);assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',masked)
for p in q['entire_three_selected_sources']:checked(p).read_text()
for p in q['additional_full_used_primary_sources'].values():checked(p).read_text()
proposal=json.loads(checked(q['exact_approved_four_phrase_unnumbered_proposal']).read_bytes());narrow=json.loads(checked(q['independent_full_literal_and_fresh29_narrow_peer']).read_bytes());assert narrow['status'].startswith('passed')and narrow['errors']==[]
assert q['exact_approved_four_phrase_unnumbered_proposal']['sha256']=='03acf20631de9effbada95d6e75c1f288282b821578ff4d66cdf144842a64f79'and q['independent_full_literal_and_fresh29_narrow_peer']['sha256']=='88ad49a7a575af03b410f0da0baa4b57af17129a9997f4dd7c765969ee3329fd'
assert q['entire_prospective_three_literals']==proposal['entire_current_and_proposed_literal_records']
assert checked(q['full_current_Basics_source']).read_bytes()==checked(proposal['source']).read_bytes()and checked(q['full_exact_prospective_Basics_source']).read_bytes()==checked(proposal['proposed_source']).read_bytes()
assert q['full_current_and_prospective_context']=={'current':proposal['full_current_context_lines985_1015'],'prospective':proposal['full_proposed_context_lines985_1015']}
for r in proposal['exact_replacements']:assert r['after']in checked(q['full_exact_prospective_Basics_source']).read_text()
# Authenticate the exact original old five records without migration of their historical context labels.
assert q['original_five_genuine_histories_body_times_warnings_contexts_unchanged']==old['actual_genuine_five_native_histories']
assert q['all_genuine_source_codes']==[1,1,1,1,0,0]
row=q['new_genuine_source12_trial6'];n=json.loads(checked(row['native']).read_bytes());log=checked(row['raw_log']).read_text();assert n['actual_exit_code']==0 and n['protection_errors']==[]and n['actual_runner_exit_code']==0
assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
assert checked(row['source']).read_bytes()==checked(row['source_snapshot']).read_bytes()==source.encode()
assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(checked(row['source']))and n['raw_log_sha256']==sha(checked(row['raw_log']))
assert {k:n[k]for k in row['original_body_times']}==row['original_body_times']and len(re.findall(r'^.*:\d+:\d+: warning:',log,re.M))==row['actual_emitted_warning_headers']==4
ax=q['new_all12_axiom_inspection'];an=json.loads(checked(ax['native']).read_bytes());assert an['actual_exit_code']==0 and an['protection_errors']==[]and checked(ax['source']).read_bytes()==checked(ax['source_snapshot']).read_bytes()
asource=checked(ax['source']).read_text();assert asource.startswith(source)and asource[len(source):].count('#print axioms')==12
printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(ax['raw_log']).read_text())};assert set(printed)==set(q['public_theorem_names'])and printed==q['actual_standard_axioms_per_declaration']and all(set(a)<= {'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Preserve completed author preparation from its genuine sidecar, which does not infer semantic approval.
S=Q.parent/'foundations-Basics12-original-genuine-author-preparation-native-closure32-v1.json';s=json.loads(S.read_bytes());walk(s);refs[str(S)]=sha(S);au=json.loads(checked(s['actual_author_preparation']).read_bytes());assert au['actual_exit_code']==0 and au['protection_errors']==[]and {k:au[k]for k in s['original_body_times']}==s['original_body_times']
# Every definition clause is bound to an actual selected/new proof, rather than to parser integrity.
clause_map=[{'clause':'nonnegative geometric recurrence supplies every prefix q^k e0 and convergence','proof':'SafeLearning.CompleteFoundationsConvergenceRates.actual_one_step_geometric_error_bound_gives_every_natural_prefix_bound'}, {'clause':'exact C/k^p with C,p>0 converges and is slower than every positive geometric BigO rate','proof':q['public_theorem_names'][-2]},{'clause':'upper-bound-only polynomial certificate does not classify a sequence as sublinear','proof':q['public_theorem_names'][6]},{'clause':'positive-C quadratic recursion convention and small-initial-error convergence','proof':'SafeLearning.CompleteFoundationsConvergenceRateExamples.actual_quadratic_errors_converge_in_the_true_small_initial_error_domain'},{'clause':'scalar C2 regular-root Newton actually has invariant neighborhood/all iterates/positive quadratic constant and convergence','proof':q['public_theorem_names'][7]}]
assert 'actual_C2_regular_newton_has_an_invariant_quadratic_neighborhood_and_converges'in source and 'isBigO_const_mul_left_iff hc.ne\''in source
assert 'coefficient * t ^ (-power)'in source and '-power / x'in source
guard()
f={'status':'passed_independent_Basics12_exact_ten_prefix_two_additions_and_full_prospective916918_semantic_composition_review','errors':[],'full_source_read':True,'all12_complete_bodies_and_three_entire_selected19_sources_read':True,'original10_complete_component_peer_preserved_and_explicitly_reused':q['original_full10_independent_component_peer'],'entire_original10_source_bytes_exact_prefix':True,'new_two_full_body_components_approved':{'actual_positive_scaled_reciprocal_errors_converge_and_have_no_geometric_big_o_bound':True,'actual_positive_scaled_power_curve_has_the_true_flattening_logarithmic_slope':True},'used_primary_complete_bodies_read':True,'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_count':12,'definitions_count':0,'public_theorem_names':q['public_theorem_names'],'full_definition_clause_correspondence':clause_map,'full_current_and_prospective_literals_read':True,'prospective_whole_decisions':{key:{'whole_semantic_approved':True,'missing_requirements':[],'conditional_on_later_exact_four_phrase_source_application':True,'exact_entire_proposed_literal':q['entire_prospective_three_literals'][key]['entire_proposed']}for key in ['primer-basics.html::node-916','primer-basics.html::node-918']},'current_original_whole916918_approved':False,'current_or_prospective_whole922_approved':False,'whole922_remaining_gaps':['The unchanged linked Module2 interior-point iteration complexity, Module8 actual algorithm-rate domain and PrimerB gradient-descent associations are not established by this bounded12 family.'],'exact_narrow_proposal_prerequisite':q['exact_approved_four_phrase_unnumbered_proposal'],'exact_narrow_peer_prerequisite':q['independent_full_literal_and_fresh29_narrow_peer'],'original_six_true_source_histories_body_time_context_warnings_unchanged':True,'original_source_exit_codes':q['all_genuine_source_codes'],'new12_true_native':row,'new_all12_true_axiom_native':ax,'actual_standard_axioms_per_declaration':printed,'genuine_author_preparation_sidecar':ref(S),'source_ordinal_applied_or_owner_canonical_selected_publication_mutated':False,'uninstalled_ten_prefix_not_an_additional_count_if_full12_later_installed':True,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'prospective_whole_keys':list(f['prospective_whole_decisions']),'whole922':False,'errors':[]}))
