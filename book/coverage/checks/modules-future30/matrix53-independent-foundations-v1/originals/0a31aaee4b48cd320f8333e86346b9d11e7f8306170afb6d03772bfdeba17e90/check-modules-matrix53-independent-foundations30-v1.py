from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/matrix53-normal-covariance-supplement-v2/modules-matrix53-provided-matrix-normal-full-eleven-body-association-component-review-request30-v2.json'
OUT=Path('/tmp/modules-matrix53-independent-foundations30-findings-v1.json')
EXTRA=Path('/tmp/modules-matrix53-independent-foundations30-extra-primary-v1')
assert not OUT.exists() and not EXTRA.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def path(q):
 p=Path(q['file']);return p if p.is_absolute() else ROOT/p
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q);assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
 closed[str(p)]=q['sha256'];return p
assert sha(REQUEST)=='7ce22826d18cd690bc36d685096a247455cd98677b4cda33d2c413a9b2f6fa24'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 add(q);p=Path(n);p=p if p.is_absolute() else ROOT/p;assert sha(p)==q['sha256']
source=add(d['source']);body=source.read_text()
sys.path.insert(0,str(ROOT/'book/coverage'));import lean_names;add(ref(ROOT/'book/coverage/lean_names.py'))
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(body))
decs=lean_names.declarations(body);names=[r['name'] for r in decs if r['kind'] in ['theorem','lemma']];other=[r for r in decs if r['kind'] not in ['theorem','lemma']]
assert len(names)==d['public_theorem_count']==53 and names==d['public_theorem_names'] and len(decs)==d['public_declaration_count']==77
assert names[42:]==d['new11_public_theorem_names'] and other[-5:]==d['new_five_other_declarations']
old=add(d['original42_entire_byte_prefix']);assert source.read_bytes().startswith(old.read_bytes()) and old.stat().st_size==d['prefix_length_bytes']==34396 and d['prefix_includes_closing_namespace_end'] is True
prior=add(d['original42_independent_full_semantic_peer']);pd=json.loads(prior.read_bytes())
assert sha(prior)=='0b202383dae9bb629732c68b0b9e5ebed031573f6cef18105c7e8e97ba1a3a1e' and pd['errors']==[] and pd['source']['sha256']==sha(old) and pd['whole_current_Exercise19_or_any_material_literal_approved'] is False
oldrequest=json.loads(add(d['original42_full_component_request']).read_bytes())
for k in ['entire_current_exercise','entire_original_owned_exercise_row','entire_current_material_literals','entire_original_material_rows','entire_used_scenario_section_context','entire_exercise_context']:assert d[k]==oldrequest[k]
assert d['new_genuine_native_codes']==[1,1,1,0] and d['new_genuine_warning_headers']==[27,27,27,27]
for row,code in zip(d['four_new_authentic_kernel_histories'],[1,1,1,0]):
 a=json.loads(add(row['native']).read_bytes());raw=add(row['raw_log'])
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k]) is int and a[k]==code
 assert a['status']==('passed_actual_tmp_lean_only' if code==0 else 'failed_actual_tmp_lean_or_protection') and row['actual_exit_code']==code
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean') and a['protection_errors']==[] and a['source_unchanged'] is True
 assert sha(add(row['source']))==sha(add(row['source_snapshot']))==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256'] and len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==row['actual_warning_headers']==27
 assert row['original_actual_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 assert [a[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 for k in ['original_actual_runner','actual_source65_installed29_context']:
  q=d['original_closed_byte_aliases'][a[k]['file']];assert q['sha256']==a[k]['sha256'];add(q)
 for k in ['actual_installed29_selection','actual_frozen29_original_audit']:add(a[k])
 assert all(sha(ROOT/n)==h for n,h in a['installed29_owner_sha256'].items())
assert d['four_new_authentic_kernel_histories'][-1]['source']['sha256']==sha(source)
inv=json.loads(add(d['current_inventory']).read_bytes());owner=json.loads(add(d['immutable_original_owner29']).read_bytes())
assert d['current_inventory']['sha256']=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
current79=ROOT/'book/coverage/inventory.json';assert sha(current79)=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de';inv79=json.loads(current79.read_bytes());add(ref(current79))
assert path(d['immutable_original_owner29']).read_bytes()==(ROOT/'book/coverage/modules.json').read_bytes()
assert d['entire_current_exercise']==next(r for r in inv['exercises'] if r['key']=='verification.html::exercise-19')==next(r for r in inv79['exercises'] if r['key']=='verification.html::exercise-19')
assert d['entire_original_owned_exercise_row']==next(r for r in owner['exercises'] if r['inventory_key']=='verification.html::exercise-19')
for u in d['entire_current_material_literals']:assert u==next(r for r in inv['material_source_units'] if r['key']==u['key'])==next(r for r in inv79['material_source_units'] if r['key']==u['key'])
keys={u['key'] for u in d['entire_current_material_literals']};assert d['entire_original_material_rows']==[r for r in owner['material_claims'] if any(k in keys for k in r['source_unit_keys'])]
for k in ['entire_used_scenario_section_context','entire_exercise_context']:
 c=d[k];page=add(c['original_page']);assert page.read_bytes()==(ROOT/'SafeLearning/verification.html').read_bytes()
 assert c['keepends_exact_full_html']==''.join(page.read_text().splitlines(keepends=True)[c['start_line_inclusive']-1:c['end_line_exclusive']-1])
for row in d['full_new_used_primary_API_sources']:add(row['entire_physical_primary_source'])
extra=[];base=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'
for p in [base/'LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean']:
 q=EXTRA/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());add(ref(q));extra.append({'original_historical_path':str(p),'entire_physical_source':ref(q)})
author=Path('/tmp/modules-matrix53-normal-covariance-supplement30-preparation-actual-v2.json');a=json.loads(author.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[] and a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['raw_log'])==a['raw_log_sha256']
for p in [author,Path(a['raw_log']),Path(a['actual_command'][1]),Path('/tmp/run-modules-matrix53-normal-covariance-supplement30-preparation-v2.py')]:add(ref(p))
for k in ['whole_current_exercise_requested','source_applied','source_ordinal_reserved','canonical_pairs_executed','whole_promotion_performed','coverage_complete']:assert d[k] is False
reasons=[
'The standard Euclidean Gaussian is genuinely the toLp pushforward of independent unit-variance Gaussian coordinates. The previously proved real Gaussian full-support body and finite product full-support instance apply to that probability measure. WithLp toLp is surjective and continuous in the product-induced topology. Positive covariance supplies an actual invertible CFC square root, by its nonnegative-unit equivalence and the positive matrix unit theorem. The actual Euclidean matrix action is continuous and surjective, so translation plus this action maps full support onto full support. The probability assertion also holds for other covariance inputs because the actual definition is a measurable Gaussian pushforward; full support and covariance identities require the explicit positive factors.',
'PosteriorIndex is exactly Fin5 columns times Fin4 rows. The actual latent multivariateGaussian(mean,V tensor U) is defined explicitly. The mapping sends its first four columns to A and last column to B; inverse coordinates are constructed with actual Fin.snoc, not supplied as a desired bijection. The complete fin-snoc proofs establish each coordinate equality. Continuity is proved for the original finite product Plant topology; CStar matrix norm notation is confined to the Gaussian square-root section. The genuine covariance-evaluation proof uses the CFC square-root square identity, Gaussian integrability, and Euclidean basis covariance. The genuine covariance-map proof applies actual measurable maps and coordinate functions, deriving V[j,jprime]*U[i,iprime] for the recovered (A,B). Positive U,V make the Kronecker positive definite by real nonnegative Gram factors and the explicit invertible Kronecker matrix. This establishes a provided matrix-normal law; it does not identify that law with a GP derivative conditional posterior.',
'The actual provided-law full-support and probability instances yield the five-independent-sample product measure. The unchanged prior nonempty open five-model trace obstruction is measurable and has strictly positive product mass. Every point in that open witness excludes the actual paper PSD initial-LMI certificate by the approved principal/Schur/closed-unit-disk bridge. Monotonicity gives positive outer measure to the wider existential-infeasibility set; full measurability of that wider set is not newly asserted. No incompatible pair, arbitrary sample count, posterior conditioning, general scenario bound, or optimizer attainment is derived from these eleven bodies.'
]
groups=[]
for scope,ns,reason in zip(d['exact_components_requested'],[names[42:45],names[45:52],names[52:]],reasons):groups.append({'scope':scope['scope'],'public_theorem_names':ns,'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':reason})
assert sorted(n for g in groups for n in g['public_theorem_names'])==sorted(names[42:])
f={'status':'passed_independent_matrix53_exact42_prefix_full11_provided_matrix_normal_component_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'source':ref(source),'public_theorem_count':53,'public_declaration_count':77,'public_theorem_names':names,'other_public_declarations':other,'original42_full_semantic_peer_exact_body_time':ref(prior),'entire_original42_byte_prefix_retained':True,'all53_full_bodies_read_with_original42_semantic_scope_retained':True,'all11_entire_new_bodies_and_five_other_declarations_read':True,'full_used_Gaussian_probability_covariance_CFC_square_root_matrix_unit_Kronecker_coordinate_and_open_support_proof_chains_read':True,'full_current_exercise_five_material_literals_rows_and_context_read':True,'component_decisions':groups,'primary_physical_sources':d['full_new_used_primary_API_sources'],'additional_used_primary_physical_sources':extra,'genuine_new_native_history':d['four_new_authentic_kernel_histories'],'genuine_new_native_codes':[1,1,1,0],'genuine_new_warning_headers':[27,27,27,27],'original_nine_native_histories_and_original42_verdict_times_retained_by_exact_refs':True,'original_genuine_author1_failure':d['original_author_preparation1_true_failure'],'original_genuine_author2_native':ref(author),'all_original_sources_snapshots_logs_failures_and_native_body_times_preserved':True,'current_Source79_association':{'historical_Source65_inventory':d['current_inventory'],'actual_current_Source79_inventory':ref(current79),'full_requested_exercise_and_five_unit_records_identical':True,'raw_owner29_retained_historical_Source65':d['immutable_original_owner29'],'original_Source65_kernel_context_and_times_retained_unchanged':True,'current79_not_claimed_to_have_new_aggregate_kernel_audit':True},'whole_current_Exercise19_or_any_material_literal_approved':False,'scope_exclusions':d['scope_exclusions'],'provided_matrix_normal_covariance_and_non_degenerate_full_support_approved':True,'GP_conditional_posterior_or_incompatible_pair_or_general_scenario_theorem_approved':False,'full_failure_event_measurability_newly_derived':False,'positive_measurable_open_failure_witness_explicit':True,'semantic_decisions_from_full_math_read_not_integrity':True,'compiler_or_parser_launched_by_reviewer':False,'canonical_or_source_or_owner_or_publication_mutation':False,'source_ordinal_reserved':False,'source_applied':False,'coverage_complete':False,'prospective_postfreeze_evidence_not_part_of_frozen29':True,'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':d['original_closed_byte_aliases'],'errors':[]}
OUT.write_text(json.dumps(f,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'new_components':11,'groups':3,'whole_decision':False,'errors':[]}))
