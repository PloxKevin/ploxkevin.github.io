from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/foundations-matrix-residual-five-bridges27-full-literal-review-request-v1.json');OUT=Path('/tmp/foundations-matrix-residual17-independent-modules-whole-source-review27-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def checked(r):p=path(r['file']);assert sha(p)==r['sha256'],r;return p
assert sha(REQUEST)=='a4c156bccae27e04b88e33f987cf1e10930eeb8b5ce031de962b7768d48c26a8'
d=read(REQUEST);source=checked(d['source']);body=source.read_text();assert body==d['entire_cumulative_lean_source']
base=d['entire_original_base_request_body_and_time'];assert read(checked(d['original_base_request']))==base
old=d['entire_original_twelve_component_review_body_and_time'];assert read(checked(d['original_twelve_component_review']))==old
assert sha(checked(d['original_twelve_component_review']))=='1278676ab324cca10873e5493667776fd1e44ab30f6bcc13acc20d61ee94033d'
assert body.startswith(base['entire_lean_source']) and body.count(base['entire_lean_source'])==1
assert old['public_theorem_count']==12 and old['whole_material_unit_approved'] is False
clar=d['original_scope_count_clarification'];assert read(checked(clar['reference']))==clar['entire_body']
all_names=re.findall(r'^theorem\s+([\w\u0080-\uffff]+)',body,re.M);assert len(all_names)==17 and len(set(all_names))==17
new=d['new_public_declarations'];assert len(new)==5 and set(n.rsplit('.',1)[-1] for n in new)==set(all_names[-5:])
assert not re.search(r'\bsorry\b|\badmit\b|^axiom\s',body,re.M)
record=read(checked(d['actual_standalone']['reference']));assert record==d['actual_standalone']['entire_record']
for k in ['actual_exit_code','actual_runner_exit_code']:assert type(record[k]) is int and record[k]==0
assert record['source_sha256_before']==record['source_sha256_after']==d['source']['sha256']
assert record['source_unchanged'] is True and record['protection_errors']==[]
assert sha(checked(d['actual_source_snapshot']))==d['source']['sha256']
raw=checked(d['actual_raw_log']);assert raw.read_text().count('warning:')==d['actual_warning_group_count']==3
# Read/re-hash every authentic earlier failure/pass and original review artifact, without rerunning Lean.
evidence={str(REQUEST):sha(REQUEST),str(source):sha(source),str(Path(__file__)):sha(Path(__file__))}
for n,h in d['all_original_failed_and_passed_history_sha256'].items():assert sha(path(n))==h,n;evidence[n]=h
for passage in d['additional_direct_primary_API_passages']:
 p=checked(passage);actual=''.join(p.read_text().splitlines(True)[passage['from_line']-1:passage['through_line']])
 assert actual.rstrip('\n')==passage['entire_passage'].rstrip('\n');evidence[passage['file']]=passage['sha256']
inv=read(checked(d['current_inventory']));unit=d['literal_units'][0];key=unit['source_unit_key'];assert key=='primer-linalg.html::node-1289'
assert next(r for r in inv['material_source_units'] if r['key']==key)==unit['entire_inventory_record']
current=ROOT/unit['entire_inventory_record']['source'];assert sha(current)==unit['entire_inventory_record']['source_sha256']
ctx=d['full_context'];p=checked(ctx);actual=''.join(p.read_text().splitlines(True)[ctx['first_line']-1:ctx['last_line']]);assert actual==ctx['exact_excerpt']
assert hashlib.sha256(actual.encode()).hexdigest()==ctx['excerpt_sha256']
manifest=read(ROOT/'reports/full-coverage/checkpoint-26-manifest.json');assert manifest['status']=='formal_verification_passed_partial_coverage' and len(manifest['proof_files'])==1167
for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256'],n
for n,h in manifest['working_inputs_sha256'].items():
 if n.startswith('SafeLearning/') or n in record['installed26_owner_sha256']:assert sha(ROOT/n)==h,n
for n,h in record['installed26_owner_sha256'].items():assert sha(ROOT/n)==h,n
assert read(checked(d['selected26_selection']))['checkpoint']==26 if 'checkpoint' in read(checked(d['selected26_selection'])) else True
# Direct correspondence: compose the actual finite Euclidean H-map/transpose identities with the preserved generic local perturbation statements.
base_ns='SafeLearning.CompleteFoundationsResidualOrthogonality27.';bridge_ns='SafeLearning.CompleteFoundationsMatrixResidualBridge27.'
groups=[
 {'component_id':'actual_matrix_two_sided_small_perturbation_and_local_necessity','lean_declarations':[base_ns+'actual_residual_two_sided_perturbation_expansion',base_ns+'actual_residual_direction_derivative_follows_from_expansion',base_ns+'actual_every_local_minimum_has_a_residual_perpendicular_to_whole_range',base_ns+'actual_normal_equation_iff_residual_perpendicular_to_whole_range',bridge_ns+'actual_rectangular_matrix_operator_action',bridge_ns+'actual_rectangular_matrix_adjoint_is_the_actual_transpose_action',bridge_ns+'actual_matrix_squared_residual_is_the_generic_loss'],'hypotheses':'Arbitrary real rectangular finite H, standard Euclidean spaces, arbitrary measurements y and candidate x. IsLocalMin is the stated sufficiently-small two-sided perturbation premise; no global minimum is assumed for necessity.','reason':'The actual H.toEuclideanLin continuous operator is exactly H.mulVec and its actual adjoint is H.transpose.mulVec. Substituting these identities into the generic all-real-t expansion gives the printed matrix residual expansion and its vᵀHᵀr cross term. The genuine local derivative argument, using both signs through IsLocalMin, proves every modeled change is orthogonal to the residual and hence Hᵀr=0.','status':'proved','missing_clauses':[]},
 {'component_id':'actual_matrix_normal_equation_and_global_sufficiency','lean_declarations':[base_ns+'actual_normal_equation_gives_exact_global_loss_difference',base_ns+'actual_local_least_squares_minimum_is_already_a_global_minimum',bridge_ns+'actual_matrix_least_squares_normal_equation_is_exactly_transpose_residual_zero'],'hypotheses':'Same finite real matrix and arbitrary y,x, with actual Hᵀ(Hx-y)=0. No independent-column assumption is needed for global least-squares sufficiency.','reason':'The exported equivalence identifies actual Euclidean matrix squared-residual global minimization with the printed transpose residual equation. The exact generic loss difference is a nonnegative squared norm, so this equation is sufficient as well as necessary.','status':'proved','missing_clauses':[]},
 {'component_id':'independent_actual_matrix_columns_positive_gram_and_one_attained_estimate','lean_declarations':[base_ns+'actual_independent_matrix_columns_give_positive_definite_transpose_gram',base_ns+'actual_independent_columns_gram_is_strictly_positive',base_ns+'actual_independent_columns_make_the_normal_equation_solution_unique',base_ns+'actual_finite_dimensional_independent_columns_have_one_attained_minimum',bridge_ns+'actual_independent_matrix_columns_have_one_attained_unique_least_squares_estimate'],'hypotheses':'Function.Injective H.mulVec is the finite real matrix independent-columns premise. Finite Euclidean domain, arbitrary y; no unproved attainment assumption.','reason':'The actual transpose Gram is proved positive definite from injective H.mulVec. The direct matrix bridge establishes injectivity of its Euclidean continuous operator, derives a genuine attained unique minimum via the finite-dimensional normal equation and transfers that minimum back to the literal matrix objective.','status':'proved','missing_clauses':[]}
]
all_decls=base['all_public_declarations']+new
assert len(all_decls)==17 and len(set(all_decls))==17
material={'source_unit_key':key,'entire_inventory_record':unit['entire_inventory_record'],'source_text':unit['entire_inventory_record']['source_text'],'source_text_sha256':unit['entire_inventory_record']['text_sha256'],'status':'proved','decision':'approved_full_literal_under_explicit_finite_real_matrix_hypotheses','whole_literal_approved':True,'lean_declarations':all_decls,'hypotheses':'Finite real rectangular matrix H on standard Euclidean spaces; actual matrix operator/transpose adjoint identified. Arbitrary measurements and candidate. A local minimum for necessity; injective H.mulVec (independent columns) only for positive-definite Gram and unique attained estimate.','reason':'All clauses of the exact directional-expansion, local normal-equation, range-orthogonality and independent-column unique-least-squares paragraph are covered by the original twelve complete bodies plus the five actual direct matrix/adjoint/loss bridges. The expansion cross term follows from the actual adjoint identity; the local-minimum argument is genuinely two-sided.','components':groups,'missing_clauses':[],'remaining_gaps':[]}
for r in [d['source'],d['actual_standalone']['reference'],d['actual_raw_log'],d['actual_source_snapshot'],d['original_base_request'],d['original_twelve_component_review'],clar['reference'],d['current_inventory'],d['selected26_selection']]:evidence[r['file']]=r['sha256']
result={'status':'passed_independent_full_seventeen_body_and_whole1289_source_review','errors':[],'reviewer':'independent Modules agent','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'source':d['source'],'entire_source':body,'all_seventeen_complete_bodies_read':True,'five_new_complete_matrix_bridge_bodies_read':True,'public_theorem_count':17,'new_public_theorem_count':5,'all_public_declarations':all_decls,'material_units':[material],'whole_material_unit_approved':True,'whole_exercise_approved':False,'missing_clauses':[],'entire_original_twelve_component_review_body_and_time':old,'original_twelve_component_review':d['original_twelve_component_review'],'entire_original_scope_count_clarification':clar['entire_body'],'entire_original_request_body_and_time':d,'full_context':ctx,'actual_standalone_original':record,'actual_warning_groups_retained':3,'original_companion_failed_trial_preserved':True,'packet_preparer_two_native_tool_failure_observations_preserved':True,'protected_counts':{'selected26_sources':1167,'current53_assets':31,'installed26_owners':5},'evidence_sha256':evidence,'scope':'Fresh whole exact literal1289 correspondence after full reading of the five actual matrix companion bridges and the original twelve bodies. Original twelve positive component decisions/body/time remain untouched. TMP standalone only; no canonical/named build, owner mutation, parent exercise or adjacent numerical promotion.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','peer':str(OUT),'sha256':sha(OUT),'whole_unit':key,'public_theorems':17,'missing_clauses':[]}))
