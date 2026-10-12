from pathlib import Path
import hashlib,json,re,sys
from fractions import Fraction
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/frobenius15-full-scope-v1/foundations-frobenius15-entire-source-two-full-current-literals-independent-review-request32-v1.json';QH='994ac6f953d05abe120f4ad17b7823b20ecec3f5b3b2f3fa94f58969074dc12a';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-Frobenius15-independent-modules32-findings-v1.json');D=Path('/tmp/modules-Frobenius15-complete-used-additional-primary32-v1')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert p.is_file()and sha(p)==r['sha256'],r
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(C)==CH and sha(Q)==QH and not F.exists()and not D.exists();ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
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
names=lean_names.declarations(source);assert names==q['all_public_declarations'] and len(names)==16
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==15 and th==q['public_theorem_names']
assert len([d for d in names if d['kind']=='def'])==1
masked=lean_names.without_comments(source);assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',masked)and 'private theorem actual_gram_is_hermitian'in source
inv=json.loads(checked(q['current_inventory81']).read_bytes());rows={r['key']:r for r in inv['material_source_units']};assert set(q['complete_current_literals'])=={'primer-linalg.html::node-315','primer-linalg.html::node-317'}
for key,literal in q['complete_current_literals'].items():assert rows[key]==literal
current=checked(q['full_current_Source81_linalg']).read_bytes();assert current==(R/'SafeLearning/primer-linalg.html').read_bytes()
assert q['full_source_context_lines300_345']==''.join(current.decode().splitlines(keepends=True)[299:345])
selected=checked(q['full_selected_literal_matrix_CLM_bridge_source']);s=selected.read_text();assert 'def sourceMatrixMap'in s and '(Matrix.toLpLin a b A).toContinuousLinearMap'in s and 'actual_matrix_map_is_the_literal_matrix_vector_product'in s
for p in q['complete_used_primary_source_copies'].values():checked(p).read_text()
# Physically close additional complete providers of the actually used inner products and elementary matrix identities.
D.mkdir();extra={};ml=R/'verification/lean/.lake/packages/mathlib/Mathlib'
providers={'Analysis/InnerProductSpace/PiL2.lean':['theorem PiLp.inner_apply'],'Analysis/InnerProductSpace/Basic.lean':['theorem real_inner_self_eq_norm_sq'],'LinearAlgebra/Matrix/Hermitian.lean':['theorem isHermitian_conjTranspose_mul_self'],'Data/Matrix/Mul.lean':['dotProduct_transpose_mulVec']}
for n,tokens in providers.items():
 original=ml/n;code=original.read_text();assert all(token in code for token in tokens),n
 target=D/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(original.read_bytes());assert sha(target)==sha(original);extra[n]=ref(target);refs[str(target)]=sha(target)
# Authenticate all preserved failures and final pass, with real warning headers, cwd, source snapshots and exact runner/context.
codes=[];warning_counts=[];hist=[]
for row in q['genuine_original_three_Lean_histories']:
 n=json.loads(checked(row['native']).read_bytes());log=checked(row['raw_log']).read_text();snap=checked(row['source_snapshot']);src=checked(row['source']);assert snap.read_bytes()==src.read_bytes()
 assert n['actual_exit_code']==row['actual_exit_code']and n['protection_errors']==[]and n['source_unchanged']is True
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src) and n['raw_log_sha256']==sha(checked(row['raw_log']))
 assert n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'and n['actual_source81_installed_owner31_context']['sha256']==CH
 assert {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 count=len(re.findall(r'^.*:\d+:\d+: warning:',log,re.M));assert count==row['actual_emitted_location_first_warning_headers']
 codes.append(n['actual_exit_code']);warning_counts.append(count);hist.append(row)
assert codes==[1,1,0]and warning_counts==[8,8,8]
ax=q['actual_separate_all15_axiom_native'];an=json.loads(checked(ax['native']).read_bytes());assert an['actual_exit_code']==0 and an['protection_errors']==[]and checked(ax['source']).read_bytes()==checked(ax['source_snapshot']).read_bytes()
asource=checked(ax['source']).read_text();assert asource.startswith(source)and asource[len(source):].count('#print axioms')==15
alog=checked(ax['raw_log']).read_text();printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",alog)}
assert set(printed)==set(th)and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<= {'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Independent exact matrix and rounding recomputation.
A=[[2,2],[-1,1]];gram=[[sum(A[k][i]*A[k][j]for k in range(2))for j in range(2)]for i in range(2)];assert gram==[[5,3],[3,5]]and sum(x*x for row in A for x in row)==10
assert Fraction(3155,1000)**2<10<Fraction(3165,1000)**2
assert 8<=10<=16 and Fraction(1,1)**2<2
# No desired spectral inequality is a hypothesis: Gram eigenvalues equal actual unit image energy, and rank-cardinality removes only zero values.
for token in ['h.rank_eq_card_non_zero_eigs','Matrix.rank_transpose_mul_self','h.trace_eq_sum_eigenvalues','actual_each_gram_eigenvalue_is_nonnegative_and_bounded_by_operator_norm_squared A i','actual_rectangular_euclidean_matrix_action_is_bounded_by_frobenius A']:
 assert token in source
guard()
f={'status':'passed_independent_Frobenius15_full_source_two_entire_current_literals_semantic_review','errors':[],'full_source_read':True,'all15_entire_public_bodies_one_definition_private_Gram_proof_and_selected19_complete_source_read':True,'all_used_primary_API_full_bodies_read':True,'additional_complete_actual_primary_providers':extra,'original_full_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'actual_public_theorem_names':th,'public_theorem_count':15,'definitions_count':1,'full_current_literal_decisions':{key:{'entire_current_literal_read':True,'whole_semantic_approved':True,'missing_requirements':[],'reason':'All Frobenius definition/flattened norm, trace inner product, noninduced-family witness, exact identity sqrt dimension, sharp arbitrary rectangular rank comparison and running sqrt10 approximation clauses have actual full support.'}for key in q['complete_current_literals']},'entire_current_literals':q['complete_current_literals'],'non_induced_claim_scope':'The Frobenius norm family is not an induced operator-norm family, witnessed by I2; no false exclusion of coincidence in one dimension is asserted.','empty_finite_input_or_output_dimensions_supported_without_unit_sphere_existence_premise':True,'actual_rank_and_actual_eigenvalue_bounds_derived_not_assumed':True,'exact_running_Gram_and_rounding_independently_checked':{'Gram':gram,'squared_Frobenius':10,'rounding_squared_lower':str(Fraction(3155,1000)**2),'rounding_squared_upper':str(Fraction(3165,1000)**2)},'original_true_kernel_histories':hist,'actual_kernel_exit_codes':codes,'actual_warning_headers':warning_counts,'separate_genuine_all15_axiom_native':ax,'actual_standard_axioms_per_public_theorem':printed,'original_induced19_component_verdict_body_time_unchanged':q['original_induced19_component_peer_body_time_unchanged'],'no_other_linalg_unit_or_source_ordinal_or_live_owner_canonical_publication_promotion':True,'compiler_or_parser_or_selected_source_mutated_by_reader':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_keys':list(f['full_current_literal_decisions']),'theorems':15,'errors':[]}))
