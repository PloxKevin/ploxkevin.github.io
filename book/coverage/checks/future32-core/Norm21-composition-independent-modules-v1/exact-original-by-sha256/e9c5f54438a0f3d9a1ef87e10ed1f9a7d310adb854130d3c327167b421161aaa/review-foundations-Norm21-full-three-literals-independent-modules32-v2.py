from pathlib import Path
from fractions import Fraction as Fr
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/common-mixed-matrixnorm21-full-scope-v1/foundations-common-mixed-inducednorm21-entire-source-three-literals-full-mathematical-independent-review-request32-v1.json';QH='f79f36b9f416047769fe1a0f73cd8220a577541db7154a9f664b19a01647f7f7';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-Norm21-independent-modules32-findings-v2.json');P=Path('/tmp/foundations-common-matrixnorm-positive-dimensions-unnumbered32-v1/foundations-common-inducednorms-positive-dimensions-one-phrase-unnumbered-full29-proposal32-v1.json');PH='13203e3e9fb32999536666a488fc64cffaec2ba7355646917ac35005dfcb3b57'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert p.is_file()and sha(p)==r['sha256'],r
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(C)==CH and sha(Q)==QH and sha(P)==PH and not F.exists();ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH
 for n,h in g.items():assert sha(path(n))==h,n
 return []
guard();q=json.loads(Q.read_bytes());prop=json.loads(P.read_bytes());refs={str(Q):QH,str(P):PH}
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str)and len(x['sha256'])==64:
   p=checked(x);refs[str(p)]=sha(p)
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(q);walk(prop)
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(path(n))==h;refs[n]=h
source=checked(q['final_genuine_passed_source']).read_text();sys.path.insert(0,str(R/'book/coverage'));import lean_names
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==25
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==21 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==4
assert source.count('private theorem ')==6 and not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
for v in q['genuine_literal_byte_prefixes'].values():
 if isinstance(v,dict):assert source.startswith(checked(v).read_text())
inv=json.loads(checked(q['current_inventory81']).read_bytes());literals=q['entire_three_current_literals'];assert set(literals)=={'primer-linalg.html::node-'+x for x in ['305','307','311']}
for k,lit in literals.items():assert lit==next(r for r in inv['material_source_units']if r['key']==k)
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()and q['full_p_norm_domain_and_dual_norm_context_lines139_309']==''.join(page.decode().splitlines(keepends=True)[138:309])and q['full_induced_norm_definition_table_proofs_and_running_fixture_context_lines309_350']==''.join(page.decode().splitlines(keepends=True)[308:350])
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());assert all(row in owner['material_claims']for row in q['actual_installed_owner31_affected_rows'])and len(q['actual_installed_owner31_affected_rows'])==3 and all(row['status']=='pending'for row in q['actual_installed_owner31_affected_rows'])
for p in q['entire_three_selected_dependencies'].values():checked(p).read_text()
for p in q['full_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert [r['actual_exit_code']for r in history]==[1,0,1,1,0,1,0,0,0]
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log']);assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code']and n['protection_errors']==[] and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[6]['source']).read_text()==source
axsource=checked(history[-1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==21
printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[-1]['raw_log']).read_text())};assert set(printed)==set(th)and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<={'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Exact independent fixture recomputation and rounding: A^T A has eigenvalues8,2; AA^T is diag8,2.
A=((2,2),(-1,1));G=[[sum(A[k][i]*A[k][j]for k in range(2))for j in range(2)]for i in range(2)];H=[[sum(A[i][k]*A[j][k]for k in range(2))for j in range(2)]for i in range(2)]
assert G==[[5,3],[3,5]]and H==[[8,0],[0,2]]and max(sum(abs(A[i][j])for i in range(2))for j in range(2))==3 and max(sum(abs(v)for v in r)for r in A)==4 and max(abs(v)for r in A for v in r)==2
assert Fr(565,200)**2<8<Fr(567,200)**2
assert prop['exact_replacements']==[{'before':'$\\|A\\|_1=\\max_j\\sum_i|a_{ij}|$ (largest absolute <strong>column</strong> sum);','after':'For $m,n\\ge1$, $\\|A\\|_1=\\max_j\\sum_i|a_{ij}|$ (largest absolute <strong>column</strong> sum);'}]
for k,v in prop['entire_current_and_proposed_literal_records'].items():assert v['entire_current']==literals[k]
assert prop['entire_unchanged_current_and_prospective311_proof_fixture']['current']==literals['primer-linalg.html::node-311']and prop['entire_unchanged_current_and_prospective311_proof_fixture']['prospective']['source_text']==literals['primer-linalg.html::node-311']['source_text']
sidecars=list(Q.parent.glob('*closure*.json'));assert len(sidecars)==1;side=sidecars[0];sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side);author=json.loads(checked(sd['actual_original_native']).read_bytes());assert author['actual_exit_code']==0 and author['protection_errors']==[]
prior_reader=Path('/tmp/foundations-Norm21-independent-modules32-actual-v1.json');prior_helper=Path('/tmp/review-foundations-Norm21-full-three-literals-independent-modules32-v1.py');prior_wrapper=Path('/tmp/run-foundations-Norm21-full-three-literals-independent-modules32-v1.py');pn=json.loads(prior_reader.read_bytes());assert pn['actual_exit_code']==1 and pn['protection_errors']==[]
for pp in [prior_reader,prior_helper,prior_wrapper,path(pn['log'])]:refs[str(pp)]=sha(pp)
guard();gap='Current table and its generic proof paragraph omit the common positive row/column domain: a worst row and row maximum do not exist for m=0. The exact proposed m,n>=1 table prefix scopes every formula and the following unchanged proof paragraph.'
decisions={k:{'entire_current_literal_read':True,'current_whole_semantic_approved':False,'current_missing_requirements':[gap],'entire_prospective_literal_and_context_read':True,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact_proposal_application':True}for k in literals}
f={'status':'passed_independent_Norm21_full_mathematics_current_components_prospective_three_wholes','errors':[],'full_source_read':True,'all21_four_definitions_six_private_proofs_read':True,'full_three_selected_sources_and_used_primary_complete_proof_bodies_read':True,'original_request':ref(Q),'dimension_proposal':ref(P),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':21,'public_name_count':25,'entire_current_literals':literals,'entire_prospective_table_and_unchanged_following_proof_literals':prop['entire_current_and_proposed_literal_records'],'unchanged_proof_fixture':prop['entire_unchanged_current_and_prospective311_proof_fixture'],'whole_unit_decisions':decisions,'all21_exact_component_scopes_approved':True,'component_missing_requirements':[],'actual_named_singular_value_Gram_and_operator_norm_correspondence_read':True,'actual_full_circle_image_is_ellipse_and_longest_axis_supported':True,'zero_row_sign_vector_attains_zero_ball_bound_without_unit_norm_claim':True,'independent_Fraction_fixture_Gram_and_rounding_verified':True,'original_true_source_and_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'genuine_original_author_preparation_sidecar':ref(side),'current_owner_pending_rows_preserved':q['actual_installed_owner31_affected_rows'],'independent_parser_not_run_by_this_full_math_reader':True,'no_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'prior_genuine_reader1_schema_failure':ref(prior_reader),'prior_reader1_failure_reason':'Completed author sidecar uses actual_original_native, not the WeightedAngle sidecar key actual_author_preparation; all prior mathematical/native/literal assertions had passed. Original reader helper/native/raw/times preserved.','input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'theorems':21,'current_wholes':False,'prospective_wholes':['305','307','311'],'errors':[]}))
