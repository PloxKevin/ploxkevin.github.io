from pathlib import Path
import hashlib,json,re,sys
from fractions import Fraction as Fr
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/boximage-zonotope14-full-scope-v2/foundations-boximage-zonotope14-entire-source-current332-component-prospective332-whole-independent-review-request32-v2.json';QH='5cf17cbe5dc37d399807d9be438ca074cc3537eef9d6c39f377c5c278189664f';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-BoxImage14-independent-modules32-findings-v1.json')
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
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==18
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==14 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==4
assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
inv=json.loads(checked(q['current_inventory81']).read_bytes());literal=q['entire_current_literal'];assert literal==next(r for r in inv['material_source_units']if r['key']=='primer-linalg.html::node-332')
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()and q['full_matrix_norm_and_box_image_context_lines309_362']==''.join(page.decode().splitlines(keepends=True)[308:362])and q['full_previous_radius_and_metric_context_lines172_219']==''.join(page.decode().splitlines(keepends=True)[171:219])
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());assert all(row in owner['material_claims']for row in q['actual_installed_owner31_pending_rows'])and len(q['actual_installed_owner31_pending_rows'])==1 and q['actual_installed_owner31_pending_rows'][0]['status']=='pending'
for p in q['entire_two_selected_dependencies'].values():checked(p).read_text()
for p in q['full_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert [r['actual_exit_code']for r in history]==[1,1,0,0]
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log']);assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code'] and n['protection_errors']==[] and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']==4
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[2]['source']).read_text()==source
axsource=checked(history[-1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==14
printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[-1]['raw_log']).read_text())};assert set(printed)==set(th)and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<= {'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Independent exact planar fixture and area check, plus actual empty negative-radius convention.
W=((1,1),(1,-1));det=W[0][0]*W[1][1]-W[0][1]*W[1][0];assert det==-2
vertices=[tuple(sum(W[i][j]*x[j]for j in range(2))for i in range(2))for x in[(1,1),(-1,-1),(1,-1),(-1,1)]];assert vertices==[(2,0),(-2,0),(0,2),(0,-2)]
assert abs(det)*4==8 and 4*4==16
for i in range(2):assert sum(abs(W[i][j])for j in range(2))==2
prospective=q['exact_planned_prospective_positive_radius_literal'];assert prospective['key']==literal['key']and q['unnumbered_exact_planned_replacements']==[{'before':'$W$ maps','after':'For $\\varepsilon>0$, $W$ maps'}]
assert prospective['source_text']==literal['source_text'].replace('$W$ maps','For $\\varepsilon>0$, $W$ maps')
# Completed author receipt is preserved through its exact sidecar, independently of whole semantics.
sidecars=[p for p in Q.parent.glob('*closure*.json')if p!=Q];assert len(sidecars)==1;side=sidecars[0];sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side)
receipts=[v for k,v in sd.items()if k=='actual_original_native'];assert len(receipts)==1;author=json.loads(checked(receipts[0]).read_bytes());assert author['actual_exit_code']==0 and author['protection_errors']==[]
guard()
f={'status':'passed_independent_BoxImage14_full_current332_components_and_prospective_whole','errors':[],'full_source_read':True,'all14_public_bodies_four_definitions_read':True,'full_selected_AffineIBP29_and_BalancedSensor_sources_and_used_primary_complete_proof_bodies_read':True,'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':14,'public_name_count':18,'entire_current_literal':literal,'entire_prospective_literal':prospective,'whole_unit_decisions':{'primer-linalg.html::node-332':{'entire_current_literal_read':True,'current_whole_semantic_approved':False,'current_missing_requirements':['The norm-ball/image/scaled-segment correspondence needs epsilon>=0; the printed nondegenerate invertible parallelogram needs epsilon>0. The exact one-phrase positive-radius proposal supplies both.'],'entire_prospective_literal_and_context_read':True,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact_proposal_application_and_independent_narrow_parser':True}},'all14_exact_component_scopes_approved':True,'component_missing_requirements':[],'full_column_segment_sum_is_actual_finite_Minkowski_sum_and_named_geometric_segments':True,'tight_box_is_actual_smallest_by_attained_both_sign_coordinate_extrema':True,'invertibility_derives_independent_scaled_generators_for_positive_radius':True,'running_shape_is_actual_scaled_Euclidean_square_and_true_area8_vs16':True,'independent_exact_Fraction_vertex_determinant_area_fixture_verified':True,'old_AffineIBP29_full_peer_body_time_and_own_scope_preserved':q['old_AffineIBP29_full_mathematical_peer_unchanged'],'old_AffineIBP29_metadata_and_actual_pairs_preserved':q['exact_old_AffineIBP29_canonical_proof_metadata_and_pairs'],'original_true_source_and_all14_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'genuine_original_author_preparation_sidecar':ref(side),'original_author1_genuine_metadata_failure_preserved':q['original_genuine_author1_metadata_schema_failure_preserved'],'current_owner_pending_rows_preserved_unchanged':q['actual_installed_owner31_pending_rows'],'no_neighbor_verification196_or_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_key':'primer-linalg.html::node-332','theorems':14,'current_whole':False,'prospective_whole':True,'errors':[]}))
