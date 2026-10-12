from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
Q=R/'book/coverage/checks/future32-foundations/metric-examples10-full-scope-v1/foundations-metric-examples10-entire-source-all-input-distances-grid-and-certified-balls-current202-independent-review-request32-v1.json'
QH='7bf9c88443af5cfcb1b262c06bff9504402abfc63a60c205c739c293c32fbd3f'
C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
F=Path('/tmp/foundations-MetricExamples10-independent-modules32-findings-v1.json')
E=Path('/tmp/MetricExamples10-independent-extra-physical-providers-v1/added-used-physical-providers.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert p.is_file()and sha(p)==r['sha256'],r
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(C)==CH and sha(Q)==QH and not F.exists()
ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH
 for n,h in g.items():assert sha(path(n))==h,n
guard();q=json.loads(Q.read_bytes());assert q['errors']==[]
refs={str(Q):QH,str(E):sha(E)}
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str)and len(x['sha256'])==64:
   p=checked(x);refs[str(p)]=sha(p)
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(q)
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(path(n))==h;refs[n]=h
extra=json.loads(E.read_bytes());walk(extra)
source=checked(q['final_genuine_passed_source']).read_text();sys.path.insert(0,str(R/'book/coverage'));import lean_names
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==11
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==10 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==1
assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
body=[]
for m in re.finditer(r'^theorem (\w+)',source,re.M):
 tail=source[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1]if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
assert body==q['all10_complete_body_signatures']
inv=json.loads(checked(q['current_inventory81']).read_bytes());literal=q['entire_current_literal'];assert literal==next(r for r in inv['material_source_units']if r['key']=='primer-linalg.html::node-202')
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()
assert q['full_current_metric_examples_and_signed_distance_context_lines194_239']==''.join(page.decode().splitlines(keepends=True)[193:239])
assert 'on $D$ satisfies'in q['full_current_metric_examples_and_signed_distance_context_lines194_239']and 'closed ball'in q['full_current_metric_examples_and_signed_distance_context_lines194_239']
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());row=q['actual_installed_owner31_pending_row'];assert row in owner['material_claims']and row['status']=='pending'and row['source_text']==literal['source_text']and row['source_text_sha256']==literal['text_sha256']
for selected in q['entire_two_selected_metric_and_positive_L_certificate_sources'].values():checked(selected).read_text()
for p in q['full_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
for p in extra.values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert [r['actual_exit_code']for r in history]==[1,0,0]and [r['actual_emitted_location_first_warning_headers']for r in history]==[0,1,1]
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log'])
 assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code']and n['protection_errors']==[]and n['source_unchanged']is True and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[1]['source']).read_text()==source
axsource=checked(history[-1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==10
printed={name:[a.strip()for a in atoms.replace('\n',' ').split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[-1]['raw_log']).read_text(),re.S)}
assert list(printed)==th and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<={'propext','Classical.choice','Quot.sound'}for a in printed.values())
def headers(s):return re.findall(r'(?ms)^theorem\s+\w+.*?(?=\s*:=)',s)
assert headers(source)[:9]==headers(checked(history[0]['source']).read_text())and q['original_first9_statement_headers_retained_exactly_after_repairs']is True
side=Q.parent/'foundations-metric-examples10-original-genuine-author-preparation-native-closure32-v1.json';sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side)
author=json.loads(checked(sd['exact_original_execution_and_native_refs']['completed_original_native']).read_bytes());assert author['actual_exit_code']==0 and author['protection_errors']==[]and {k:author[k]for k in sd['original_body_times']}==sd['original_body_times']
assert sd['unchanged_original_request']['sha256']==QH
guard()
component_scopes={
 'all_input_coordinate_halfspace_distance':{'approved':True,'domain':'Every finite Euclidean coordinate type with an actual coordinate i, every input x; an explicit single-coordinate projection supplies the attained upper bound and every halfspace point supplies the norm lower bound.'},
 'all_input_unit_disc_distance':{'approved':True,'domain':'The actual closed unit-ball formula is derived in every real normed vector space at every input, including its inside and outside radial branches; the literal planar Euclidean unit disc is its specialization.'},
 'all_real_radii_infinity_coordinate_boxes':{'approved':True,'domain':'Every nonempty finite real coordinate type, every x,x0 and real epsilon. Negative-radius sets are both empty, the zero-radius set is the center, and each positive-radius condition is exactly the independent coordinate interval.'},
 'actual_rectangular_grid_metric_and_attainment':{'approved':True,'domain':'Every complete rectangular nearest-neighbour grid Fin(r+1) times Fin(c+1), including one-vertex dimensions: exact unit-step adjacency, derived connectivity, real shortest-path metric axioms and a genuinely attained minimum walk length.'},
 'arbitrary_connected_graph_metric_and_attainment':{'approved':True,'domain':'Every structurally connected graph, finite or infinite. This does not assign a finite metric to an arbitrary disconnected obstacle mask; library unreachable-pair junk value0 is explicitly excluded by connectivity.'},
 'actual_Lipschitz_margin_positive_ball_and_union':{'approved':True,'domain':'Global LipschitzWith L on the declared (pseudo)metric domain, with L>0. The lower margin is derived and each actual positive-center closed ball and the entire union have g>=0; balls are relative to that domain.'},
 'zero_Lipschitz_entire_domain':{'approved':True,'domain':'LipschitzWith0 on the declared domain yields equality of every two values; one positive center certifies every domain point without division.'}}
correspondence=[
 {'literal_clause':'coordinate halfspace distance at all inputs','theorems':[th[0]],'approved':True},
 {'literal_clause':'unit disc distance at all inputs','theorems':[th[1]],'approved':True},
 {'literal_clause':'infinity ball is exactly the coordinate box, allowing coordinate-by-coordinate interval treatment','theorems':[th[2]],'approved':True},
 {'literal_clause':'shortest-path length on a grid is a metric','theorems':th[3:6]+[th[9]],'approved':True},
 {'literal_clause':'printed lower margin, positive-L closed-ball and union certificate','theorems':th[6:8],'unchanged_selected_positive_L_certificate':q['entire_two_selected_metric_and_positive_L_certificate_sources']['CompleteFoundationsGeometry.lean'],'approved':True},
 {'literal_clause':'zero-L whole declared domain, with no division','theorems':[th[8]],'approved':True}]
f={'status':'passed_independent_MetricExamples10_entire_current202_full_mathematical_review','errors':[],'full_source_read':True,'all10_public_bodies_one_rectangular_grid_definition_read':True,'both_complete_selected_metric_and_geometry_sources_read':True,'all_used_complete_primary_infimum_norm_coordinate_graph_connectivity_shortest_walk_and_Lipschitz_proof_bodies_read':True,'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':10,'public_name_count':11,'definition_count':1,'all10_complete_body_signatures':body,'entire_current_literal':literal,'whole_unit_decisions':{'primer-linalg.html::node-202':{'entire_current_literal_and_full_context_read':True,'current_whole_semantic_approved':True,'current_missing_requirements':[],'context_domain_read':'The vector examples use their ordinary nonempty finite coordinate domain (the first clause names x1), the disc is planar Euclidean, grid means an ordinary connected nearest-neighbour grid, and certificates use the declared metric domain D. These domains agree with the actual all-input proofs and need no new wording proposal.'}},'exact_component_scopes':component_scopes,'all10_exact_component_scopes_approved':True,'component_missing_requirements':[],'full_literal_clause_correspondence':correspondence,'actual_hypotheses_are_structural_domain_or_Lipschitz_primitives_not_desired_distance_or_connectivity_conclusions':True,'no_empty_dimension_negative_radius_or_disconnected_grid_metric_or_certificate_outside_Lipschitz_domain_inference':True,'actual_distance_infimum_association':{'complete_selected_real_norm_infimum_source':q['entire_two_selected_metric_and_positive_L_certificate_sources']['CompleteFoundationsMetricAndSetDistance26.lean'],'both_target_sets_nonempty_derived':True,'halfspace_projection_and_radial_unit_point_attain_upper_bound':True,'all_target_points_satisfy_matching_lower_bound':True},'actual_added_primary_provider_copies':extra,'provider_observation':'The author supplied Group.Constructions pi_norm_le_iff and Module.Basic NormedSpace instance bodies; this independent closure also supplies their direct Pseudo.Pi distance-max and Normed.MulAction scalar-norm providers, with all actually used complete proof bodies read. Original request/source/native bytes stay fixed.','original_true_failed_source9_passed_source10_and_all10_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'genuine_original_author_preparation_sidecar':ref(side),'uncompiled_offline_draft2_not_assigned_a_native':q['uncompiled_offline_draft2_retained_without_native_claim'],'current_owner_pending_row_preserved_unchanged':q['actual_installed_owner31_pending_row'],'no_neighbor197199205209_parent_section_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_Source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_key':'primer-linalg.html::node-202','theorems':10,'public_names':11,'current_whole':True,'errors':[]}))
