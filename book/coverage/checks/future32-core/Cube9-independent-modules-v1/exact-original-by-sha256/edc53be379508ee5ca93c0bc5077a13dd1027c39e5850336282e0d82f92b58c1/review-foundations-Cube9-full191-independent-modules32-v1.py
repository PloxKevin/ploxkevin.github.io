from pathlib import Path
import hashlib,json,re,sys
from fractions import Fraction as Fr
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/cube-radius-netmargin9-full-scope-v1/foundations-cube-radius-netmargin9-entire-source-current191-component-prospective191-whole-independent-review-request32-v1.json';QH='d0532b926f3c2c5c137aa1fbde74c44f09845d1cc467b1b7f3ea65fcb2d5bf5a';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-Cube9-independent-modules32-findings-v1.json')
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
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==10
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==9 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==1
assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
inv=json.loads(checked(q['current_inventory81']).read_bytes());literal=q['entire_current_literal'];assert literal==next(r for r in inv['material_source_units']if r['key']=='primer-linalg.html::node-191')
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()and q['full_norm_comparison_cube_and_radius_context_lines188_235']==''.join(page.decode().splitlines(keepends=True)[187:235])
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());assert q['actual_installed_owner31_pending_row']in owner['material_claims']and q['actual_installed_owner31_pending_row']['status']=='pending'
for p in q['entire_four_selected_dependencies'].values():checked(p).read_text()
for p in q['full_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert [r['actual_exit_code']for r in history]==[1,0,0,0]
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log']);assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code'] and n['protection_errors']==[] and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']==0
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[2]['source']).read_text()==source
axsource=checked(history[-1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==9
printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[-1]['raw_log']).read_text())};assert set(printed)==set(th)and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<= {'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Independent exact grid cardinality/rounding and corner/coordinate projection checks.
assert 7**2<50<=8**2 and 15**2<250<=16**2 and 8**2==64 and 16**10==1099511627776
assert 1050000000000<16**10<1150000000000
for x in [Fr(0),Fr(1,3),Fr(1)]:
 for z in [Fr(-5),Fr(-1,7),Fr(0),Fr(3,5),Fr(1),Fr(9,2)]:
  p=max(Fr(0),min(Fr(1),z));assert abs(x-p)<=abs(x-z)
prospective=q['exact_planned_prospective_domain_qualified_literal'];assert prospective['key']==literal['key']and q['unnumbered_exact_planned_replacements']==[{'before':'A cube of side $s$ lies','after':'Assume $s\\ge0$, $\\tau>0$ and $d\\ge1$. A cube of side $s$ lies'}]
assert prospective['source_text']==literal['source_text'].replace('A cube of side $s$ lies','Assume $s\\ge0$, $\\tau>0$ and $d\\ge1$. A cube of side $s$ lies')
assert source.startswith(checked(q['genuine_entire_passed5_byte_prefix']).read_text())
# Extra physical provider closes the actual finite-image cardinality theorem; Image.lean alone imports it.
provider=R/'verification/lean/.lake/packages/mathlib/Mathlib/Data/Finset/Card.lean';refs[str(provider)]=sha(provider);assert 'theorem card_image_le' in provider.read_text()and 'theorem card_image_of_injective' in provider.read_text()
for key in ['full_current_Primer0_net_definitions','full_current_PrimerB_margin_and_net_context']:checked(q[key]).read_text()
# Completed author receipt is preserved through its exact sidecar, independently of whole semantics.
sidecars=[p for p in Q.parent.glob('*closure*.json')if p!=Q];assert len(sidecars)==1;side=sidecars[0];sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side)
receipts=[v for k,v in sd.items()if k=='actual_original_native'];assert len(receipts)==1;author=json.loads(checked(receipts[0]).read_bytes());assert author['actual_exit_code']==0 and author['protection_errors']==[]
guard()
f={'status':'passed_independent_Cube9_full_current191_components_and_prospective_whole','errors':[],'full_source_read':True,'all9_public_bodies_one_projection_definition_read':True,'full_four_selected_sources_and_used_primary_complete_proof_bodies_read':True,'additional_full_primary_finite_image_cardinality_provider':ref(provider),'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':9,'public_name_count':10,'entire_current_literal':literal,'entire_prospective_literal':prospective,'whole_unit_decisions':{'primer-linalg.html::node-191':{'entire_current_literal_read':True,'current_whole_semantic_approved':False,'current_missing_requirements':['The printed side/reciprocal cutting formulas need s>=0,tau>0,d>=1. The exact proposed opening supplies these domains; no zero-radius finite cover or ordinary zero-dimension cutting is inferred.'],'entire_prospective_literal_and_context_read':True,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact_proposal_application_and_independent_narrow_parser':True}},'all9_exact_component_scopes_approved':True,'component_missing_requirements':[],'arbitrary_side_center_cube_and_isometric_image_half_diagonal_and_corner_attainment_derived':True,'actual_clamped_ambient_centers_distance_nonincrease_cardinality_and_least_cover_equivalence_derived':True,'counts_64_and1099511627776_are_grid_construction_counts_not_claimed_optimal_covering_values':True,'generic_full_sampled_margin_m0_minus_L_tau_on_domain_derived':True,'independent_exact_Fraction_ceiling_count_and_projection_fixture_verified':True,'old_Grid14_full_peer_body_time_and_own_scope_preserved':q['old_Grid14_full_component_peer_original_scope_body_time_unchanged'],'original_true_source_and_all9_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'genuine_original_author_preparation_sidecar':ref(side),'current_owner_pending_row_preserved_unchanged':q['actual_installed_owner31_pending_row'],'no_other_parent_algorithm_infinite_dimension_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_key':'primer-linalg.html::node-191','theorems':9,'current_whole':False,'prospective_whole':True,'errors':[]}))
