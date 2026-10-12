from pathlib import Path
import hashlib,json,re,sys
from fractions import Fraction as Fr
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/signed-distance-Hausdorff10-full-scope-v1/foundations-signed-distance-Hausdorff10-entire-source-current205-component-prospective205-whole-independent-review-request32-v1.json';QH='db97682886327f29ae087ced28bc03e4544a7cfe1ab37fa7411aef421ee9fc08';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-Signed10-independent-modules32-findings-v1.json')
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
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==12
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==10 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==2
assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
inv=json.loads(checked(q['current_inventory81']).read_bytes());literal=q['entire_current_literal'];assert literal==next(r for r in inv['material_source_units']if r['key']=='primer-linalg.html::node-205')
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()and q['full_current_metric_signed_distance_Hausdorff_context_lines213_239']==''.join(page.decode().splitlines(keepends=True)[212:239])
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());assert q['actual_installed_owner31_pending_row']in owner['material_claims']and q['actual_installed_owner31_pending_row']['status']=='pending'
for p in q['full_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert [r['actual_exit_code']for r in history]==[0,0]
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log']);assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code'] and n['protection_errors']==[] and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']==2
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[0]['source']).read_text()==source
axsource=checked(history[-1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==10
printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[-1]['raw_log']).read_text())};assert set(printed)==set(th)and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<= {'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Entire prospective proper-closed domain and actual prior Module7 sign context, not an infinite-return level-set theorem.
prospective=q['exact_planned_prospective_domain_qualified_literal'];assert prospective['key']==literal['key']
rep=q['unnumbered_exact_planned_replacements'];assert rep==[{'before':'A signed distance to a closed set equals','after':'For a closed set $C$ with $C\\ne\\emptyset$ and $C^c\\ne\\emptyset$, a signed distance equals'}]
assert prospective['source_text']==literal['source_text'].replace(rep[0]['before'],rep[0]['after'])
vp=checked(q['full_current_Source81_viability_local_convention_context']).read_text();assert q['actual_current_viability_signed_distance_and_positive_safety_side_lines140_147']==''.join(vp.splitlines(keepends=True)[139:147])
assert 'for a nonempty closed failure set with nonempty complement' in vp and 'whose positive level certifies a safety margin' in vp
# Independently verify exact directed interval maximum: B=[0,2] point2 has distance1 to A=[0,1]; clamp min(x,1) realizes every upper bound1.
for x in [Fr(0),Fr(1,3),Fr(1),Fr(3,2),Fr(2)]:
 y=min(x,Fr(1));assert Fr(0)<=y<=Fr(1)and abs(x-y)<=1
assert Fr(2)-Fr(1)==1
# Completed author receipt is preserved through its exact sidecar, independently of whole semantics.
sidecars=[p for p in Q.parent.glob('*closure*.json')if p!=Q];assert len(sidecars)==1;side=sidecars[0];sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side)
receipts=[v for k,v in sd.items()if k=='actual_original_native'];assert len(receipts)==1;author=json.loads(checked(receipts[0]).read_bytes());assert author['actual_exit_code']==0 and author['protection_errors']==[]
guard()
f={'status':'passed_independent_SignedDistanceHausdorff10_full_current205_components_and_prospective_whole','errors':[],'full_source_read':True,'all10_public_bodies_two_definitions_read':True,'full_used_primary_complete_infDist_closure_Hausdorff_compact_supremum_proof_bodies_read':True,'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':10,'public_name_count':12,'entire_current_literal':literal,'entire_prospective_literal':prospective,'whole_unit_decisions':{'primer-linalg.html::node-205':{'entire_current_literal_and_context_read':True,'current_whole_semantic_approved':False,'current_missing_requirements':['The finite real signed-distance construction requires nonempty closed C and nonempty complement for zero iff boundary; current205 omits these proper/nonempty qualifications. Full-space real-distance totalization countermodel is explicit.'],'entire_prospective_literal_and_context_read':True,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact_proposal_application_and_independent_narrow_parser':True}},'all10_exact_component_scopes_approved':True,'component_missing_requirements':[],'actual_two_sides_zero_iff_frontier_and_both_strict_nonstrict_difference_sets_derived':True,'actual_viability_convention_bound':'For failure C=X_F, the displayed difference dist(x,C)-dist(x,Ccomplement) is positive outside failure. Its negative is positive on interior C when C is interpreted as the safe region. Both local conventions are supported; no infinite-horizon value level-set identification is derived.','actual_nonempty_compact_Hausdorff_max_of_two_true_real_suprema_derived':True,'actual_interval_Hausdorff_distance1_derived_and_independently_verified':True,'real_totalization_countermodel_not_extended_infinite_distance_counterexample':True,'original_true_source_and_all10_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'genuine_original_author_preparation_sidecar':ref(side),'author_wrapper_historical_Cube9_description_observation':'Completed author sidecar preserves the inherited Cube9 wrapper description while actual command/helper/request and findings bind signed10; no false failure or rerun is inferred.','current_owner_pending_row_preserved_unchanged':q['actual_installed_owner31_pending_row'],'already_proved197199209_supplementary_eight_append_bodies_excluded':True,'no_other_parent_trajectory_value_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_key':'primer-linalg.html::node-205','theorems':10,'current_whole':False,'prospective_whole':True,'errors':[]}))
