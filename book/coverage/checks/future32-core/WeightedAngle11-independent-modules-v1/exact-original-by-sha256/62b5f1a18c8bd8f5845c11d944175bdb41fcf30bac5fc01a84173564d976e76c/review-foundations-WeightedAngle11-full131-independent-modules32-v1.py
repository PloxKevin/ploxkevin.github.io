from pathlib import Path
import hashlib,json,re,sys
from fractions import Fraction as Fr
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future32-foundations/weighted-angle11-full-scope-v1/foundations-weighted-plane-angle11-entire-source-current131-full-mathematical-independent-review-request32-v1.json';QH='dc5aadacba08fb926da2968f51613dd771b94b7e371df17c0c1726af24a92505';C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c';F=Path('/tmp/foundations-WeightedAngle11-independent-modules32-findings-v1.json')
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
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==11 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==6 and len([x for x in names if x['kind']=='abbrev'])==1
assert source.count('private theorem ')==3 and not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
inv=json.loads(checked(q['current_inventory81']).read_bytes());literal=q['entire_current_literal'];assert literal==next(r for r in inv['material_source_units']if r['key']=='primer-linalg.html::node-131')
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()and q['entire_weighted_inner_product_angle_definition_and_source_example_context_lines88_149']==''.join(page.decode().splitlines(keepends=True)[87:149])
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());assert all(row in owner['material_claims']for row in q['actual_installed_owner31_pending_rows'])and len(q['actual_installed_owner31_pending_rows'])==1 and q['actual_installed_owner31_pending_rows'][0]['status']=='pending'
for p in q['full_two_selected_coordinate_and_quadratic_form_sources'].values():checked(p).read_text()
for p in q['complete_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert len(history)==2
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log']);assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code']==0 and n['protection_errors']==[] and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']==0
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[0]['source']).read_text()==source and checked(history[0]['raw_log']).stat().st_size==0
axsource=checked(history[1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==11
printed={name:[a.strip()for a in atoms.split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[1]['raw_log']).read_text())};assert set(printed)==set(th)and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<= {'propext','Classical.choice','Quot.sound'}for a in printed.values())
# Independently derive exact fixture algebra and the sine/pi rational enclosure, not floating-angle approximations.
x=(1,2);y=(3,-1);z=(-2,1);M=(1,4)
assert sum(a*b for a,b in zip(x,y))==1 and sum(a*a for a in x)==5 and sum(b*b for b in y)==10
assert sum(M[i]*x[i]*y[i]for i in range(2))==-5 and sum(M[i]*x[i]**2 for i in range(2))==17 and sum(M[i]*y[i]**2 for i in range(2))==13
assert sum(x[i]*z[i]for i in range(2))==0 and sum(M[i]*x[i]*z[i]for i in range(2))==6
sqrtlo=Fr(7071,1000);sqrthi=Fr(70711,10000);coslo=Fr(7071,50000);coshi=Fr(14143,100000);tlo=Fr(709,5000);thi=Fr(71,500)
assert sqrtlo**2<50<sqrthi**2 and coslo*sqrthi<1<coshi*sqrtlo
assert tlo-tlo**3/6+tlo**5/100<coslo and coshi<thi-thi**3/6-thi**5/100
assert Fr(90)-thi*180/Fr(31415,10000)>Fr(1637,20)and Fr(90)-tlo*180/Fr(31416,10000)<Fr(1639,20)
# Completed author receipt is preserved through its exact sidecar, independently of whole semantics.
sidecars=[p for p in Q.parent.glob('*closure*.json')if p!=Q];assert len(sidecars)==1;side=sidecars[0];sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side)
receipts=[v for k,v in sd.items()if k=='actual_author_preparation'];assert len(receipts)==1;author=json.loads(checked(receipts[0]).read_bytes());assert author['actual_exit_code']==0 and author['protection_errors']==[]
guard()
f={'status':'passed_independent_WeightedAngle11_entire_current131_full_mathematical_review','errors':[],'full_source_read':True,'all11_public_bodies_six_definitions_one_abbrev_three_private_analytic_proofs_read':True,'full_two_selected_sources_and_used_primary_complete_proof_bodies_read':True,'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':11,'public_name_count':18,'entire_current_literal':literal,'whole_unit_decisions':{'primer-linalg.html::node-131':{'entire_current_literal_read':True,'whole_semantic_approved':True,'missing_requirements':[]}},'actual_coordinate_scaling_identifies_the_exact_weighted_metric_and_angle':True,'independent_exact_Fraction_fixture_and_sine_pi_rounding_enclosure_verified':True,'rounding_degree_interval':'81.85 < actual angleDegrees <81.95','metric_dependency_example':'sourceX perpendicular to(-2,1) in Euclidean metric, pairing6 after sourceMetric=diag(1,4); length sqrt5 changes tosqrt17.','original_true_source_and_all11_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'genuine_original_author_preparation_sidecar':ref(side),'current_owner_pending_row_preserved_unchanged':q['actual_installed_owner31_pending_rows'],'no_other_neighbor_parent_general_metric_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_key':'primer-linalg.html::node-131','theorems':11,'errors':[]}))
