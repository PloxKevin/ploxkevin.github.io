from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
ROOT=Path('/home/oxrexkevin/SafetyBased');SOURCE=Path('/tmp/foundations-scalar-calculus25-trial4.lean');OUT=Path('/tmp/foundations-scalar-calculus25-three-literal-full-source-review-request-v1.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
R=lambda p:json.loads(Path(p).read_text())
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(ROOT))if p.is_relative_to(ROOT)else str(p),'sha256':H(p)}
inventory=R(ROOT/'book/coverage/inventory-after-correction52.json');ledger=R(ROOT/'book/coverage/foundations.json');actual=R(SOURCE.with_suffix('.json'))
assert actual['actual_exit_code']==0 and H(SOURCE)==actual['source_sha256_before']==actual['source_sha256_after']=='7d24107b1224f26221cefece2cd054070eb78f4d6f2bfae2527707d477b49382'
assert H(ROOT/'book/coverage/inventory.json')==H(ROOT/'book/coverage/inventory-after-correction52.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert H(ROOT/'book/coverage/foundations.json')=='e3ff8460281d2a745c6def2d007b6465a1b5c352a1e14d90d486dec64835982b'
names=re.findall(r'^theorem\s+(\w+)',SOURCE.read_text(),re.M);assert len(names)==14
ns='SafeLearning.CompleteFoundationsScalarCalculusMaterial25.'
groups=[
 {'id':'generic_weighted_sum_and_product_rules','lean_declarations':[ns+names[0],ns+names[1]],'hypotheses':['Real f,g actually HasDerivAt at the point; a,b fixed real constants.'],'reason':'Arbitrary-function true derivative rules with every contribution retained, not a single fixture.'},
 {'id':'literal_square_times_exponential_and_exact_three_e_value','lean_declarations':[ns+names[3],ns+names[4]],'hypotheses':['Literal t²exp(t) on all real t.'],'reason':'True HasDerivAt 2t exp(t)+t²exp(t) everywhere and exact ordinary derivative3 exp1 at1.'},
 {'id':'generic_chain_and_exact_affine_square_outer_inner_and_twelve','lean_declarations':[ns+names[2],ns+names[5],ns+names[6],ns+names[7]],'hypotheses':['Outer f differentiable at g(x), inner g differentiable at x; literal affine-square example on R.'],'reason':'True generic composition derivative, explicit outer2(2t+1)/inner2, full4(2t+1), exact12 at1.'},
 {'id':'frozen_partial_coordinate_and_entire_curve_velocity','lean_declarations':[ns+names[10],ns+names[11]],'hypotheses':['Fréchet differentiable f at the actual coordinate-update or curve point and genuine differentiable curve; finite real coordinates or a real normed vector space.'],'reason':'Function.update freezes every coordinate except i and its actual derivative is Pi.single i1; arbitrary curve velocity passes through the entire Fréchet derivative. These are exactly the conditional derivative conventions in the source, with no C1 converse asserted.'},
 {'id':'literal_shifted_square_and_exp_twice_derivatives','lean_declarations':[ns+names[8],ns+names[9]],'hypotheses':['Literal (t−1)² and exp(2t), all real t.'],'reason':'True global HasDerivAt2(t−1) and2 exp(2t).'},
 {'id':'literal_halfline_boundary_unique_minimum_and_nonstationary_boundary','lean_declarations':[ns+names[12],ns+names[13]],'hypotheses':['Minimize exactly (t−2)² over t≤1.'],'reason':'Actual IsMinOn at1/value1, equality iff t1 and strict larger value for every t<1, plus true ordinary derivative−2 at boundary. The optimum is not substituted from another rhs/function fixture.'}]
units=[]
mapping={152:[0,1],154:[2,3],166:[4,5]}
for node,ids in mapping.items():
 key='primer-optimization.html::node-'+str(node);row=next(x for x in inventory['material_source_units']if x['key']==key)
 old=[x for x in ledger['material_claims']if key in x['source_unit_keys']];assert old and any(x['status']=='pending'for x in old)
 units.append({'entire_inventory_record':row,'entire_original_held24_ledger_claims':old,'proposed_precise_groups':[groups[i]for i in ids],'owner_proposal_only':True,'instructions':'Assess every literal clause and full context independently; approve the whole unit only if these genuine bodies match every mathematical assertion and its implicit differentiability/domain assumptions. Learning instructions may be scoped as instructions, but do not drop embedded mathematical claims.'})
history=[]
for n in range(1,5):
 stem=Path('/tmp/foundations-scalar-calculus25-trial'+str(n));d=R(stem.with_suffix('.json'))
 assert d['actual_exit_code']==(0 if n==4 else 1)
 artifacts=[stem.with_suffix('.lean'),stem.with_suffix('.json'),stem.with_suffix('.log'),Path(str(stem)+'-source.lean'),Path('/tmp/run-'+stem.name+'.py')]
 for p in artifacts:assert p.is_file()
 assert H(stem.with_suffix('.lean'))==H(Path(str(stem)+'-source.lean'))==d['source_sha256_before']==d['source_sha256_after']
 assert H(stem.with_suffix('.log'))==d['raw_log_sha256']
 history.append({'trial':n,'actual_exit_code':d['actual_exit_code'],'actual_record':ref(stem.with_suffix('.json')),'entire_original_actual_record_and_time':d,'all_source_log_snapshot_runner_artifacts':[ref(p)for p in artifacts]})
html=ROOT/'SafeLearning/primer-optimization.html';context=''.join(html.read_text().splitlines(keepends=True)[92:160])
assert 'Sum and product:'in context and 'Chain rule:'in context and 'Check before continuing:'in context
data={'status':'future25_tmp_only_full_three_literal_source_review_request_with_actual_standalone0_and_original_failures_retained','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'preparation_helper':ref(Path(__file__)),'inventory':ref(ROOT/'book/coverage/inventory-after-correction52.json'),'current24_held_foundation_ledger':ref(ROOT/'book/coverage/foundations.json'),'actual_root24_integration':ref(ROOT/'reports/full-coverage/owner24-reviewed-candidate-integration-v1.json'),'source':ref(SOURCE),'entire_passed_source_and_all14_public_bodies':SOURCE.read_text(),'public_theorem_names':[ns+x for x in names],'material_units':units,'all_six_precise_proposed_groups':groups,'full_current_source_context':{'source':ref(html),'start_line':93,'end_line':160,'entire_context':context,'context_sha256':hashlib.sha256(context.encode()).hexdigest()},'actual_standalone':ref(SOURCE.with_suffix('.json')),'all_four_actual_trial_histories':history,'selected23_manifest':ref(ROOT/'reports/full-coverage/checkpoint-23-manifest.json'),'current24_installed_owner_current52_inventory_sha256':actual['current24_installed_owner_current52_inventory_sha256'],'current52_all31_assets_sha256':actual['current52_asset_sha256'],'no_named_or_canonical_execution':True,'coverage_complete':False,'scope':'Distinct future25 scalar calculus material only. Current24 owner/candidate/offer/source/selected proofs remain exact. Genuine failed1/2/3 and passed4 with two real style warnings are retained unchanged. No whole exercise, FTC/Taylor theorem or surrounding generic gradient/Hessian claim is inferred. Please write a unique TMP-only peer with complete individual decisions and every precise scope gap; do not amend the held24 ledger.'}
with OUT.open('x')as f:f.write(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'request':ref(OUT),'public_theorems':14,'whole_unit_requests':3,'actual_trial4_exit_code':0}))
