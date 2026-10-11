from pathlib import Path
import datetime
import hashlib
import json
import sys

root=Path('/home/oxrexkevin/SafetyBased')
out=Path('/tmp/modules-landscape-explorer-evidence19-v1')
source=root/'SafeLearning/landscape.html'
inventory=root/'book/coverage/inventory-after-correction33.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
extraction=json.loads((out/'extraction-record.json').read_text())
harness=json.loads((out/'harness-results.json').read_text())
numeric=json.loads((out/'numeric-crosscheck.json').read_text())
underflow=json.loads((out/'allowed-slider-complete-tail-underflow.json').read_text())
intermediate=json.loads((out/'printed-intermediate-rounding.json').read_text())
inv=json.loads(inventory.read_text())
exercise=next(x for x in inv['exercises'] if x['key']=='landscape.html::exercise-19')
units=[x for x in inv['material_source_units'] if x['source']=='SafeLearning/landscape.html' and 724<=x['line']<=738]
assert sha(source)==extraction['source_sha256']==exercise['source_sha256']==sha(out/'landscape-source.html')
assert sha(out/'explorer-original.js')==extraction['original_iife_sha256']
assert sha(out/'explorer-instrumented.js')==extraction['instrumented_sha256']
for asset in numeric['assets_read_only_hashes']:
    assert sha(Path(asset['file']))==asset['sha256']
for case in harness['cases']:
    assert sha(Path(case['record']))==case['recordSHA256']
assert harness['aggregate']['episodes']==200000
assert harness['aggregate']['jointEstimate']==137711/200000
assert underflow['trace']['analyticEN']==0 and underflow['trace']['cmdpPass'] is False
assert all(term['implementedQ']==0 for term in underflow['terms'])
for name in ['harness-stderr.log','numeric-crosscheck-stderr.log','underflow-harness-stderr.log']:
    assert (out/name).read_bytes()==b''

record={
 'kind':'readonly_original_landscape_1_5_explorer_implementation_and_floating_point_execution_evidence',
 'created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'hold33_active':True,'promotion_authorized':False,
 'source_binding':{'file':str(source),'sha256':sha(source),'source_bytes':source.stat().st_size,
     'inventory_file':str(inventory),'inventory_sha256':sha(inventory),'exercise':exercise,'source_units':units},
 'implementation':{
   'unchanged_iife_line_range':[extraction['iife_first_line'],extraction['iife_last_line']],
   'unchanged_iife_sha256':extraction['original_iife_sha256'],
   'default_settings':{'k':.5,'sigma':.07,'T':40,'alpha':.9,'budget':1,'delta':.05,'seed_number':1},
   'exercise_settings':{'k':.5,'sigma':.1,'T':40,'goal':.8,'unsafe_condition':'x > 1'},
   'fixed_constants':{'N':200,'XG':.8,'XB':1,'TMAX':100},
   'sampling':'mulberry32 seed = 20260929 + seedNo * 7919; Box–Muller sqrt(-2 log u) cos(2 pi v); one 200 by 100 noise matrix cached per seed',
   'common_random_numbers':'Input events reuse the cached matrix. Only actual resample click increments seedNo and regenerates it. Shortened-horizon trajectory-prefix assertions passed for all 200 episodes.',
   'analytical_formula':'For t = 1..T: m = XG*(1-(1-k)^t); v = sigma^2*(1-(1-k)^(2t))/(1-(1-k)^2); Q((XB-m)/sqrt(v)); deterministic strict m>XB indicator when v=0.',
   'q_implementation':'Direct complementary-erf polynomial/exponential approximation, attributed by the local comment to Numerical Recipes erfcc. No call to a browser erf function; primary Numerical Recipes attribution or real-approximation error theorem was not independently checked in this task.',
   'sample_statistics':'Ns are counts of x>XB after steps 1..T. Joint fraction counts Ns>0. Ns mean SE is sample SD/sqrt(200); joint SE is sqrt(pHat*(1-pHat)/200). CVaR is worst tail of empirical Z with split boundary atom, VaR lower ceil(alpha*N)-th empirical quantile; Z includes initial safe state.',
   'verdict_semantics':'CMDP uses analytical floating expectation with explicit sigma>0 and d<=0 failure guard. Chance/risk/hard compare actual empirical statistics and render SAMPLE badges.',
   'original_vs_instrumented':'All DOM output digests agreed after every mirrored input/resample event in the recorded scenarios; instrumentation only exposed functions and copied existing local values.',
   'read_only_assets':numeric['assets_read_only_hashes']},
 'actual_executions':[
   {'command':'python3 /tmp/modules-landscape-explorer-extract19-v1.py','actual_exit_code':0,'artifact':'extraction-record.json'},
   {'command':'node /tmp/modules-landscape-explorer-harness19-v1.cjs','actual_exit_code':0,'stdout':'harness-stdout.log','stderr':'harness-stderr.log'},
   {'command':'python3 /tmp/modules-landscape-explorer-numeric-crosscheck19-v1.py','actual_exit_code':0,'stdout':'numeric-crosscheck-stdout.log','stderr':'numeric-crosscheck-stderr.log'},
   {'command':'node /tmp/modules-landscape-explorer-underflow-harness19-v1.cjs','actual_exit_code':0,'stdout':'underflow-harness-stdout.log','stderr':'underflow-harness-stderr.log'}],
 'numerical_clause_assessment':{
   'source_line_737_and_node':'landscape.html::node-1368, exact source/inventory bytes included above',
   'stationary':'Exact rational variance 1/75; binary64 sqrt gives .11547005383792516 and true standardized threshold sqrt(3). Float erfc tail .04163225833177522; expected stationary approximation at T=40 is 1.6652903332710087. The printed .1155, 1.732, .0416, 1.665 are appropriate individual rounded values using full precision before display.',
   'printed_intermediate_chain':intermediate,
   'printed_intermediate_caveat':'Literal equality of the printed rounded intermediates fails. Plugging .1155 into the tail gives .04167224885212909, rounding to .0417; the true stationary tail rounds to .0416. Similarly 40 times rounded .0416 is 1.664, whereas 40 times the true tail rounds to 1.665. Retain full precision and use approximation signs.',
   'transients':[term for term in numeric['exercise']['terms'] if term['t'] in [1,3,5,10]],
   'transient_assessment':'p1 is about 9.87e-10, strictly positive, so printed approximate zero is only a coarse approximation. p3=.0044, p5=.0256, p10=.0410 are correct four-decimal roundings of the full-precision marginals, not exact real equalities.',
   'expected_count':{'implemented_Q_sum':harness['cases'][1]['analyticEN'],
       'independent_math_erfc_sum':numeric['exercise']['mean_violating_steps'],
       'implemented_minus_reference':harness['cases'][1]['analyticEN']-numeric['exercise']['mean_violating_steps'],
       'assessment':'Both round to 1.484; neither equals the exact real expectation 1.484. Markov gives probability <= true EN, which exceeds 1 and is vacuous. The displayed <=1.484 is also vacuous since all probabilities are <=1; the rounded count should not be treated as an exact derived threshold.'},
   'empirical_joint_probability':harness['aggregate'],
   'joint_assessment':'137711/200000 = .688555 across seeds 1..1000 supports the rounded empirical statement about .69. The unchanged ordinary explorer has only 200 episodes per seed: seed1 .72, seed2 .64. A single seed is not promised to display .69. This is not an exact Gaussian probability evaluation or a certified confidence interval.',
   'defaults':{'analytic_EN':harness['cases'][0]['analyticEN'],'sample_mean':harness['cases'][0]['sampleMeanCount'],
       'joint_fraction_seed1':harness['cases'][0]['jointEstimate'],
       'assessment':'Default sigma=.07 differs from exercise sigma=.1. EN=.23221067 supports about .23 and seed1 fraction .18 supports about one in five. Original default CMDP PASS and chance/risk/hard SAMPLE FAIL were actually executed.'}},
 'cancellation_and_underflow':{
   'source_lines':[929,930,954,967,968,734,735],
   'actual_tail_samples':harness['tailValues'],
   'cancellation_threshold_for_explicit_1_minus_1_minus_Q':numeric['cancellation_threshold_for_forming_cdf_as_1_minus_math_erfc_tail'],
   'near_8_3':'Current Q(8.3) remains about 5.21e-17 and Q(9) about 1.13e-19; subtracting their CDF formed as 1-Q from 1 produces exact binary64 zero. About 8.3 is accurate for this tested rounding route; the exact threshold depends on the CDF implementation.',
   'attribution_limit':'The current page avoids 1-Phi in exactEN by calling its direct Q. Its comment describes a historical false-zero defect; no previous source version was executed in this task, so the historical event is not independently certified here.',
   'allowed_slider_complete_underflow':{'settings':{key:underflow['trace'][key] for key in ['k','sigma','T','budget','seedNo']},
       'terms':underflow['terms'],'raw_analytic_EN':underflow['trace']['analyticEN'],
       'CMDP_pass':underflow['trace']['cmdpPass'],
       'actual_display':'positive, below the double-precision range'},
   'underflow_assessment':'Direct Q avoids cancellation but does not avoid eventual underflow: Q(39)=0. For actual allowed sliders k=.05, sigma=.01, T=5, every computed tail and sum underflow to 0; mathematically all true tails are positive. The existing positivity formatting and explicit zero-budget failure guard handle this case correctly.',
   'literal_global_error_comment':'The local implementation comment claims relative error below 1.2e-7 for every z. That cannot literally be a global guarantee of its binary64 implementation: actual underflow returns 0 for a positive Gaussian tail, giving relative error 1. Real approximation accuracy and machine range must be distinguished.',
   'math_vs_implementation_at_zero':'The true Q(0)=1/2 by Gaussian symmetry; the current polynomial implementation gives .5000000150000002. The mathematical identity is correct, while the implementation is an approximation.'},
 'scope_limits':['No browser was launched; no rendering, layout, accessibility or complete page integration was tested.',
   'Strict fake DOM executes only the exact explorer IIFE and input/click listeners; components.js and surrounding page initialization were not executed.',
   'Fixed finite PRNG outputs are not proven iid exact Gaussian random variables. Nominal SE calculations do not establish independence or a certified coverage probability.',
   'Python math.erfc crosscheck uses host binary64 libm; rational moments are exact but probabilities are floating-point execution values.',
   'No new rigorous Lean numeric probability or rounding theorem was created. This evidence does not close whole Exercise1.5 mathematical coverage.',
   'No source, asset, inventory, coverage, live review metadata or selected/protected proof was modified; all created files are distinct TMP paths.'],
 'runtime':{'node':harness['node'],'python':sys.version},
 'evidence_files':[{'file':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(out.iterdir()) if p.is_file()],
 'harness_source_files':[{'file':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in [
   Path('/tmp/modules-landscape-explorer-extract19-v1.py'),Path('/tmp/modules-landscape-explorer-harness19-v1.cjs'),
   Path('/tmp/modules-landscape-explorer-underflow-harness19-v1.cjs'),Path('/tmp/modules-landscape-explorer-numeric-crosscheck19-v1.py'),Path(__file__)]],
 'all_recorded_bytes_freshly_checked':True,
 'final_readonly_verification':{'actual_exit_code':0,'source_and_referenced_assets_equal_snapshot_hashes':True,
     'all_case_record_hashes_match':True,'all_runtime_stderr_logs_empty':True}}
target=Path('/tmp/modules-landscape-explorer-implementation-review19-v1.json')
target.write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'review_file':str(target),'review_sha256':sha(target),'source_sha256':sha(source),
    'actual_node_exit_codes':[0,0],'episodes':harness['aggregate']['episodes'],'joint_fraction':harness['aggregate']['jointEstimate']}))
