import json,hashlib,pathlib,sys,datetime
root=pathlib.Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0,str(root/'book/coverage'))
from lean_names import declarations
h=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(p),'sha256':h(p)}
invpath=root/'book/coverage/inventory-after-correction48.json'
inv=json.loads(invpath.read_text())
assert h(invpath)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
ex=next(r for r in inv['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')
assert h(root/ex['source'])==ex['source_sha256']
unitkeys=[f'lyapunov-mpc.html::node-{i}' for i in [1393,1397,1399,1401,1403]]
units=[next(r for r in inv['material_source_units'] if r['key']==k) for k in unitkeys]
rows=[]
for name,last in [('ScenarioNumbers',5),('ValidationBridge',2)]:
 source=pathlib.Path('/tmp/CompleteLyapunov'+name+'23.lean')
 stem='/tmp/applied-lyapunov-'+('scenario-numbers' if name=='ScenarioNumbers' else 'validation-bridge')+'23-trial'
 record=pathlib.Path(stem+str(last)+'.json')
 r=json.loads(record.read_text());assert r['actual_exit_code']==0
 assert h(source)==r['source_sha256_before']==r['source_sha256_after']==h(r['source_file'])
 assert h(r['raw_log_file'])==r['raw_log_sha256']
 assert h(r['runner_file'])==r['runner_sha256']
 hist=[]
 for n in range(1,last):
  p=pathlib.Path(stem+str(n)+'.json');rr=json.loads(p.read_text())
  assert rr['actual_exit_code']!=0
  assert h(rr['source_file'])==rr['source_sha256_before']==rr['source_sha256_after']
  assert h(rr['raw_log_file'])==rr['raw_log_sha256']
  hist.append({'record':ref(p),'entire_original_record':rr,'source_snapshot':ref(rr['source_file']),'raw_log':ref(rr['raw_log_file'])})
 rows.append({'proof_source':ref(source),'actual_standalone_record':ref(record),'entire_actual_record':r,'source_snapshot':ref(r['source_file']),'raw_log':ref(r['raw_log_file']),'public_declarations':declarations(source.read_text()),'historical_failed_trials':hist,'compiler_scope':'One actual standalone execution of the immutable TMP source; no named/shared-package build, checkpoint22 execution or aggregate claim.'})
manifestpath=root/'reports/full-coverage/checkpoint-21-manifest.json'
m=json.loads(manifestpath.read_text())
errors=[]
for p,r in m['proof_files'].items():
 if h(root/p)!=r['sha256']:errors.append(p)
assert not errors
imports=[]
for name in ['CompleteAppliedDiscountedHorizons','CompleteFoundationsExponentialNumerics','CompleteAppliedBinomialModel','CompleteAppliedValidation','CompleteAppliedConcentration','CompleteAppliedFailureCounts']:
 p='verification/lean/SafeLearning/'+name+'.lean';r=m['proof_files'][p]
 ev=[]
 for f,sha in r['evidence_sha256'].items():
  assert h(root/f)==sha
  ev.append({'file':f,'sha256':sha})
 imports.append({'source_file':p,'sha256':r['sha256'],'retained_selected21_row':r,'existing_evidence':ev,'evidence_scope':'Retained selected actual source/compiler evidence; no new execution of this dependency is asserted.'})
names=[d['name'] for r in rows for d in r['public_declarations'] if d['kind'] in ['theorem','lemma']]
print('theorems',len(names),'files',len(rows))
ns='SafeLearning.CompleteLyapunovScenarioNumbers23.'
nb='SafeLearning.CompleteLyapunovValidationBridge23.'
groups=[
 {'id':'genuine_binomial_probability_and_recurrence','lean_declarations':[ns+n for n in ['actual_independent_count_lower_tail_probability','actual_binomial_tail_successor_identity','actual_binomial_tail_nonincrease','actual_ten_term_tail_antitone_from_nine']], 'reason':'Actual independently sampled finite event counts have the literal binomial lower-tail probability. The successor identity is proved from Pascal and finite sums; nonincrease is derived rather than assumed. This proves the binomial expression, not the scenario optimizer support theorem.', 'hypotheses':['Arbitrary probability space; measurable finite independent equal-probability events for the probability identity.','0≤p≤1 and m≤n for the successor nonincrease.']},
 {'id':'dimension_one_exact_cutoff_and_source_roundings','lean_declarations':[ns+n for n in ['actual_dimension_one_reduction','actual_one_dimensional_boundary_and_rounding','actual_least_one_dimensional_sample_size','actual_one_dimensional_logarithmic_threshold']]+[nb+'actual_source_logarithm_roundings_and_strict_numerical_inequalities'], 'reason':'All natural sample counts satisfy the exact cutoff iff N≥135, with the logarithmic iff and rigorous source roundings. Actual logarithms and actual ratio differ from the printed finite decimals.', 'hypotheses':['Source ε=1/20 and β=1/1000; N is a natural number.']},
 {'id':'dimension_ten_first_crossing_with_certified_roundings','lean_declarations':[ns+n for n in ['actual_ten_variable_boundary_enclosures','actual_ten_variable_source_roundings_and_crossing','actual_least_ten_variable_sample_size']], 'reason':'True ten-term binomial tails have rational enclosures and the printed significant-figure roundings at580/581. The proof covers every natural N including N<9 via a nonnegative zero-count term; first crossing is genuine, not a finite search assumption.', 'hypotheses':['d=10; ε=1/20; β=1/100000.']},
 {'id':'given_variable_count_sufficient_formula_and_comparison','lean_declarations':[ns+n for n in ['actual_common_lyapunov_variable_count','actual_logarithm_five_decades','actual_sufficient_threshold_enclosure_and_least_integer']], 'reason':'Substitutes dx2/du1 into the given n_k formula, proves exact log100000 relation and genuine ceil861, and certifies about48% more samples than581. It does not prove the general Chernoff-sufficient scenario theorem.', 'hypotheses':['Use the n_k=2dx²+dxdu and sufficient2/ε formula attributed by the page.']},
 {'id':'validation_exact_rule_and_least_integer','lean_declarations':[ns+n for n in ['actual_validation_thresholds_rounding_and_ceilings','actual_validation_exponential_bound_iff_threshold','actual_least_validation_size']], 'reason':'Corrected rule gives5757; misprinted first-power rule gives116; the corrected count is equivalent to the exact one-sided exponential upperbound≤.01 for every natural count.', 'hypotheses':['Fixed tolerance1/50 and confidence parameter1/100.']},
 {'id':'misprint_certified_lower_confidence_and_precision_gaps','lean_declarations':[ns+n for n in ['actual_misprinted_size_exponent_and_rigorous_rounding','actual_printed_decimal_equalities_are_false']], 'reason':'An actual exponential Taylor remainder yields .91137575<exp(-.0928)<.91137577. Its complement rounds to9% and is below9%; this is the lower confidence supplied by Hoeffding, not an upperbound on actual procedure confidence. The printed exact equalities are false.', 'hypotheses':['116 independent tests with source tolerance.02 when applying the one-sided Hoeffding inequality.']},
 {'id':'actual_fixed_iid_validation_population_guarantee','lean_declarations':[nb+n for n in ['actual_corrected_validation_samples_certify_the_population_lower_mean','actual_accepted_fixed_validation_certifies_point_nine_three']], 'reason':'A genuine centered bounded MGF and independent sum tail derive probability≥.99 for the population-lower event and the accepted-test implication. No generic procedure repeated-until-pass confidence is inferred.', 'hypotheses':['One fixed controller/fixed population mean; n≥5757.','Actual probability space, measurable independent test variables in[0,1] and genuine common expectation.']},
 {'id':'normalized_credible_probability_to_actual_posterior_guarantee','lean_declarations':[nb+n for n in ['actual_normalized_credible_region_transfers_stability_to_full_belief','actual_independent_normalized_posterior_validation_has_point_eight_eight_confidence']]+[ns+'actual_corrected_posterior_lower_bound_arithmetic'], 'reason':'Actual full belief and actual credible/stability intersection define the normalized population probability. With credible mass.95 and fresh independent Bernoulli samples of that true normalized probability, accepted validation gives full stability probability≥.8835≥.88 with confidence≥.99. The proof does not construct a GP derivative posterior or identify nonlinear stability with linearization stability.', 'hypotheses':['Fixed genuine posterior probability measure and measurable credible/stability events in the source use.','Credible probability mass is19/20.','Bernoulli validation laws have parameter exactly equal to credible∩stable probability divided by credible probability; independence is supplied, not inferred.','One accepted fixed batch n≥5757 with empirical success≥19/20.']}
]
assert set(names)==set(d for g in groups for d in g['lean_declarations'])
primary=[]
for p,scope,url in [
 ('sources/text/cg2008.txt','Assumption1/Proposition2.2/Theorem2.4 and Table2.2, lines160–305. The scenario optimizer/binomial upperbound remains a primary attributed result; arithmetic does not prove it.','https://epubs.siam.org/doi/10.1137/07069821X'),
 ('sources/text/2105.07668.txt','Assumption1/the initialization theorem/Section3.2 one-sided validation proof, lines180–335. Actual online primary arXivv2 PDF read. The source theorem contains the first-power tolerance and stated/proved posterior discrepancy; retained scope is a fixed fresh independent validation batch.','https://arxiv.org/pdf/2105.07668')]:
 primary.append({'source_file':p,'sha256':h(root/p),'primary_url':url,'direct_read_scope':scope})
material=[]
for r in units:
 gaps=[]
 if r['key'].endswith('1397'):gaps=['The printed chain uses false exact equality for rounded logarithms/fraction/ratio.','The general scenario-support/missed-region assertion is directly attributed to the primary scenario theorem, not proved by the new binomial count model.']
 if r['key'].endswith('1401'):gaps=['Printed exact equalities5756.5/115.1/.911 must be qualified as approximations.']
 if r['key'].endswith('1403'):gaps=['No actual GP derivative-posterior construction or nonlinear-system stability theorem is supplied; the precise fresh iid validation/credible-region mathematical component is proved under its explicit source assumptions.']
 material.append({'source_unit_key':r['key'],'entire_inventory_record':r,'unit_text_sha256':r['text_sha256'],'source_sha256':r['source_sha256'],'whole_unit_approved':False,'status':'numeric_and_probability_components_ready_for_independent_review','missing_clauses':gaps})
result={'status':'actual_tmp_two_source_quantitative_pack_ready_for_independent_literal_component_review','created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inventory':{'file':'book/coverage/inventory-after-correction48.json','sha256':h(invpath)},'exercise_key':ex['key'],'exercise_text_sha256':ex['text_sha256'],'entire_inventory_record':ex,'proof_rows':rows,'theorem_count':len(names),'approved_by_author_components':groups,'material_units':material,'primary_source_correspondence':primary,'selected21_dependency_rows':imports,'protected_selected_sources':{'manifest':'reports/full-coverage/checkpoint-21-manifest.json','manifest_sha256':h(manifestpath),'count':len(m['proof_files']),'errors':errors},'limits':['No working HTML/inventory/owner ledger/canonical coverage file has been written.','No named/shared-package build or aggregate23 execution is claimed.','No general Campi–Garatti optimizer theorem, full GP posterior construction, nonlinear stability guarantee or repeated-validation-until-pass coverage is promoted.','Original false finite-decimal equalities remain exact current48 source gaps.']}
p=pathlib.Path('/tmp/applied-lyapunov-scenario-validation23-two-source-readiness-v1.json');assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n')
print(str(p),h(p))
