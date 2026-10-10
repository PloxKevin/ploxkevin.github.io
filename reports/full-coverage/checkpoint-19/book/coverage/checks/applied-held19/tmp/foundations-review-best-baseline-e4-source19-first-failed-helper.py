import copy,datetime,hashlib,json,pathlib,re
R=pathlib.Path('/home/oxrexkevin/SafetyBased')
def P(p):
 q=pathlib.Path(p);return q if q.is_absolute() else R/q
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
ip='book/coverage/inventory-after-correction33.json'
assert H(ip)=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
iv=json.loads(P(ip).read_text());source='SafeLearning/primer-rl-nn.html'
assert H(source)==iv['source_sha256'][source]
e=next(x for x in iv['exercises'] if x['key']=='primer-rl-nn.html::exercise-38')
units=[copy.deepcopy(next(x for x in iv['material_source_units'] if x['key']=='primer-rl-nn.html::node-'+str(n))) for n in [1926,1930,1931,1932,1933]]
proof={};evidence=[];audit_path='reports/full-coverage/lean-checkpoint-18/verification.json'
audit=json.loads(P(audit_path).read_text());assert audit['status']=='passed' and (audit['proof_file_count'],audit['theorem_count'])==(490,5190)
checks=[]
for name in ['Bandit','Baselines','BaselineDegenerate']:
 src=f'verification/lean/SafeLearning/CompleteApplied{name}.lean';mp=f'book/coverage/checks/applied-next/{name}.json'
 d=json.loads(P(mp).read_text());h=H(src)
 assert d['exit_code']==0 and d['sha256_before']==d['sha256_after']==h
 assert H(d['log'])==d['log_sha256']
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',P(src).read_text())
 assert audit['proof_sha256'][src]==h
 proof[src]=h;evidence.append(dict(file=src,sha256=h,compiler_manifest=mp,compiler_manifest_sha256=H(mp),actual_exit_code=0,raw_log_is_empty=not P(d['log']).read_bytes(),raw_execution_record=d))
 check=copy.deepcopy(next(x for x in audit['checks'] if x.get('module')=='SafeLearning.CompleteApplied'+name))
 assert check['exit_code']==0 and H(check['output_file'])==check['log_sha256']
 assert H(check['reused_from']['report'])==check['reused_from']['report_sha256']
 for p,hv in check['reused_from']['verified_local_import_sha256'].items():assert H(p)==hv
 checks.append(check)
hyp=[
 'The toy law is the actual PMF with p=sigmoid(theta), for finite real theta, so 0<p<1. Formal Fin2 index0 is source action1 with reward1; formal index1 is source action0 with reward0. The actual log-probability derivatives, not an arbitrary score fixture, give 1-p and -p.',
 'The general part(d) uses an arbitrary probability space, score and reward*score in L2, mean(score)=0, and strictly positive score second moment, exactly as printed. L2 and finite measure provide the needed first moments, squares and cross-product integrability. No finite support or reward boundedness is imposed on that general theorem.',
 'The source positive denominator is ordinary mathematical division. The separately read degenerate theorem proves score=0 almost everywhere and every baseline has zero variance if the second moment is0; its totalized ratio is not used to extend the printed positive-denominator formula.',
 'The final sentence describes squared-score weighting in this two-action example. The weights are p*(1-p)^2 and (1-p)*p^2: the less probable action has the larger absolute score and larger weight when p differs from1/2; at p=1/2 they tie. At the preceding p=.8 the rare action0 dominates. It does not assert that every arbitrary score/reward distribution has one identifiable rare action.',
 'Step5 is checked only for its literal mean-zero-score baseline-cancellation correspondence. No whole policy-gradient, trajectory interchange or advantage policy-improvement theorem is approved by that internal cross-reference.'
]
def ns(stem,names):return ['SafeLearning.CompleteApplied'+stem+'.'+n for n in names]
groups=[
 dict(id='actual-binary-policy-log-scores-and-unbiased-constant-baseline',source_clause='(a) Actual sigmoid law, both log scores, gradient atoms and mean p(1-p) for every baseline.',lean_declarations=ns('Bandit',['both_actual_log_probability_scores','finite_expectation_is_actual_integral','binary_expectation','actual_score_identity','any_constant_baseline_same_gradient'])+ns('Baselines',['unit_gradient_actual_mean']),reason='The actual PMF has the source two probabilities and rewards. Genuine HasDerivAt log-probability statements yield the two printed scores. The integral equals the finite expectation; the two atom products and cancellation give p(1-p) independently of b.'),
 dict(id='actual-second-moment-derivative-and-unique-zero-variance-baseline',source_clause='(b) Actual second moment and derivative, unique baseline1-p and constant gradient with minimal variance0.',lean_declarations=ns('Baselines',['finite_variance_is_actual_variance','unit_gradient_actual_second_moment','unit_gradient_second_moment_actual_derivative','unit_gradient_actual_variance','unit_gradient_optimal_baseline_constant','unit_gradient_unique_optimal_baseline']),reason='The exact weighted second moment is differentiated with HasDerivAt to2p(1-p)(b-(1-p)). The actual variance is p(1-p)(b-(1-p))^2; strict positive sigmoid factors give the unique minimizer. Both true action gradients at that minimizer equal p(1-p), hence actual variance0.'),
 dict(id='actual-point-eight-gradients-three-variances-and-ninefold-ratio',source_clause='(c) Actual p=.8, four gradient atoms, all three variances and exact factor9.',lean_declarations=ns('Baselines',['four_fifths_parameter','four_fifths_actual_variance_comparison']),reason='The source probability is instantiated at theta=log4, rather than presumed. Exact rational atoms1/5,0,1/25,16/25 and variances4/625,36/625,0 equal every finite decimal displayed here; the latter variance is exactly9 times the first.'),
 dict(id='arbitrary-law-L2-weighted-baseline-variance-quadratic-and-global-minimum',source_clause='(d) Actual arbitrary-law variance moment expansion, baseline-independent mean and unique score-squared-weighted optimum.',lean_declarations=ns('Baselines',['actual_general_baseline_mean','actual_baseline_variance_quadratic','actual_variance_minimizing_baseline','actual_general_score_weighted_baseline_formula','actual_general_gradient_variance_moment_formula','actual_general_score_weighted_variance_minimum','unit_score_squared_moments','actual_unit_score_weighted_baseline_ratio']),reason='The true L2 covariance/variance identities give the full printed quadratic with actual Bochner integrals. Mean-zero score removes the baseline from the mean. Completing the square proves a global unique minimizer for every constant baseline; the positive coefficient is derived from the exact positive second-moment assumption. The genuine toy moments then give the printed ratio1-p and its squared-score interpretation.')]
for g in groups:
 g.update(status='approved_precise_component',review_status='approved_precise_source_component',per_clause_reason=g.pop('reason'),hypotheses=hyp,missing_clauses=[])
 for d in g['lean_declarations']:
  assert any(x['name']==d and x['file'] in proof for x in audit['declarations'])
  assert set(audit['axiom_dependencies'][d])<=set(audit['allowed_standard_axioms'])
for u in units:u.update(status='proved',review_status='approved_complete_source',hypotheses=hyp,missing_clauses=[],per_unit_reason='All literal question and corresponding answer clauses are covered by the source-matched actual policy, moment, derivative, variance and arbitrary-probability-law theorem groups.')
prior='/tmp/foundations-future19-held-work-index-v18.json';pd=json.loads(P(prior).read_text())
for p,h in pd['held_current_metadata_sha256'].items():assert H(p)==h
mp='reports/full-coverage/checkpoint-18-manifest.json';m=json.loads(P(mp).read_text());paths={}
for p,row in m['proof_files'].items():
 assert H(p)==row['sha256'];paths[p]=row['sha256']
 for ep,h in row['evidence_sha256'].items():assert H(ep)==h;paths[ep]=h
for p,h in m['frozen_inputs_sha256'].items():assert H(R/m['snapshot']/p)==h
out=dict(schema_version=1,status='independent_full_source_review_passed',reviewer='/root/foundations_next',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_sha256={source:H(source)},inventory=ip,inventory_sha256=H(ip),proof_source_sha256=proof,actual_standalone_evidence=evidence,
 actual_checkpoint18_reused_kernel_evidence=dict(report=audit_path,report_sha256=H(audit_path),status='passed',proof_file_count=490,theorem_count=5190,actual_module_checks=checks,limits='Previously passed actual checkpoint18 audit reuses identical prior source/import kernel evidence; this semantic review claims no fresh compiler or kernel replay.'),
 records=[dict(exercise_key=e['key'],exercise_text_sha256=e['text_sha256'],source_text=e['source_text'],review_status='approved_complete_source',reviewed_clauses=groups,hypotheses=hyp,missing_clauses=[])],material_units=units,missing_clauses=[],
 checked_internal_attribution=dict(source=source,source_sha256=H(source),lines=[1907,1909,1910,1911],literal_title='Step 5: Subtracting a baseline changes nothing on average',reason='Directly read the local state-only baseline and zero-mean score passage. The binary baseline theorem proves the precise cancellation used by answer(a); no surrounding policy-gradient theorem is inferred.'),
 extra_degenerate_scope=dict(proof='verification/lean/SafeLearning/CompleteAppliedBaselineDegenerate.lean',reason='Read and rehashed as requested. Its zero-score-second-moment extension is not needed for the printed strictly positive-denominator domain and is not used to infer an ordinary zero-denominator ratio.'),
 preservation_check=dict(manifest=mp,manifest_sha256=H(mp),selected_proofs_checked=len(m['proof_files']),unique_selected_source_evidence_paths_checked=len(paths),frozen_inputs_checked=len(m['frozen_inputs_sha256']),all_exact=True),
 limits=['Full question/all four answers/all five physical units, all three protected proof files and the exact local Step5 attribution were independently read.', 'Baselines and Bandit raw standalone logs have genuine warnings; BaselineDegenerate standalone log is empty. Every source/record/raw-log and reused actual kernel identity was rehashed.', 'TMP only under unreleased HOLD33. No live coverage, source, inventory, ledger, builder, offer or neighboring theorem promotion.'])
q=P('/tmp/rl-best-baseline-e4-full-source-review19-v1.json');assert not q.exists();q.write_text(json.dumps(out,indent=2)+'\n')
print(q,H(q),'whole E4 +5 literal units approved')
