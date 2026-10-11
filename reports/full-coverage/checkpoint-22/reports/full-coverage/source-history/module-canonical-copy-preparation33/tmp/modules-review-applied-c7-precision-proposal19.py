from pathlib import Path
import json,hashlib,datetime,shutil,sys,importlib.util
R=Path('/home/oxrexkevin/SafetyBased')
def p(x):return Path(x) if Path(x).is_absolute() else R/x
def H(x):return hashlib.sha256(p(x).read_bytes()).hexdigest()
proposal='/tmp/applied-coverage-c7-precision-proposal19.json'
assert H(proposal)=='cce3ba4e77567bc91871cecb1ebc5a4698d8a779c8ece7123d42bb9925bb9bef'
d=json.loads(p(proposal).read_text());source=d['source'];old=p(source).read_bytes();assert H(source)==d['source_sha256_before'];new=old
for rep in d['replacements']:
 assert new.count(rep['before'].encode())==rep['count']==1
 new=new.replace(rep['before'].encode(),rep['after'].encode(),1)
assert hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']
reverse=new
for rep in reversed(d['replacements']):reverse=reverse.replace(rep['after'].encode(),rep['before'].encode(),1)
assert reverse==old and old.count(b'\n')==new.count(b'\n')
assert p(d['source_bytes_before_snapshot']).read_bytes()==old
assert p(d['source_bytes_proposed_after_snapshot']).read_bytes()==new
for src,sha in d['actual_proof_source_sha256'].items():assert H(src)==sha
for e in d['actual_standalone_evidence']:
 assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']
 row=json.loads(p(e['compiler_manifest']).read_text());assert row==e['raw_execution_record']
 assert row['exit_code']==0 and H(row['source'])==row['sha256_before']==row['sha256_after']
 assert H(row['log'])==row['log_sha256'] and (p(row['log']).stat().st_size==0)==e['raw_log_is_empty']
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode());assert len(A.nodes)==len(B.nodes)
assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
sim=Path('/tmp/modules-independent-c7-precision19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for f in (R/'SafeLearning').glob('*.html'):shutil.copyfile(f,sim/'SafeLearning'/f.name)
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('modules_independent_C7_inventory19',R/'book/inventory_claims.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);g.ROOT=sim;g.OUT=sim/'book/coverage';g.inventory()
I=json.loads(p(d['inventory_at_preparation']).read_text());assert H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']
np=g.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts'];delta={}
for typ in ['exercises','material_source_units']:
 a={x['key']:x for x in I[typ]};b={x['key']:x for x in N[typ]};assert a.keys()==b.keys();delta[typ]=[]
 for key,x in a.items():
  y=b[key];assert x.keys()==y.keys()
  for field in x:
   if field not in ['source_sha256','source_text','text_sha256']:assert x[field]==y[field],(key,field)
  if x['source_text']!=y['source_text']:delta[typ].append(key)
  else:assert x['text_sha256']==y['text_sha256']
  if x['source']!=source:assert x==y
assert delta=={'exercises':['primer-probability.html::exercise-44'],'material_source_units':['primer-probability.html::node-1840','primer-probability.html::node-1841']}
cm='reports/full-coverage/checkpoint-18-manifest.json';C=json.loads(p(cm).read_text());protected={}
for f,row in C['proof_files'].items():
 protected[f]=row['sha256'];assert H(f)==row['sha256']
 for f,sha in row['evidence_sha256'].items():protected[f]=sha;assert H(f)==sha
for f,sha in C['frozen_inputs_sha256'].items():assert H(str(Path(C['snapshot'])/f))==sha
assert len(C['proof_files'])==490 and len(protected)==565 and len(C['frozen_inputs_sha256'])==2431
held=json.loads(Path('/tmp/modules-future19-held-work-index-v6.json').read_text())
for f,sha in held['held_pre33_metadata_sha256'].items():assert H(f)==sha
z=dict(schema_version=1,status='approved_narrow_read_only_precision_proposal',reviewer='/root/modules_resume',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=proposal,proposal_sha256=H(proposal),original_preparation_time_preserved=d['prepared_at_utc'],source=source,source_sha256_before=H(source),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=d['inventory_at_preparation'],inventory_sha256=d['inventory_sha256_at_preparation'],exact_substitutions=d['replacements'],fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-applied-c7-precision-proposal19.py'],actual_exit_code=0,simulated_inventory=str(np),simulated_inventory_sha256=H(np),counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,exact_forward_reverse_source_bytes=True),proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],mathematical_review=[
 dict(clause='Beta coverage mean/variance and standard deviation',decision='approved_precision_qualification',declarations=['SafeLearning.CompleteAppliedCoverageBeta.actual_beta_coverage_mean_variance_and_test_noise_moment','SafeLearning.CompleteAppliedCoverageBetaCDF.actual_beta_variance_and_standard_deviation_have_the_source_roundings'],reason='The actual normalized Beta18,2 density, its true polynomial integrals, all natural moment integrability and variance identity derive mean9/10, variance3/700 and E[C(1-C)]=3/35. Nearest-place bounds prove .00429 and .065 are approximations; the variance is strictly unequal to .00429. Replacing only these display values with exact quantities plus approximation signs is correct.'),
 dict(clause='Strict probability C<.8',decision='approved_precision_qualification',declarations=['SafeLearning.CompleteAppliedCoverageOrderStatistic.actual_second_largest_strict_threshold_is_at_least_eighteen_below','SafeLearning.CompleteAppliedCoverageBetaCDF.actual_beta_low_coverage_probability_is_the_literal_binomial_polynomial','SafeLearning.CompleteAppliedCoverageBetaCDF.actual_beta_low_coverage_probability_has_the_printed_rounding'],reason='The true second-largest event is exactly at least18 of19 scores below the threshold. The genuine Beta strict CDF equals19(.8)^18(.2)+(.8)^19. Its error from.083 is strictly below.0005 and its strict non-equality is proved; the approximation sign corrects the display without changing the event or informal about-one-in-twelve interpretation.'),
 dict(clause='Finite fresh-test total variance and its one-percent addition',decision='approved_exact_fraction_and_final_rounding',declarations=['SafeLearning.CompleteAppliedCoverageFreshTests.actual_every_fixed_coverage_has_a_derived_binomial_fresh_test_count','SafeLearning.CompleteAppliedCoverageFreshTests.actual_fresh_test_product_experiment_derives_its_mean_and_variance','SafeLearning.CompleteAppliedCoverageScoreTestMoments.actual_iid_raw_tests_have_the_derived_conditional_binomial_law_and_moments','SafeLearning.CompleteAppliedCoverageBetaCDF.actual_two_thousand_test_variance_expression_and_exact_one_percent_addition','SafeLearning.CompleteAppliedCoverageBetaCDF.actual_measured_variance_square_root_has_the_source_rounding'],reason='Actual probability product measures and genuine conditional test-section integrals yield variance3/700+(3/35)/2000=303/70000. The extra term divided by calibration variance is exactly1/100. The rounded intermediate decimals are not substituted as exact moments; only the final variance and standard deviation use certified approximation signs.'),
 dict(clause='Unchanged iid continuous-score scope',decision='read_unchanged_not_whole_promoted',declarations=['SafeLearning.CompleteAppliedCoverageContinuousTransform.actual_continuous_cdf_probability_integral_transform_has_the_true_uniform_law','SafeLearning.CompleteAppliedCoverageContinuousTransform.actual_iid_arbitrary_continuous_score_cdf_coverage_has_the_genuine_beta_law'],reason='The probability-integral transform derives the actual uniform law for any continuous CDF, monotone CDF commutes with the genuine second-largest statistic, and the Beta coverage law is derived rather than assumed. These justify the arithmetic context. The arbitrary raw-score full calibration/fresh-test product consequence and independent whole C7 review remain separate; this precision proposal does not promote the whole exercise.')],protected_selection_integrity=dict(manifest=cm,sha256=H(cm),selected_proofs=490,source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,held_modules_metadata_exact=True),missing_clauses=[],limits=['TMP-only during explicit HOLD33; no live HTML/inventory/coverage/index mutation or publication.','Approval covers the exact two paragraph precision replacements. Root authorization/serialization and fresh actual corrected-source whole review remain separate.','All seven genuine actual-zero source/compiler/rawlog records checked; Beta, UniformLaw and ContinuousTransform nonempty warning logs retained exactly. No new Lean or browser execution inferred.','No additional raw-score joint law, rank theorem or whole original C7 conclusion inferred by association.'])
out=Path('/tmp/modules-c7-precision-independent-modules-proposal-review19.json');assert not out.exists();out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n')
assert p(source).read_bytes()==old and H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation'];print(out,H(out))
