from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/applied-gaussian-mixture24-complete401-full-source-review-request-v1.json')
OUT=Path('/tmp/applied-gaussian-mixture401-independent-foundations-full-source-review-v1.json')
cache={}
def H(p):
 p=Path(p);s=p.stat();key=(s.st_dev,s.st_ino,s.st_mtime_ns,s.st_size)
 if key not in cache:cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[key]
def path(s):
 p=Path(s);return p if p.is_absolute() else ROOT/p
def read(p):return json.loads(path(p).read_text())
def ref(p):return {'file':str(p),'sha256':H(path(p))}
def checked(r):assert H(path(r['file']))==r['sha256'];return read(r['file'])
assert not OUT.exists() and H(REQUEST)=='0f7857d4be2b9d991d429cd48cc8911388c566f73986d3e563a4b0d5f5a6c267'
j=read(REQUEST);unit=j['entire_inventory_record'];assert unit['key']=='primer-probability.html::node-401'
historical=ROOT/'book/coverage/inventory-after-correction51.json';assert H(historical)==j['current_inventory']['sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
current_bytes=(ROOT/'book/coverage/inventory.json').read_bytes();observed_current=json.loads(current_bytes)
for inv in [read(historical),observed_current]:assert next(r for r in inv['material_source_units'] if r['key']==unit['key'])==unit
assert H(ROOT/unit['source'])==unit['source_sha256']=='02779ca8a2499c347f73c0365000522e36ee93961bc68cf9d9fcff26a55e0a99'
for r in j['complete_source_contexts']:
 p=ROOT/r['file'];assert H(p)==r['sha256']
 assert ''.join(p.read_text().splitlines(True)[r['lines_start']-1:r['lines_end']])==r['exact_lines']
assert len(j['complete_source_contexts'])==4
sources=[];names=[]
for r in j['new_fixed_TMP_proof_sources']:
 p=path(r['file']);assert H(p)==r['sha256'] and p.read_text()==r['entire_source']
 s=r['entire_source'];assert not re.search(r'\b(sorry|admit)\b',s)
 ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
 actual_names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
 assert actual_names==r['public_theorem_names']
 sources.append(dict(r));names.extend(actual_names)
assert len(sources)==4 and len(names)==len(set(names))==26
assert [len(r['public_theorem_names']) for r in sources]==[6,10,2,8]
actual_passes=[]
for r in j['actual_TMP_standalone_passes']:
 a=checked(r);assert a==r['entire_actual_record'] and a['actual_exit_code']==0
 assert H(a['source'])==a['source_sha256_before']==a['source_sha256_after']==H(a['source_snapshot'])==a['source_snapshot_sha256']
 assert H(a['log'])==a['log_sha256'] and H(a['actual_runner'])==a['actual_runner_sha256']
 assert a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['source'] in [r['file'] for r in sources] and a['actual_command'][-1]==a['source']
 actual_passes.append({'reference':ref(r['file']),'entire_original_record_body_and_time':a,'raw_log':ref(a['log']),'raw_log_text':Path(a['log']).read_text()})
assert len(actual_passes)==4
history=[]
for n,h in j['exact_original_trial_and_isolated_import_history_sha256'].items():
 assert H(n)==h
 if n.endswith('.json'):
  a=read(n)
  if 'actual_exit_code' in a:
   assert a['actual_exit_code'] in [0,1] and H(a['log'])==a['log_sha256']
   assert a['actual_workdir']==str(ROOT/'verification/lean') and H(a['actual_runner'])==a['actual_runner_sha256']
   if 'source_snapshot' in a:assert H(a['source_snapshot'])==a['source_snapshot_sha256']==a['source_sha256_before']==a['source_sha256_after']
   if a.get('actual_olean_output') and a['actual_exit_code']==0:
    assert H(a['actual_olean_output'])==a['actual_olean_sha256'] and H(a['source'])==H(a['byte_exact_original_source'])==a['source_sha256_before']==a['source_sha256_after']
   history.append({'reference':ref(n),'entire_original_actual_record_body_and_time':a,'raw_log':ref(a['log'])})
assert len(history)==15 and sum(r['entire_original_actual_record_body_and_time']['actual_exit_code']==1 for r in history)==8
isolated=read('/tmp/applied-gaussian-mixture24-isolated-retained-import-symlinks-v3.json')
assert len(isolated['files'])==3650
for r in isolated['files']:
 p=Path(r['file']);assert p.is_symlink() and p.resolve()==Path(r['target']).resolve()
 assert str(p).startswith('/tmp/applied-gaussian-mixture24-isolated-imports-v2/') and H(p)==H(r['target'])==r['sha256']
import_ready=read('/tmp/applied-gaussian-mixture24-isolated-import-build-readiness-v2.json')
assert len(import_ready['actual_records'])==3
for r in import_ready['actual_records']:assert checked(r)['actual_exit_code']==0
original_component=checked(j['original_component_request_preserved'])
old_cov_peer=checked(j['original_covariance_component_peer']);assert 'passed' in old_cov_peer['status'] and old_cov_peer['errors']==[]
cov=j['retained_canonical_covariance_source'];assert H(cov['file'])==cov['sha256'] and Path(cov['file']).read_text()==cov['full_source']
assert len(cov['public_names'])==4
dep=j['retained_actual_finite_mixture_dependency'];assert H(dep['file'])==dep['sha256']
dependency_pairs=[]
for r in j['canonical_dependency_pairs']:
 a=checked(r);exits=[a[k] for k in ['exit_code','actual_exit_code'] if k in a];assert exits and all(x==0 for x in exits)
 assert H(path(a['source']))==a['source_sha256_before']==a['source_sha256_after'] and H(path(a['log']))==a['log_sha256']
 dependency_pairs.append({'reference':ref(r['file']),'entire_original_record_body_and_time':a,'raw_log':ref(a['log'])})
assert len(dependency_pairs)==4
manifest=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json');assert len(manifest['proof_files'])==1131
for n,r in manifest['proof_files'].items():assert H(ROOT/n)==r['sha256']
owners={n:h for n,h in manifest['working_inputs_sha256'].items() if n in ['book/coverage/'+x+'.json' for x in ['core','foundations','applied','modules','applied-promotions']]}
assert len(owners)==5
for n,h in owners.items():assert H(ROOT/n)==h
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert H(ROOT/manifest['snapshot']/n)==h
primary=[]
for name,begin,end in [
 ('verification/lean/.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean',495,585),
 ('verification/lean/SafeLearning/CompleteAppliedGaussianGeneralIntegral.lean',1,None),
 ('verification/lean/SafeLearning/CompleteAppliedGaussianQuantile.lean',1,84)]:
 p=ROOT/name;lines=p.read_text().splitlines(True);end=end or len(lines)
 if name.startswith('verification/lean/SafeLearning/'):assert H(p)==manifest['proof_files'][name]['sha256']
 primary.append({'file':name,'sha256':H(p),'lines_start':begin,'lines_end':end,'exact_lines':''.join(lines[begin-1:end])})
groups=[
 {'component_id':'actual_normalized_gaussian_residual_law_and_variance',
  'lean_declarations':sources[0]['public_theorem_names'][:3]+[names[18]],
  'hypotheses':['The actual normalized selector has weights4/5,1/5 and centered Gaussian component variances1/4,9. Each component and the finite mixture have genuine finite second moments.'],
  'per_component_reason':'The definitions and probability instance construct the actual law, not an assumed variance. True component means/variances and the finite-mixture integral identities derive mean0 and variance2; the matched Gaussian0,2 has the same actual moments. The Module15 display and .8/.5/3 draw branch are an exact distribution-model cross-reference.', 'missing_clauses':[]},
 {'component_id':'actual_tail_formula_radius5_and_all_printed_roundings',
  'lean_declarations':sources[0]['public_theorem_names'][3:]+sources[1]['public_theorem_names']+sources[2]['public_theorem_names']+sources[3]['public_theorem_names'][1:3]+sources[3]['public_theorem_names'][4:5]+sources[3]['public_theorem_names'][6:8],
  'hypotheses':['Positive Gaussian scale and nonnegative radius; the literal uses fixed radii1 and5. The Taylor/CDF estimates are proved on [0,2] or [0,4], which contain every evaluated radius.'],
  'per_component_reason':'The strict absolute-tail event is evaluated by actual normalized measures, Gaussian scaling and true CDF reflection. Certified rational exponential-integral estimates plus true MGF/Chernoff tail10 control derive mixture tail5 in(0.01911,0.01914) and variance-matched tail5 in(0.0004068,0.0004071). These imply both printed rounding tolerances and the strict heavier-tail comparison; none of these probabilities or desired inequalities is a theorem premise.', 'missing_clauses':[]},
 {'component_id':'actual_radius1_concentration_comparison',
  'lean_declarations':[sources[3]['public_theorem_names'][3],sources[3]['public_theorem_names'][5],sources[3]['public_theorem_names'][6],sources[3]['public_theorem_names'][7]],
  'hypotheses':['Near-origin concentration is the source parenthetical comparison at radius1; no all-radius stochastic order or density dominance is asserted.'],
  'per_component_reason':'The true tail1 bounds(0.1841,0.1843) and(0.47944,0.47951) prove the printed0.18/0.48 roundings and smaller tail1 for the mixture. Complementing the exact strict-tail event gives greater probability of the closed unit interval, which is the stated near-zero comparison.', 'missing_clauses':[]},
 {'component_id':'actual_equal_weight_ensemble_full_covariance_matrix',
  'lean_declarations':cov['public_names'],
  'hypotheses':['Finite nonempty ensemble and coordinate finite second moments, as supplied by the full probability page context. Member laws are actual probability laws; Gaussian members satisfy this finite-moment domain.'],
  'per_component_reason':'The retained four full canonical bodies derive scalar centered within/between covariance, the genuine label-law covariance of actual member means, the entire vector covariance matrix identity and the true1/E specialization. They match the displayed average-member plus between-member covariance, including the Section1 hatSigma cross-reference. Aleatoric/epistemic are explanatory names for these exact terms.', 'missing_clauses':[]}
]
assert len(groups)==4 and all(r['missing_clauses']==[] for r in groups)
report={'status':'passed_independent_fresh_whole401_full_literal_gaussian_law_true_CDF_MGF_numeric_consequences_and_ensemble_covariance_review',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),
 'original_request':ref(REQUEST),'entire_original_request_body_and_time':j,'historical_source51_inventory':ref(historical),
 'observed_current_inventory_sha256':hashlib.sha256(current_bytes).hexdigest(),
 'current_whole401_record_equal_to_entire_source51_record':True,'entire_complete_source_contexts':j['complete_source_contexts'],
 'all26_new_full_public_and_private_bodies_and_retained4_covariance_bodies_read':True,
 'new_TMP_public_names':names,'new_TMP_sources':sources,'actual_original_TMP_passes':actual_passes,
 'original_failed_and_passed_trial_and_import_records':history,
 'original_history_artifact_sha256':j['exact_original_trial_and_isolated_import_history_sha256'],
 'isolated_retained_import_symlinks_read_and_rehashed':{'reference':ref('/tmp/applied-gaussian-mixture24-isolated-retained-import-symlinks-v3.json'),'count':3650,'all_exact':True,'TMP_only':True},
 'retained_canonical_dependency_pairs':dependency_pairs,'original_component_request_retained':{'reference':j['original_component_request_preserved'],'entire_original_body_and_time':original_component},
 'original_covariance_component_peer_retained':{'reference':j['original_covariance_component_peer'],'entire_original_body_and_time':old_cov_peer},
 'material_units':[{'entire_inventory_record':unit,'status':'whole_mathematical_unit_proved','whole_unit_approved':True,
   'components':groups,'lean_declarations':names+cov['public_names'],'hypotheses':j['hypotheses'],
   'per_unit_reason':'Every mathematical clause in the full printed401 unit matches the actual normalized Gaussian-mixture model, true four numeric tail roundings/two comparisons and the complete finite-ensemble covariance identity under the page moment domain. Full context and Module15/Section1 cross-references were read directly.', 'missing_clauses':[]}],
 'whole_mathematical_units_approved':[unit['key']],'precise_component_groups_approved':groups,'direct_primary_reads':primary,
 'all1131_current_selected23_source_hashes_exact':True,'all31_frozen23_asset_hashes_exact':True,'all_five_live23_owner_sha256':owners,
 'scope_limits':['This is a fresh whole401 mathematical decision. The original covariance-only peer/body/time and reviewed4-source29-export Applied24 candidate remain unchanged.',
   'The explorer cross-reference identifies its intended .8/.2 Gaussian model and absolute-residual score. No theorem about finite PRNG software, numerical implementation or exact empirical sampler law is inferred.',
   'Near-origin concentration means the explicit radius1 parenthetical. No all-radius comparison, global density order or general epistemic/aleatoric probabilistic interpretation is added.',
   'Four new sources currently have actual TMP standalone evidence and isolated TMP import outputs only. Canonical named pairing, mapping/selection, aggregate audit and publication require separate genuine future actions.',
   'Inventory51 is the immutable request identity. The fresh entire401 literal/page is unchanged during another-page source52 preparation; global identities are separately rebound after Root actual source52 release.'],
 'errors':[],'coverage_complete':False,'ledger_HTML_candidate_or_selected_source_mutations':False}
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':ref(OUT),'whole_units':[unit['key']],'new_public_names':len(names),'retained_covariance_names':len(cov['public_names']),'compiler_rerun':False}))
