from pathlib import Path
import json,hashlib,re,importlib.util,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/matrix53-normal-covariance-supplement-v1';assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==h
 r=ref(q);aliases[str(p)]=r;return r
S=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v14.lean');old=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v10.lean');assert sha(S)=='794793810c46f178fe1b2d7b1b9b4985d2a4aae7ede55dfd4a3ba30cc6220b4c';assert S.read_bytes().startswith(old.read_bytes())
Q=R/'book/coverage/checks/modules-future30/matrix42-paper-PSD-eq4-supplement-v2/modules-matrix42-paper-PSD-equation4-exact-prefix-full-association-component-review-request30-v2.json';q=json.loads(Q.read_bytes())
P=R/'book/coverage/checks/modules-future30/matrix42-independent-foundations-v1/modules-matrix42-full-source-current-literal-components-independent-foundations30-closed-peer-v1.json';p=json.loads(P.read_bytes());assert p['errors']==[]
sp=importlib.util.spec_from_file_location('matrix53_supply_names',R/'book/coverage/lean_names.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);ds=m.declarations(S.read_text());prior=m.declarations(old.read_text());assert ds[:len(prior)]==prior
names=[x['name']for x in ds if x['kind']in['theorem','lemma']];newds=ds[len(prior):];assert len(names)==53 and sum(x['kind']in['theorem','lemma']for x in newds)==11
hist=[]
for i in range(10,14):
 n=Path('/tmp/modules-matrix-scenario-open-obstruction30-owner29-trial'+str(i)+'.json');a=json.loads(n.read_bytes());assert a['source_unchanged']and a['protection_errors']==[]
 assert a['actual_command']==['lake','env','lean',a['source']]and a['actual_workdir']==str(R/'verification/lean')
 assert sha(a['source'])==sha(a['source_snapshot'])==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256'];assert sha(a['raw_log'])==a['raw_log_sha256']
 hist.append({'native':copy(n),'source':copy(a['source']),'source_snapshot':copy(a['source_snapshot']),'raw_log':copy(a['raw_log']),'actual_exit_code':a['actual_exit_code'],'actual_warning_headers':len(re.findall(r'^.*?:\d+:\d+: warning:',Path(a['raw_log']).read_text(),re.M)),'original_actual_times':{k:a[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [x['actual_exit_code']for x in hist]==[1,1,1,0]
primary=[]
for name in ['Probability/Distributions/Gaussian/Multivariate.lean','Analysis/Matrix/Order.lean','Analysis/CStarAlgebra/Matrix.lean','Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean','LinearAlgebra/Matrix/NonsingularInverse.lean','Data/Matrix/Kronecker.lean','Probability/Moments/Covariance.lean','Analysis/Normed/Lp/WithLp.lean','Analysis/Normed/Lp/PiLp.lean','Data/Fin/Tuple/Basic.lean','MeasureTheory/Measure/OpenPos.lean']:
 x=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name;primary.append({'original_package_path_historical_metadata':str(x),'entire_physical_primary_source':copy(x)})
for x in [__file__,'/tmp/run-modules-matrix53-normal-covariance-supplement30-preparation-v1.py','/tmp/modules-matrix-scenario-matrix-normal-append30-v11.txt','/tmp/root_tmp_lean_current65_owner29_runner_v1.py','/tmp/root_tmp_lean_current65_owner29_context_v1.json']:copy(x)
d={'status':'prepared_matrix53_exact_prefix_provided_matrix_normal_covariance_fullsupport_and_printed_initial_LMI_failure_component_review_request','source':copy(S),'public_theorem_count':len(names),'public_theorem_names':names,'public_declaration_count':len(ds),'new11_public_theorem_names':[x['name']for x in newds if x['kind']in['theorem','lemma']],'new_five_other_declarations':[x for x in newds if x['kind']not in['theorem','lemma']],
 'original42_entire_byte_prefix':copy(old),'prefix_length_bytes':old.stat().st_size,'prefix_includes_closing_namespace_end':True,'original42_full_component_request':ref(Q),'original42_independent_full_semantic_peer':ref(P),'original23_and_strict30_verdicts_and_body_times_retained_by_exact_prior_refs':True,
 'four_new_authentic_kernel_histories':hist,'new_genuine_native_codes':[x['actual_exit_code']for x in hist],'new_genuine_warning_headers':[x['actual_warning_headers']for x in hist],'original_nine_authentic_kernel_histories_retained_by_exact_request_refs':True,
 'entire_current_exercise':q['entire_current_exercise'],'entire_original_owned_exercise_row':q['entire_original_owned_exercise_row'],'entire_current_material_literals':q['entire_current_material_literals'],'entire_original_material_rows':q['entire_original_material_rows'],'entire_used_scenario_section_context':q['entire_used_scenario_section_context'],'entire_exercise_context':q['entire_exercise_context'],'current_inventory':q['current_inventory'],'immutable_original_owner29':q['immutable_original_owner29'],
 'full_new_used_primary_API_sources':primary,'primary_paper_bounded_read_preserved':q['primary_paper_bounded_read'],
 'exact_components_requested':[
 {'scope':'Genuine finite multivariate Gaussian probability and full support from positive covariance','mathematical_route':'Actual standard Euclidean Gaussian is the pushforward of independent N(0,1) coordinates through toLp. True positive covariance makes CFC.sqrt invertible; its actual Euclidean linear action plus mean is continuous and surjective, hence full support. The exact Gaussian measure is a probability.'},
 {'scope':'Provided matrix-normal law has actual V tensor U covariance and true(A,B) coordinates','mathematical_route':'Columns indexed Fin5 and rows Fin4. The latent multivariateGaussian(mean,V tensor U) maps bijectively and continuously to A first four columns and B final column. Actual covariance_eval and covariance_map give cov(Mij,Mi\u2032j\u2032)=Vjj\u2032 Uii\u2032. Positive row and column covariance factors make the Kronecker covariance positive definite, yielding full support and a probability measure.'},
 {'scope':'Provided nondegenerate matrix-normal five-sample law has positive printed PSD initial-LMI failure','mathematical_route':'The previously reviewed genuine nonempty open five-model obstruction has positive measure under the derived full-support matrix-normal product law; it excludes all common recovered gains for the actual printed PSD equation4 blocks. Positivity is through a measurable open witness. No unproved measurability of the whole existential-failure event is presumed.'}],
 'scope_exclusions':['The source assumes a PROVIDED matrix-normal law; no equality to a particular GP derivative conditional posterior is derived.','Positive U,V are explicit nondegeneracy hypotheses, not asserted for every prior kernel or dataset.','Five samples are used; neither an open incompatible pair nor arbitrary sample count larger than five is silently derived.','Current numeric precision, full generic scenario theorem/tightness/union-bound and paper attribution scopes remain distinct.'],
 'whole_current_exercise_requested':False,'whole_current_material_units_requested':False,'source_applied':False,'source_ordinal_reserved':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{x['file']:x['sha256']for x in aliases.values()}}
for par in [q,p]:
 for n,h in par['required_evidence_artifacts_sha256'].items():d['required_evidence_artifacts_sha256'][n]=h
for x in [Q,P]:d['required_evidence_artifacts_sha256'][ref(x)['file']]=sha(x)
out=B/'modules-matrix53-provided-matrix-normal-full-eleven-body-association-component-review-request30-v1.json';out.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':ref(out),'theorems':len(names),'public':len(ds),'new_codes':d['new_genuine_native_codes'],'warnings':d['new_genuine_warning_headers'],'closed_refs':len(d['required_evidence_artifacts_sha256'])}))
