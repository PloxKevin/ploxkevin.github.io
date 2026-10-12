from pathlib import Path
import hashlib,json,importlib.util,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future30/matrix-scenario23-full-components-v2'
assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def path(r):
 p=Path(r['file']);p=p if p.is_absolute() else R/p;assert sha(p)==r['sha256'];return p
aliases={}
def copy(p):
 p=Path(p);q=B/'original-closed-bytes'/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==sha(p)
 z=ref(q);aliases[str(p)]=z;return z
S=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v7.lean')
N=[Path('/tmp/modules-matrix-scenario-open-obstruction30-owner29-trial'+str(i)+'.json') for i in range(1,7)]
final=json.loads(N[-1].read_bytes())
assert final['actual_exit_code']==final['actual_runner_exit_code']==0 and final['protection_errors']==[]
assert sha(S)==final['source_sha256_before']==final['source_sha256_after']=='115284c6cf2d925f21844691d91945c32f9c3dab46805c2d7b7eee36ac7cafa1'
old=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v3.lean');assert S.read_bytes().startswith(old.read_bytes())
Q=R/'book/coverage/checks/modules-future30/scenario33-full-components-v1/modules-scenario33-full-source-current-literals-component-independent-review-request30-v2.json'
q=json.loads(Q.read_bytes());I=path(q['current_inventory']);O=path(q['immutable_original_owner29']);P=R/'SafeLearning/verification.html'
assert sha(O)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
assert sha(P)=='2b60f48b0b374ab75902df099a19d28289b1e107ba2e23187c2b1e348f7d52cb'
B.mkdir(parents=True)
sp=importlib.util.spec_from_file_location('matrix23_names',R/'book/coverage/lean_names.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
ds=m.declarations(S.read_text());names=[d['name'] for d in ds if d['kind'] in ['theorem','lemma']]
assert len(names)==23
hist=[]
for p in N:
 j=json.loads(p.read_bytes());assert j['source_unchanged'] and j['protection_errors']==[]
 assert j['actual_command']==['lake','env','lean',j['source']] and j['actual_workdir']==str(R/'verification/lean')
 assert sha(j['source'])==sha(j['source_snapshot'])==j['source_sha256_before']==j['source_sha256_after']==j['source_snapshot_sha256']
 assert sha(j['raw_log'])==j['raw_log_sha256']
 hist.append({'actual_native':copy(p),'source':copy(j['source']),'source_snapshot':copy(j['source_snapshot']),'raw_log':copy(j['raw_log']),'actual_exit_code':j['actual_exit_code'],'actual_warning_headers':len(re.findall(r'^.*?:\d+:\d+: warning:',Path(j['raw_log']).read_text(),re.M)),'original_actual_times':{k:j[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
primary=[]
for name in ['LinearAlgebra/Matrix/Charpoly/Basic.lean','LinearAlgebra/Matrix/Charpoly/LinearMap.lean','LinearAlgebra/Matrix/Charpoly/Coeff.lean','Analysis/Matrix/Spectrum.lean','LinearAlgebra/Eigenspace/Basic.lean','LinearAlgebra/Matrix/PosDef.lean','Data/Matrix/Mul.lean','LinearAlgebra/Matrix/ConjTranspose.lean','Analysis/Complex/Norm.lean','Probability/Distributions/Gaussian/Real.lean','MeasureTheory/Measure/OpenPos.lean','MeasureTheory/Constructions/Pi.lean','MeasureTheory/Measure/Typeclasses/Probability.lean','Data/Fin/Tuple/Basic.lean']:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name;primary.append({'original_package_path_historical_metadata':str(p),'entire_physical_API_source':copy(p)})
for p in ['/tmp/prepare-modules-matrix-scenario23-full-components30-v1.py','/tmp/run-modules-matrix-scenario23-full-components30-preparation-v1.py','/tmp/modules-matrix-scenario23-full-components30-preparation-actual-v1.json','/tmp/modules-matrix-scenario23-full-components30-preparation-actual-v1.log',__file__,'/tmp/run-modules-matrix-scenario23-full-components30-preparation-v2.py','/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',R/'book/coverage/lean_names.py']:copy(p)
request={'genuine_original_author_preparation_failure':copy('/tmp/modules-matrix-scenario23-full-components30-preparation-actual-v1.json'),'author_preparation_failure_scope':'True author1 failed at nonexistent old LinearAlgebra/Matrix/Spectrum API path, after partial historical copies; code/native/raw/time retained, new2 uses actual Analysis/Matrix/Spectrum path. No mathematical/source/compiler failure is invented.','status':'prepared_matrix_scenario23_full_source_and_exact_current_literals_component_review_request','source':copy(S),'public_theorem_count':len(names),'public_theorem_names':names,'public_declaration_count':len(ds),'other_public_declarations':[d for d in ds if d['kind']not in ['theorem','lemma']],
 'genuine_original_native_history':hist,'genuine_native_codes':[h['actual_exit_code']for h in hist],'genuine_warning_headers':[h['actual_warning_headers']for h in hist],
 'uncompiled_historical_sources':[{'source':copy('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v1.lean'),'compiled':False,'scope':'Original offline draft retained; not counted as an authentic compiler trial.'}],
 'exact_old11_entire_byte_prefix':copy(old),'exact_old11_prefix_length_bytes':old.stat().st_size,'exact_old11_prefix_includes_closing_namespace_end':True,
 'entire_current_exercise':q['entire_current_exercise'],'entire_original_owned_exercise_row':q['entire_original_owned_exercise_row'],'entire_current_material_literals':q['entire_current_material_literals'],'entire_original_material_rows':q['entire_original_material_rows'],
 'entire_current_page_original_byte_alias':q['entire_current_page_original_byte_alias'],'entire_used_scenario_section_context':q['entire_used_scenario_section_context'],'entire_exercise_context':q['entire_exercise_context'],'current_inventory':ref(I),'immutable_original_owner29':ref(O),'original_Scenario33_author_request':ref(Q),
 'complete_selected_sources':q['complete_selected_sources'],'entire_physical_primary_API_sources':primary,
 'exact_components_requested':[
 {'scope':'Actual nonempty open five-model matrix obstruction','proof_scope':'For dx4,du1 genuine complex charpoly roots bound stable trace; true rank-one state feedback gives trace+input-gain pairing. Four small-trace models near B=e_i bound all gain coordinates/L1; a fifth large-trace model near B=e_3 contradicts stability. The entire open event is nonempty and defeats every common feedback gain. It is five models, not an open incompatible pair.'},
 {'scope':'Actual positive Lyapunov certificates imply Schur stability','proof_scope':'Generic finite real positive P and P-C^T P C yield true positive complex energy, eigenvalue norm-scaling and a positive drop. Actual charpoly roots supply nonzero eigenvectors, hence norm<1. No stability premise. This is the genuine discrete Lyapunov criterion; the paper initial eq4 block-LMI correspondence remains separate.'},
 {'scope':'Actual nondegenerate affine Gaussian20-coordinate law has full support and probability','proof_scope':'Independent real N(0,1) coordinates are positive on all nonempty opens, product coordinates inherit it, and a continuous invertible affine factor followed by the true coordinate-to-(A,B) bijection pushes this to full support. Probability is proved. This explicit law is not silently identified with the paper GP matrix-normal posterior or its U tensor V covariance.'},
 {'scope':'Actual positive probability of common-gain and common-Lyapunov failure','proof_scope':'For independent five samples from a full-support law, the actual nonempty open obstruction has positive measure, and every sample in it has no common Schur-stable gain or positive Lyapunov certificate. The explicit nondegenerate affine Gaussian law instantiates it. No adaptive-gain fixed-gain quantifier interchange.'}],
 'whole_current_exercise_requested':False,'whole_current_exercise_expected_pending':True,'explicit_remaining_whole_associations':['Current worked paragraph explicitly requests an open matrix incompatible pair; this proof supplies a five-model obstruction.','Paper eq4 Y/Z/L full block-LMI to the actual positive discrete Lyapunov criterion is not yet derived.','Paper actual GP matrix-normal posterior and covariance/nondegeneracy to this explicit affine Gaussian law are not yet identified.','Current rounded logarithm/equality precision and broader generic scenario-tightness/union-bound/factual attribution remain separate scopes.'],
 'source_ordinal_reserved':False,'source_applied':False,'whole_promotion_performed':False,'canonical_pairs_executed':False,'independent_full_semantic_review_pending':True,'compiler_or_parser_started_by_preparation':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{v['file']:v['sha256']for v in aliases.values()}}
for n,h in q['required_evidence_artifacts_sha256'].items():request['required_evidence_artifacts_sha256'][n]=h
request['required_evidence_artifacts_sha256'][ref(Q)['file']]=sha(Q)
p=B/'modules-matrix-scenario23-full-source-current-literals-component-independent-review-request30-v2.json';p.write_text(json.dumps(request,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':ref(p),'public_theorems':len(names),'public_declarations':len(ds),'native_codes':request['genuine_native_codes'],'warnings':request['genuine_warning_headers'],'closed_refs':len(request['required_evidence_artifacts_sha256'])}))
