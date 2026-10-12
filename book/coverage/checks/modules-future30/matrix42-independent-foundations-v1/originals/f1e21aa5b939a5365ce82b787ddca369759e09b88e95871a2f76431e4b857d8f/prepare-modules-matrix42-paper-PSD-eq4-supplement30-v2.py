from pathlib import Path
import hashlib,json,re,importlib.util,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/matrix42-paper-PSD-eq4-supplement-v2'
assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==h
 r=ref(q);aliases[str(p)]=r;return r
S=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v10.lean')
old23=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v7.lean');old30=Path('/tmp/CompleteModulesMatrixScenarioOpenObstruction30-draft-v9.lean')
assert sha(S)=='2df065cf3b1342f7beab90cd3403789da197911fd855132ddedfc7cfa09035ef'
assert S.read_bytes().startswith(old30.read_bytes()) and old30.read_bytes().startswith(old23.read_bytes())
Q=R/'book/coverage/checks/modules-future30/matrix-scenario23-full-components-v3/modules-matrix-scenario23-full-source-current-literals-component-independent-review-request30-v3.json'
P=R/'book/coverage/checks/modules-future30/matrix-scenario23-independent-foundations-v1/modules-matrix-scenario23-full-source-current-literal-components-independent-foundations30-closed-peer-v1.json'
q=json.loads(Q.read_bytes());p=json.loads(P.read_bytes());assert p['errors']==[] and not p['whole_current_Exercise19_or_any_material_literal_approved']
sp=importlib.util.spec_from_file_location('matrix42_names',R/'book/coverage/lean_names.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
ds=m.declarations(S.read_text());old=m.declarations(old23.read_text());strict=m.declarations(old30.read_text())
assert ds[:len(strict)]==strict and strict[:len(old)]==old
names=[x['name']for x in ds if x['kind']in['theorem','lemma']];assert len(names)==42
hist=[]
for i in [7,8,9]:
 n=Path('/tmp/modules-matrix-scenario-open-obstruction30-owner29-trial'+str(i)+'.json');a=json.loads(n.read_bytes())
 assert a['source_unchanged'] and a['protection_errors']==[]
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(R/'verification/lean')
 assert sha(a['source'])==sha(a['source_snapshot'])==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(a['raw_log'])==a['raw_log_sha256']
 hist.append({'native':copy(n),'source':copy(a['source']),'source_snapshot':copy(a['source_snapshot']),'raw_log':copy(a['raw_log']),'actual_exit_code':a['actual_exit_code'],'actual_warning_headers':len(re.findall(r'^.*?:\d+:\d+: warning:',Path(a['raw_log']).read_text(),re.M)),'original_actual_times':{k:a[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert hist[-1]['actual_exit_code']==0 and hist[-1]['actual_warning_headers']==19
primary=[]
for name in ['LinearAlgebra/Matrix/PosDef.lean','LinearAlgebra/Matrix/SchurComplement.lean','LinearAlgebra/Matrix/Charpoly/Eigs.lean','LinearAlgebra/Matrix/Trace.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean','LinearAlgebra/Matrix/ConjTranspose.lean','Data/Matrix/Block.lean','Data/Matrix/Mul.lean','Algebra/Order/GroupWithZero/Basic.lean']:
 x=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name;primary.append({'original_package_path_historical_metadata':str(x),'entire_physical_API_source':copy(x)})
retrieval=Path('/tmp/modules-rohr-primary-eq4-30-retrieval-actual-v1.json');rn=json.loads(retrieval.read_bytes());assert rn['actual_exit_code']==0 and rn['protection_errors']==[]
receipt=Path('/tmp/modules-rohr-primary-eq4-30-v1/rohr21a-primary-http-receipt-v1.json');hr=json.loads(receipt.read_bytes());assert hr['http_status']==200 and hr['original_pdf']['sha256']=='bdc2e2f36fd0f7ba3644afaaa45b2211a87d9d87a4c12e39adfe5d85725536c6'
assert sha(hr['original_pdf']['file'])==hr['original_pdf']['sha256']
for x in ['/tmp/prepare-modules-matrix42-paper-PSD-eq4-supplement30-v1.py','/tmp/run-modules-matrix42-paper-PSD-eq4-supplement30-preparation-v1.py','/tmp/modules-matrix42-paper-PSD-eq4-supplement30-preparation-actual-v1.json','/tmp/modules-matrix42-paper-PSD-eq4-supplement30-preparation-actual-v1.log',__file__,'/tmp/run-modules-matrix42-paper-PSD-eq4-supplement30-preparation-v2.py','/tmp/root_tmp_lean_current65_owner29_runner_v1.py','/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/modules-matrix-scenario-PSD-eq4-append30-v10.txt','/tmp/modules-matrix-scenario-unit-disk-five-proof-append30-v10.txt','/tmp/retrieve-modules-rohr-primary-eq4-30-v1.py','/tmp/run-retrieve-modules-rohr-primary-eq4-30-v1.py','/tmp/modules-rohr-primary-eq4-30-retrieval-actual-v1.log']:copy(x)
d={'genuine_original_author_preparation1_failure':copy('/tmp/modules-matrix42-paper-PSD-eq4-supplement30-preparation-actual-v1.json'),'author_failure1_scope':'Actual first author preparation failed before durable writes solely using the wrong exact prior peer whole-verdict key. NEW2 corrects that key; old helper/native/log/body/time remain exact. No mathematical or compiler failure was invented.','status':'prepared_matrix42_full_source_printed_PSD_equation4_association_component_review_request','source':copy(S),'public_theorem_count':len(names),'public_theorem_names':names,'public_declaration_count':len(ds),'other_public_declarations':[x for x in ds if x['kind']not in['theorem','lemma']],
 'original23_full_component_request':ref(Q),'original23_independent_full_semantic_peer':ref(P),'original23_entire_byte_prefix':copy(old23),'original23_prefix_length_bytes':old23.stat().st_size,'original23_body_and_peer_time_retained':True,
 'original_strict30_strengthening_source':copy(old30),'exact_entire_strict30_byte_prefix_includes_namespace_end':True,'strict30_strengthening_public_declarations':strict[len(old):],'new_PSD12_public_declarations':ds[len(strict):],
 'new_authentic_native_history':hist,'new_genuine_native_codes':[x['actual_exit_code']for x in hist],'new_genuine_warning_headers':[x['actual_warning_headers']for x in hist],
 'original_six_kernel_histories_bound_without_recursive_embedding':{'original_request':ref(Q),'json_pointer':['genuine_original_native_history']},
 'entire_current_exercise':q['entire_current_exercise'],'entire_original_owned_exercise_row':q['entire_original_owned_exercise_row'],'entire_current_material_literals':q['entire_current_material_literals'],'entire_original_material_rows':q['entire_original_material_rows'],'entire_used_scenario_section_context':q['entire_used_scenario_section_context'],'entire_exercise_context':q['entire_exercise_context'],'current_inventory':q['current_inventory'],'immutable_original_owner29':q['immutable_original_owner29'],
 'entire_physical_new_used_primary_API_sources':primary,
 'primary_paper_bounded_read':{'url':hr['url'],'actual_HTTP200_receipt':copy(receipt),'actual_measured_retrieval_native':copy(retrieval),'original_PDF_SHA256':hr['original_pdf']['sha256'],'original_PDF_bytes':hr['original_pdf']['bytes'],'original_PDF_TMP_path_historical_metadata':hr['original_pdf']['file'],'full_original_stays_TMP_offline':True,'actual_visual_read_page':5,'actual_original_render_TMP_path_historical_metadata':'/tmp/modules-rohr-primary-eq4-30-v1/rohr21a-page5-eq4-original-render.png','bounded_read_summary':'Equation4 on page5 requires both displayed block matrices to be positive semidefinite, with Y positive definite; the recovered gain is L times inverse Y. The first block uses AY+BL and Y, with the lower Q-square-root and L rows and identity and inverse-R diagonal blocks. The second is the noise/slack block with Z and Y. The true rendered PDF signs resolve the text-extraction ambiguity. Our earlier positive-definite first/slack-block variant is a strict strengthening. The new semidefinite adapter derives closed-unit-disk eigenvalues from its principal block; the five-model trace obstruction excludes even that weaker conclusion. The explicit affine Gaussian law supplies a positive measurable open witness. This does not identify the general GP derivative posterior, covariance, or all other paper statements.'},
 'exact_components_requested':[
 {'scope':'Seven strict equation4-strengthening bridges','requested':True,'scope_limit':'Actual 13x13 first and slack block both PD are a strict strengthening; recover K=L Y^-1 and strict Schur roots via principal Schur complement. No assertion that paper equation4 itself is strict.'},
 {'scope':'Twelve actual semidefinite equation4 association bridges','requested':True,'scope_limit':'Exact paper PSD first and slack blocks with YPD/rpositive; recover K, true PSD Lyapunov drop, actual complex eigenvalues norm<=1. Five open models rule out every common closed-unit-disk gain, hence the actual initial block LMI. Genuine explicit nondegenerate affine Gaussian five-sample law gives positive outer measure of failure through a positive measurable open witness; no full existential-failure event measurability presumed.'}],
 'whole_current_exercise_requested':False,'whole_current_exercise_expected_pending':True,'remaining_whole_associations':['The current worked literal asks for an open incompatible matrix pair, whereas this proof uses five models.','Actual matrix-normal GP posterior U tensor V covariance and nondegeneracy are not identified with the explicit affine Gaussian law.','General scenario theorem, precision, original distribution-tightness/union-bound and factual attributions remain distinct.'],
 'source_ordinal_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{v['file']:v['sha256']for v in aliases.values()}}
for par in [q,p]:
 for n,h in par['required_evidence_artifacts_sha256'].items():d['required_evidence_artifacts_sha256'][n]=h
for x in [Q,P]:d['required_evidence_artifacts_sha256'][ref(x)['file']]=sha(x)
out=B/'modules-matrix42-paper-PSD-equation4-exact-prefix-full-association-component-review-request30-v2.json';out.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':ref(out),'theorems':len(names),'public':len(ds),'new_codes':d['new_genuine_native_codes'],'warnings':d['new_genuine_warning_headers'],'closed_refs':len(d['required_evidence_artifacts_sha256'])}))
