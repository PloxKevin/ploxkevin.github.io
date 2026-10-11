from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/mpc-feedback-norm28-one-component-independent-foundations28-findings-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else ROOT/p;assert sha(p)==r['sha256'],str(p);return p
packet=Path('/tmp/mpc-original-feedback-norm28-one-component-review-request-v2.json');assert sha(packet)=='eb93d3b07ef5801400609d3c1a4961aac02382e7dc17ef6dff907270b8dbb7f7';j=read(packet)
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']};held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners);held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'})
def guard():
 for n,h in held.items():assert sha(ROOT/n)==h,n
started=datetime.now(timezone.utc).isoformat();guard();assert len(sel['proof_files'])==1175 and len(assets)==31 and len(owners)==5
closed={str(packet):sha(packet)}
for n,h in j['closed_evidence_sha256'].items():assert sha(n)==h,n;closed[n]=h
source=checked(j['source']);old=checked(j['exact_old27_source']);s=source.read_text();prefix=old.read_text();assert s==prefix+j['new_full_body_and_namespace']
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
assert len(re.findall(r'^theorem ',s,re.M))==28 and len(re.findall(r'^theorem ',prefix,re.M))==27
body=j['new_full_body_and_namespace'];assert len(re.findall(r'^theorem ',body,re.M))==1
norm=checked(j['selected_norm_dependency']);assert sha(norm)==sel['proof_files'][str(norm.relative_to(ROOT))]['sha256']
assert 'namespace SafeLearning.CompleteCoreMPCNormBridge27' in norm.read_text()
assert 'actual_coordinate_infinity_norm_is_at_most_the_state_euclidean_norm'in body
prior=read(checked(j['original_independent27_review']));assert prior['whole_exercise18_approved']is False and prior['whole_material_units_approved']is False
assert j['original_independent27_review_times']=={k:prior[k]for k in ['reviewed_at_utc','completed_at_utc']}
inv=read(ROOT/'book/coverage/inventory.json');units={u['key']:u for u in inv['material_source_units']}
for u in j['full_current55_material_records']:assert u==units[u['key']]
a=read(checked(j['actual_trial']));raw=checked(j['actual_raw_log']);snapshot=checked(j['actual_source_snapshot'])
for k in ('actual_exit_code','actual_runner_exit_code'):assert type(a[k])is int and a[k]==0
assert a['status']=='passed_actual_tmp_lean_only'and a['protection_errors']==[] and a['source_unchanged']is True
assert a['actual_command']==['lake','env','lean',str(source)]and a['actual_workdir']==str(ROOT/'verification/lean')
assert sha(source)==sha(snapshot)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']and sha(raw)==a['raw_log_sha256']
assert a['protected_selected27_proof_sources']==1175 and a['unchanged_current55_book_assets']==31 and a['unchanged_installed27_live_owners']==5 and a['installed27_owner_sha256']==owners
for n,h in a['pinned_installed27_provenance_sha256'].items():assert sha(ROOT/n)==h,n
warnings=len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M));assert warnings==j['actual_warning_count']==15
source60peer=Path('/tmp/mpc-source60-row-definitions-independent-foundations28-v2.json');assert sha(source60peer)=='e37a5d04c72dd58ea826472a739f7a4ef2a6f7c40479dfe315a4da3f0b19a4e5';closed[str(source60peer)]=sha(source60peer)
guard()
d={'status':'passed_independent_full_original_feedback_norm28_one_new_component_review','errors':[],'reviewer':'/root/foundations_recovery28','started_at_utc':started,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(packet),'source':ref(source),'exact_old27_entire_source_prefix_preserved':True,'complete_new_public_body_and_namespace_read':body,'complete_selected_norm_dependency_source_read':ref(norm),'original_native_trial_entire_body_and_time':a,'actual_warning_count':warnings,'original_native_raw_log':ref(raw),'component_decision':{'name':j['new_public_names'][0],'approved':True,'missing_clauses':[],'mathematical_correspondence':'For finite K, the Pi infinity norm of each coordinate vector is bounded by its Euclidean norm. Applying that true norm theorem to WithLp.toLp2(tracking-v), then transitivity with the actual Euclidean feedback bound, constructs exactly the certificate feedback field. All original x,z∈X, v∈U and V<=delta hypotheses remain, as do vnext∈U and f(z,v)∈X in local contraction. Lower/positivity/contraction clauses are original assumptions; no all-stage feasibility is a premise.','adopted_domain_qualification':'The local successor-domain clause is the explicitly adopted Source56 typed-domain interpretation, not a consequence of current55 weaker ambient-scalar contraction alone. This is a conditional component approval only.','scope_extensions':'State S may be any normed additive group and K any finite type including empty; specialising to the primary Euclidean state/input dimensions preserves its original hypotheses.'},'prior_full27_independent_decision':{'ref':j['original_independent27_review'],'original_reviewed_at_utc':prior['reviewed_at_utc'],'original_completed_at_utc':prior['completed_at_utc'],'entire_original_body_and_time_preserved_by_exact_reference':True},'original_request_preparation_observation':j['request_preparation_observation'],'separate_source60_narrow_primary_parser_peer':ref(source60peer),'current55_source_selected1175_assets31_owners5_guarded_before_after':True,'closed_evidence_sha256':closed,'whole_exercise18_approved':False,'whole_material_units_approved':False,'canonical_source_owner_proof_publication_write_claimed':False,'compiler_or_new_kernel_execution_claimed':False,'remaining_full_scope':['Actual attained finite-horizon MPC optimizer/controller and positive horizon selection.','Actual all-time controller evolution, safe/convergent switched outcome, and fixed IID validation composition.','Source56/60 remain unapplied; all whole18/current737739 coverage decisions remain pending.'],'scope':'Full one-new-body mathematical component review with a measured native evidence reader; runtime records the reader, not the preceding manual reading. Exact old27 full review/body/time remains referenced without recursively nesting it.'}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'component_approved':True,'whole18_approved':False,'warnings':warnings}))
