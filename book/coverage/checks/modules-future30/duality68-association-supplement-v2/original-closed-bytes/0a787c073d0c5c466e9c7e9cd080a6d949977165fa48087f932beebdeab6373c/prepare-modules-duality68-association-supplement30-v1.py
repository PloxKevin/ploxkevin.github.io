from pathlib import Path
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/duality68-association-supplement-v1'
assert not B.exists();B.mkdir(parents=True)
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
P=R/'book/coverage/checks/modules-future30/duality55-components-v1/modules-duality55-full-source-current-literal-component-review-request30-v2.json'
Q=R/'book/coverage/checks/modules-future30/duality55-independent-foundations-v1/modules-duality55-full-source-six-components-independent-foundations30-closed-peer-v2.json'
assert sha(P)=='baab5e6bf29af3a4e306c3c6954bbd7b906926d755880bafb015d0bf058892c0'
assert sha(Q)=='155cf3e814e7a7f9651588323fdcf1614d089f45187f8be5053693eb19160316'
p=json.loads(P.read_bytes());q=json.loads(Q.read_bytes())
refs={**p['required_evidence_artifacts_sha256'],**q['required_evidence_artifacts_sha256']};aliases={**p['original_closed_byte_aliases'],**q['original_closed_byte_aliases']}
def copy(x):
 x=Path(x);h=sha(x);z=B/'original-closed-bytes'/h/x.name;z.parent.mkdir(parents=True,exist_ok=True)
 if not z.exists():
  with z.open('xb')as f:f.write(x.read_bytes())
 assert sha(z)==h;r={'file':z.relative_to(R).as_posix(),'sha256':h,'bytes':z.stat().st_size};aliases[str(x)]=r;refs[r['file']]=h;return r
def direct(x):
 x=Path(x);r={'file':x.relative_to(R).as_posix(),'sha256':sha(x),'bytes':x.stat().st_size};refs[r['file']]=r['sha256'];return r
families=[]
for tag,cap,new,last,expected,names_count,defs_count,h in [
 ('clock','Clock',6,4,[(5,0,1,'36'),(6,0,1,'37')],37,29,'73ff75fd750a53b73c4942fb05b681f9947e9c5450d2481817bf28617dd92fe7'),
 ('expectation','Expectation',10,8,[(9,1,1,'31'),(10,0,3,'31')],31,14,'8071605270f5349878a9ea79d4167fe4b9e79589f1acfcb4d84d38caf4b6618b')]:
 s=Path(f'/tmp/CompleteModulesViabilityDual{cap}30-draft-v{new}.lean');old=Path(f'/tmp/CompleteModulesViabilityDual{cap}30-draft-v{last}.lean')
 t=s.read_text();assert sha(s)==h and s.read_bytes().startswith(old.read_bytes())
 ds=lean_names.declarations(t);ns=[d['name']for d in ds if d['kind']in ['theorem','lemma']];defs=[d['name']for d in ds if d['kind']in ['def','abbrev']]
 assert (len(ns),len(defs))==(names_count,defs_count)
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(t))
 hist=[]
 for j,code,warnings,number in expected:
  f=Path(f'/tmp/modules-viability-dual-{tag}{number}-owner29-trial{j}.json');n=json.loads(f.read_bytes());raw=Path(n['raw_log']).read_text()
  assert n['actual_exit_code']==n['actual_runner_exit_code']==code and n['protection_errors']==[] and n['source_unchanged']
  assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
  assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==sha(n['source_snapshot'])==n['source_snapshot_sha256']
  assert sha(n['raw_log'])==n['raw_log_sha256']
  assert [n[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
  wc=len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M));assert wc==warnings
  hist.append({'actual_native':copy(f),'actual_source':copy(n['source']),'actual_source_snapshot':copy(n['source_snapshot']),'actual_raw_log':copy(n['raw_log']),'actual_exit_code':code,'actual_warning_count':wc,'original_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'original_body_and_times_untouched':True})
 oldnames=[d['name']for d in lean_names.declarations(old.read_text())if d['kind']in ['theorem','lemma']]
 assert ns[:len(oldnames)]==oldnames
 families.append({'source':copy(s),'full_source_body':t,'public_theorem_count':len(ns),'public_theorem_names':ns,'public_definition_count':len(defs),'public_definition_names':defs,'new_theorem_names':ns[len(oldnames):],'old_final_source':copy(old),'entire_old_final_source_exact_byte_prefix':True,'new_genuine_native_history':hist,'final_trial_is_kernel0':True,'final_warning_count':expected[-1][2]})
for x in ['/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',__file__,'/tmp/run-modules-duality68-association-supplement30-preparation-v1.py','/tmp/modules-dual-clock-stationary-append30-v5.txt','/tmp/modules-dual-clock-kernel-append30-v6.txt','/tmp/modules-dual-expectation-zero-budget-append30-v9.txt']:copy(x)
d={'status':'prepared_actual_kernel0_duality68_exact_prefix_association_supplement_for_independent_semantic_review','original55_component_request':direct(P),'original55_independent_full_peer':direct(Q),'original55_peer_body_and_times_unchanged':True,'families':families,'public_theorem_count':68,'public_definition_count':43,'private_clock_proof_count':1,
 'component_review_scopes':[{'id':'actual_stationary_clock_common_all_start_optimizer_at_every_actual_iterate','scope':'Actual stationary feedback trajectory equals shifted original history. Genuine full infinite gain/risk and arbitrary-history classification hold at each initial clock. The same threshold policy k globally maximizes from every starting clock at lambda_k=1-2^-k, including the early/late starting-state split. Genuine eta1 iteration at start0 stays unsafe. No desired global optimum or trajectory premise.'},
 {'id':'actual_clock_viability_kernel_and_uniform_post_exit_bound','scope':'Actual viability predicate is existence of a stationary feedback avoiding failure at every time. Exactly the surviving clock states are viable; the sole unviable state is already failed at time0 under every feedback, yielding the actual uniform immediate post-exit bound.'},
 {'id':'actual_source_zero_budget_CMDP_and_AE_safety_association','scope':'For nonnegative risk, the actual supremum over risk<=0 is exactly the actual zero-risk primal. Actual expected nonnegative risk<=0 is exactly AE zero risk, with genuine integrability. Dependent subtype supremum reindex is proved by explicit range equality, not inferred by simp.'},
 {'id':'positive_budget_oscillation_countermodel_only','scope':'A flat zero reward and zero cost family has genuine exact global maximizers, hence is also inexact for any positive tolerance. Its positive-budget projected process started at0 remains0 at every time and has zero increments. This disproves the current blanket oscillation assertion, and supports a separate can-oscillate wording correction; it does not prove oscillation for deep RL.'}],
 'whole_exercise_review_requested':False,'whole_exercise_current_pending':True,'explicit_remaining_whole_exercise_associations':['Generic finite deterministic dynamic-programming common stationary optimizer existence and finite-CMDP LP dual multiplier/strong-duality existence remain pending.','Actual physical Chain49 attained-return and delta2 expected profile association remains pending its full semantic peer/composition.','Common stationary clock attainment is proved at every actual nonterminating iterate; generic attainment for arbitrary penalty values is not yet a separate theorem.','The final current positive-budget oscillation assertion requires a separately independently reviewed narrow qualifier; no literal is changed here.'],
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,'remote_full_primary_bodies_kept_TMP_offline_only':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':refs}
assert all((R/f).resolve().is_relative_to(R.resolve())and sha(R/f)==h for f,h in refs.items())
O=B/'modules-duality68-exact-prefix-association-supplement-review-request30-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'public_theorems':68,'closed_refs':len(refs),'aliases':len(aliases)}))
