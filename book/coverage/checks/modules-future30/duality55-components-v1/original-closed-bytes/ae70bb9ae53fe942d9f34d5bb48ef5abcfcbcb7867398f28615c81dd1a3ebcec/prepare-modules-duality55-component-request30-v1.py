from pathlib import Path
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/duality55-components-v1'
assert not B.exists();B.mkdir(parents=True)
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(q)==h
 z={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=z;return z
owner=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(owner)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
M=json.loads(owner.read_bytes());Ipath=R/'book/coverage/inventory-after-correction65.json';I=json.loads(Ipath.read_bytes())
assert sha(Ipath)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
key='viability.html::exercise-19';e=next(x for x in M['exercises']if x['inventory_key']==key);ie=next(x for x in I['exercises']if x['key']==key)
assert e['status']=='pending'and len(e['claims'])==7 and all(x['status']=='pending'for x in e['claims'])
page=R/'SafeLearning/viability.html';assert sha(page)==e['source_sha256']=='0b0a8a5710cd4ce278e30c1c7a5534ba5f4388c7956d60a1e701c02b572490c0'
lines=page.read_text().splitlines(keepends=True)
context={'entire_current_exercise_inventory_row':ie,'entire_original_pending_exercise_owner_row':e,
 'full_exercise7_5_and_answer_context_lines941_957':''.join(lines[940:957]),
 'full_source_Section3_penalty_setup_lines251_307':''.join(lines[250:307]),
 'full_source_Section4_theorem_context_lines308_479':''.join(lines[307:479]),
 'full_source_Section5_and_duality_context_lines480_581':''.join(lines[479:581]),
 'context_serialization':'Exact physical source.splitlines(keepends=True) concatenation; no whitespace normalization.'}
cp=B/'modules-duality55-full-current-context-v1.json';cp.write_text(json.dumps(context,indent=2,ensure_ascii=False)+'\n')
families=[]
for tag,cap,last,expected,counts,warnings,sourcehash in [
 ('clock','Clock',4,[1,0,1,0],(27,18),[1,1,4,1],'e943072a484381a573dd6f3732c90ff09ab576fd388d7f5fa27a2b68b49716a9'),
 ('expectation','Expectation',8,[1,1,0,1,0,1,0,0],(28,12),[3,0,0,4,1,0,0,0],'5b5a01382c7bc6f9fe1722668231695e2de364912de1bf8cc707172370a33ae2')]:
 S=Path(f'/tmp/CompleteModulesViabilityDual{cap}30-draft-v{last}.lean');t=S.read_text();ds=lean_names.declarations(t)
 names=[d['name']for d in ds if d['kind']in ['theorem','lemma']];defs=[d['name']for d in ds if d['kind']in ['def','abbrev']]
 assert (len(names),len(defs))==counts and sha(S)==sourcehash
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(t))
 hist=[]
 for j in range(1,last+1):
  z=Path(f'/tmp/modules-viability-dual-{tag}30-owner29-trial{j}.json');n=json.loads(z.read_bytes());raw=Path(n['raw_log']).read_text()
  assert n['actual_exit_code']==n['actual_runner_exit_code']==expected[j-1]and n['protection_errors']==[]and n['source_unchanged']
  assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
  assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==sha(n['source_snapshot'])==n['source_snapshot_sha256']
  assert sha(n['raw_log'])==n['raw_log_sha256']
  assert [n[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
  wc=len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M));assert wc==warnings[j-1]
  hist.append({'actual_native':copy(z),'actual_source':copy(n['source']),'actual_source_snapshot':copy(n['source_snapshot']),'actual_raw_log':copy(n['raw_log']),
   'actual_exit_code':n['actual_exit_code'],'actual_warning_count':wc,'original_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'original_body_and_times_untouched':True})
 families.append({'source':copy(S),'source_sha256':sha(S),'full_source_body':t,'public_theorem_count':len(names),'public_theorem_names':names,'public_definition_count':len(defs),'public_definition_names':defs,'genuine_native_history':hist,
  'final_trial_is_kernel0':True,'final_warning_count':warnings[-1],'earlier_sources_and_bodies_preserved_as_originals':True,'entire_earlier_final_source_byte_prefix_asserted':False})
selected=[copy(R/'verification/lean/SafeLearning'/(n+'.lean'))for n in ['CompleteDuality','CompleteAppliedViabilityPenaltyOrder20','CompleteAppliedViabilityExactPenalty20','CompleteAppliedViabilityEpisodeRisk20','CompleteCoreProjectedDualDrift29','CompleteMonitoringDualValue22']]
apis=[]
for n in ['Order/ConditionallyCompleteLattice/Indexed.lean','Order/ConditionallyCompleteLattice/Basic.lean','Topology/Order/Monotone.lean','MeasureTheory/Integral/Bochner/Basic.lean','Algebra/Order/GroupWithZero/Basic.lean','Data/Fintype/Card.lean','Data/Finset/Max.lean','Topology/Algebra/InfiniteSum/Basic.lean']:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/n;assert p.is_file();apis.append({'original_external_package_path_historical_metadata':str(p),'exact_physical_byte_alias':copy(p)})
receipts=[]
for n in ['paternain-1910.13393v1','svf-2105.12204v4']:
 p=Path('/tmp/modules-duality-primary30-v1')/(n+'-actual-http-receipt-v1.json');v=json.loads(p.read_bytes());assert v['actual_http_status']==200
 assert sha(v['original_body_tmp_path_historical_metadata'])==v['body_sha256'];receipts.append(copy(p))
for p in ['/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',__file__,'/tmp/run-modules-duality55-component-request30-preparation-v1.py','/tmp/modules-dual-clock-finite-risk-append30-v3.txt','/tmp/modules-dual-expectation-cumulative-append30-v4.txt','/tmp/modules-dual-expectation-last-append30-v6.txt']:copy(p)
d={'status':'prepared_actual_kernel0_dual_clock27_and_expectation28_for_independent_full_component_semantic_review',
 'families':families,'public_theorem_count':55,'public_definition_count':30,'private_clock_proof_count':1,
 'exercise_key':key,'whole_exercise_review_requested':False,'whole_exercise_current_pending':True,'current_full_context':copy(cp),'current_page_original_byte_alias':copy(page),'current_inventory':copy(Ipath),
 'original_owner29_candidate':{'file':owner.relative_to(R).as_posix(),'sha256':sha(owner)},'selected_complete_dependency_sources':selected,'primary_used_API_full_sources':apis,
 'actual_primary_HTTP_receipts':receipts,'remote_full_primary_bodies_kept_TMP_offline_only':True,
 'primary_used_scope':[{'url':'https://arxiv.org/html/1910.13393v1','scope':'Full used problem/dual definitions and Theorem1 proof: bounded reward and Slater suffice for zero gap via the occupancy-measure perturbation route. This general existence theorem is a primary attribution, not proved by these components.'},
 {'url':'https://arxiv.org/html/2105.12204v4','scope':'Used SectionsII/III actual failure risk and uniform attainment, Assumption1/Proposition1/Theorem2, SectionVB Example1/Remark5 read. Printed Example1 penalty coefficient is rescaled; the exact rescaling bridge is explicit. No entire-paper read is claimed.'}],
 'component_review_scopes':[
 {'id':'actual_dual_and_primal_from_genuine_bounded_reward_unit_risk','scope':'Actual ciSup definitions, boundedness, antitone/convex/one-Lipschitz continuity, weak duality, no strict zero-risk Slater point. Closed nonnegative dual-optimal ray is derived from a common safe attained optimum and genuine attained penalized maximizers/all-maximizers-safe above threshold for p>=0 only; no desired ray or dual value premise.'},
 {'id':'actual_Bochner_primal_dual_and_all_expected_maximizers_safety','scope':'Actual integrals from measurable bounded primitives; genuine supremum/integral identity from a common pointwise maximizing controller. Expected risk0 iff AE risk0, expected constrained ciSup equals the integral of actual pointwise constrained value from common safe optimum. Actual pointwise SVF derives zero gap and AE safety for every expected global maximizer through a nonnegative zero-integral gap. Common controller and SVF premises are explicitly the source assumptions, not supplied desired expectation identities.'},
 {'id':'actual_update_saddle_and_printed_bounded_risk_counterexample','scope':'True max0 projected zero-budget increment/nondecrease/strict iff positive risk/stops iff AE risk0. From actual feasible primal controller and actual zero duality gap derives complementarity, global Lagrangian maximizing saddle and actual primal optimality. No general gap/multiplier existence theorem is asserted. Genuine printed p10 tie has feasible optimal .1, infeasible1, feasible suboptimal0; paper penalty p is exactly ordinary multiplier p/10, explicitly proved.'},
 {'id':'actual_delayed_clock_all_history_nontermination','scope':'Actual infinite first-entry risk and gain, arbitrary history first-jump or safe classification, bounded physical rewards/unit risks, risk0 iff actual trajectory safe. Completed-square derivation proves controller k is an actual global maximizer at lambda_k=1-2^-k; exact eta1 projected update gives next lambda and never safe/stops despite all lambda>1 maximizers safe. No desired gain/risk/global-max/update premise is supplied.'},
 {'id':'actual_finite_feedback_termination','scope':'Genuine no-repeat first-failure argument and cardinality bound for every finite feedback map. Genuine discounted first-entry HasSum, support-minimum positive probability mass, expected positive-risk lower bound m*gamma^card X. Exact positive constant-step recursion plus source safe-above-threshold premise derives finite stopping by Archimedean growth; no desired lower bound or stopping premise.'},
 {'id':'printed_chain_profile_algebra_component_only','scope':'Actual max profile max(-7/4,-3/2-p/4) has nonnegative optimal ray [1,infinity), tie1/strict unsafe branch beyond1 and conservative15/2 comparison. The correspondence to actual Chain49 trajectories and delta2 expectation remains a separate pending association, not assumed approved.'}],
 'explicit_remaining_whole_exercise_associations':['Actual finite deterministic dynamic-programming common stationary optimizer existence and bibliographic finite-CMDP LP strong-duality existence must be independently addressed; the generic component assumes source uniform common attainment, and its saddle theorem assumes genuine zero gap.','Relate actual Chain49 physical trajectories, attained Bellman maxima and delta2 expectation to the exact max profile; await the full Chain49 semantic peer.','Explicitly relate the delayed clock to the source viable set, the uniform immediate failure bound after exit and common stationary attainment across all initial clock states.','Read the full final positive-budget/sampled-inexact oscillation sentence as a scoped empirical motivation, or identify any literal universal assertion requiring correction. No universal oscillation theorem is supplied.'],
 'failed_diagnostic_sources_native_bodies_and_original_times_preserved':True,'component_approval_by_author':False,'independent_full_semantic_review_pending':True,
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256']for r in aliases.values()}}
d['required_evidence_artifacts_sha256'][d['original_owner29_candidate']['file']]=d['original_owner29_candidate']['sha256']
O=B/'modules-duality55-full-source-current-literal-component-review-request30-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert all(sha(R/p)==h for p,h in d['required_evidence_artifacts_sha256'].items())
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'public_theorems':55,'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases)}))
