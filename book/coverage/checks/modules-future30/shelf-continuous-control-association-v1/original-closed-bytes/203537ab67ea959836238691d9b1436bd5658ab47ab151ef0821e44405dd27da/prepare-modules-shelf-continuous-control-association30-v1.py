from pathlib import Path
import hashlib,json,importlib.util,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/shelf-continuous-control-association-v1'
assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
aliases={}
def copy(p):
 p=Path(p);q=B/'original-closed-bytes'/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.write_bytes(p.read_bytes())
 assert sha(q)==sha(p)
 z=ref(q);aliases[str(p)]=z;return z
S=Path('/tmp/CompleteModulesShelfSafeContinuousControl30-draft-v3.lean')
records=[Path('/tmp/modules-shelf-safe-continuous-control-owner29-trial'+str(i)+'.json') for i in range(1,4)]
final=json.loads(records[-1].read_bytes())
assert final['actual_exit_code']==0 and final['actual_runner_exit_code']==0 and not final['protection_errors']
assert sha(S)==final['source_sha256_before']==final['source_sha256_after']
I=R/'book/coverage/inventory-after-correction65.json';O=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json';P=R/'SafeLearning/viability.html'
assert sha(I)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert sha(O)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
assert sha(P)=='0b0a8a5710cd4ce278e30c1c7a5534ba5f4388c7956d60a1e701c02b572490c0'
old=R/'book/coverage/checks/modules-future30/shelf57-full-scope-v1/modules-shelf57-full-source-current-and-prospective-literal-independent-review-request30-v1.json'
peer=R/'book/coverage/checks/future30-core/shelf57-independent-applied30b-v1/modules-shelf57-all-components-current1122-1131-prospective1126-independent-applied30b-with-association-gap-closed-peer-v1.json'
narrow=R/'book/coverage/checks/future30-core/shelf-rounding-independent-foundations-v1/modules-shelf-rounding-unnumbered-narrow-full-literal-parser-independent-foundations30-closed-peer-v1.json'
assert sha(old)=='b93889e3ce7b8b831812b9f08baa1649b081fe97ce6243292da9b97d9ef03fb2'
assert sha(peer)=='0871675302e18aa30f180ee6b751644b36d20ba66205205459227bf9e1a44342'
assert sha(narrow)=='f6b08448e34b08aaabde74602eaacafe8e9db36e28549fccf5533a62d1fc2fed'
oldj=json.loads(old.read_bytes());peerj=json.loads(peer.read_bytes())
assert peerj['errors']==[] and peerj['actual_controller_value_association_gap']
B.mkdir(parents=True)
spec=importlib.util.spec_from_file_location('shelf_continuous_names',R/'book/coverage/lean_names.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
decls=m.declarations(S.read_text());theorems=[x['name'] for x in decls if x['kind'] in ['theorem','lemma']]
hist=[]
for p in records:
 j=json.loads(p.read_bytes())
 assert j['source_unchanged'] and not j['protection_errors'] and j['actual_command']==['lake','env','lean',j['source']]
 assert j['actual_workdir']==str(R/'verification/lean')
 assert sha(j['source'])==sha(j['source_snapshot'])==j['source_sha256_before']==j['source_sha256_after']==j['source_snapshot_sha256']
 assert sha(j['raw_log'])==j['raw_log_sha256']
 hist.append({'actual_native':copy(p),'source':copy(j['source']),'source_snapshot':copy(j['source_snapshot']),'raw_log':copy(j['raw_log']),'actual_exit_code':j['actual_exit_code'],'actual_warning_headers':len(re.findall(r'^.*?:\d+:\d+: warning:',Path(j['raw_log']).read_text(),re.M)),'original_actual_times':{k:j[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
primary=[]
for name in ['Analysis/SpecialFunctions/ImproperIntegrals.lean','MeasureTheory/Integral/IntervalIntegral/Basic.lean','MeasureTheory/Integral/IntegrableOn.lean','MeasureTheory/Integral/Bochner/Basic.lean','MeasureTheory/Integral/Bochner/Set.lean','MeasureTheory/Function/L1Space/Integrable.lean','MeasureTheory/Constructions/BorelSpace/Order.lean','Order/ConditionallyCompletePartialOrder/Basic.lean','Algebra/Order/Field/Basic.lean','Order/MinMax.lean']:
 p=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_package_path_historical_metadata':str(p),'entire_actual_physical_API_source':copy(p)})
for p in [__file__,'/tmp/run-modules-shelf-continuous-control-association30-preparation-v1.py','/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',R/'book/coverage/lean_names.py']:
 copy(p)
request={'status':'prepared_actual_continuous_safe_shelf_control_return_attainment_and_ledge_infimum_full_association_review_request','source':copy(S),'actual_public_theorem_count':len(theorems),'actual_public_theorem_names':theorems,'actual_public_declaration_count':len(decls),'actual_public_other_declarations':[x for x in decls if x['kind'] not in ['theorem','lemma']],'genuine_original_native_history':hist,'original_shelf57_full_request':ref(old),'original_shelf57_full_independent_intentional_gap_peer':ref(peer),'original_rounding8phrase_independent_peer':ref(narrow),'entire_current_and_prospective_context':oldj['entire_current_and_prospective_context'],'current_inventory':ref(I),'immutable_original_owner29':ref(O),'current_page_original_byte_alias':copy(P),'entire_primary_API_sources':primary,
'actual_model_scope':{'state':'Continuous integral trajectories x(t)=x0+integral0..t u, initial state0<=x0<=L.','controls':'Actual safe driving speeds -v,0,v; positive v; interval-integrable on each finite positive-time interval. This admits time-dependent safe controls and includes the constructed stationary right-feedback maximizer.','event_driven_domain':'All positive-time states stay in[0,L]; the right wall stops and absorbs. The ledge belongs to the safe branch and may be held with zero control. A velocity definition with exactly the printed safe/fall/absorbing branches is added and the true integral dynamics bridge is proved. No desired return/optimality/value property is an admissibility premise.','return':'Genuine Bochner integral on positive infinite time of exp(-t/tau) times actual state reward -1 before the wall and0 at the wall, for positive tau. Integrability is proved, including endpoint-null equalities.','maximizer':'Constructed x(t)=min(x0+vt,L); actual control v before travel time and0 thereafter. Its finite interval integral is explicitly computed. This stationary right-feedback path is safe and satisfies the printed dynamics.','value':'Every actual safe controlled path has x(t)<=x0+vt and cannot reach the wall before(L-x0)/v. The actual reward is bounded above by right driving pointwise on positive time; the integral is therefore bounded. The actual right return is integrated exactly using genuine exponential improper integrals. IsGreatest, actual sSup equality and attained ledge IsLeast/sInf are derived.','formula':'Actual constrained value=tau*(exp((x0-L)/(v*tau))-1); attained safe-state infimum atx0=0 equals-tau*(1-exp(-(L/v)/tau)); default L1,v1/5 exactly supplies the old -tau*(1-exp(-5/tau)) definition.'},
'full_scope_review_requested':[
 {'scope':'Current entire viability node1130','whole_decision_requested':True,'correspondence':'Combine the unchanged original57 globally derived threshold shape/minimum/Taylor/limit conclusions with the new actual continuous-controller optimum and attained ledge infimum. Assess every repeated constrained-value clause, not only the scalar expression.'},
 {'scope':'Current entire Exercise7.3','whole_expected_pending':True,'reason':'The original current numerical rounding equality/ratio precision remains unchanged; the original fullpeer remains exact.'},
 {'scope':'Prospective eight-phrase corrected entire Exercise7.3','whole_decision_requested_conditional_on_actual_later_application':True,'correspondence':'Use all original57 full clause approvals, the independent8phrase literal correction and the new actual safe-control association. Source correction is still unnumbered and unapplied. No generic preceding safety theorem, arbitrary unsafe ODE optimum, or neighboring family promotion is requested.'}],
'original_gap_to_actual_proof_association':{'original_peer_gap_exact':peerj['actual_controller_value_association_gap'],'actual_substantive_dependencies':['SafeShelfControl','actual_control_derives_speed_bound','actual_no_safe_control_reaches_wall_early','actual_right_control_integral','actual_right_driving_is_safe_control','actual_discount_tail_integral','actual_infinite_right_driving_return','actual_every_safe_controller_return_upper_bound','actual_safe_optimum_is_attained_by_right_driving','actual_constrained_value_from_continuous_controls','actual_ledge_attains_constrained_value_infimum','actual_default_ledge_infimum_is_printed_formula','actual_safe_control_matches_printed_velocity','actual_safe_control_integral_is_printed_dynamics','actual_right_state_is_clipped_right_motion','actual_right_control_is_stationary_feedback','actual_safe_optimum_explicit_travel_distance']},
'original_verdict_body_and_time_preserved':True,'independent_full_semantic_review_pending':True,'source_ordinal_reserved':False,'source_applied':False,'compiler_or_parser_launched_by_this_preparation':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{z['file']:z['sha256'] for z in aliases.values()}}
for p in [old,peer,narrow,I,O]:request['required_evidence_artifacts_sha256'][ref(p)['file']]=sha(p)
for original in [oldj,peerj,json.loads(narrow.read_bytes())]:
 for n,h in original.get('required_evidence_artifacts_sha256',{}).items():
  assert n not in request['required_evidence_artifacts_sha256'] or request['required_evidence_artifacts_sha256'][n]==h
  assert sha(R/n)==h
  request['required_evidence_artifacts_sha256'][n]=h
p=B/'modules-shelf-continuous-control-full-association-and-prospective-whole-composition-review-request30-v1.json';p.write_text(json.dumps(request,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':ref(p),'public_theorems':len(theorems),'public_declarations':len(decls),'history_codes':[j['actual_exit_code'] for j in hist],'warnings':[j['actual_warning_headers'] for j in hist],'closed_refs':len(request['required_evidence_artifacts_sha256'])}))
