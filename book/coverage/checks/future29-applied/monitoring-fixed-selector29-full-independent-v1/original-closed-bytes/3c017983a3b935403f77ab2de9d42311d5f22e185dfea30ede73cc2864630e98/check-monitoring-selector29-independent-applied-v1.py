from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased'); REQ=R/'book/coverage/checks/future29-core/monitoring-fixed-selector29-v1/core-monitoring-fixed-selector29-full-semantic-review-request-v1.json'; C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):p=Path(q['file']);return p if p.is_absolute() else R/p
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
ctx=json.loads(C.read_bytes());pins={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 for n,h in pins.items():assert sha(R/n)==h,n
assert ctx['status']=='actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'
guard();before={n:sha(R/n) for n in pins}
assert sha(REQ)=='298fa499667b537f2e95c0655f4854e4870303baeba756f36066b75f2f4bfff4'
d=json.loads(REQ.read_bytes());closed={str(REQ):sha(REQ),str(C):sha(C),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q) if isinstance(q,dict) else Path(q)
 if isinstance(q,dict):assert sha(p)==q['sha256'],str(p)
 assert p.is_file();closed[str(p)]=sha(p);return p
aliases=d['original_TMP_receipts_sources_snapshots_raw_logs_and_context']
for original,q in aliases.items():
 p=add(q);assert p.resolve().is_relative_to(R)
 o=Path(original)
 if o.exists():assert sha(o)==sha(p),original
src=add(d['final_actual_source']);s=src.read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
ns='SafeLearning.CompleteCoreMonitoringFixedSelector29.'
parsed=[{'name':ns+n,'kind':k} for k,n in re.findall(r'^(def|theorem)\s+(\w+)',s,re.M)]
assert parsed==d['source_level_public_declarations'] and len(parsed)==29 and sum(q['kind']=='theorem' for q in parsed)==16
natives=[];warnings=[]
for i,expected in zip(range(1,7),[1,1,0,1,0,0]):
 q=aliases[f'/tmp/root-core-monitoring-fixed-selector29-trial{i}.json'];p=add(q);n=json.loads(p.read_bytes())
 assert type(n['actual_exit_code']) is int and n['actual_exit_code']==expected and n['protection_errors']==[]
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert n['actual_source64_installed28_context']['sha256']=='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
 raw=add(aliases[n['raw_log']]);snapshot=add(aliases[n['source_snapshot']]);original_source=add(aliases[n['source']])
 assert n['raw_log_sha256']==sha(raw) and n['source_snapshot_sha256']==n['source_sha256_before']==n['source_sha256_after']==sha(snapshot)==sha(original_source)
 assert n['source_unchanged'] is True and n['finished_at_utc']>=n['started_at_utc']
 natives.append(q);warnings.append(len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M)))
assert warnings==[7,8,2,2,2,2] and sha(snapshot)==sha(src)
for k in ['source_literal','source64_inventory','original_owner28_source60','actual_source61_to64_application']:add(d[k])
inv=json.loads((R/'book/coverage/inventory.json').read_bytes());units={x['key']:x for x in inv['material_source_units']};ex={x['key']:x for x in inv['exercises']};owner=json.loads((R/'book/coverage/core.json').read_bytes())
row=d['whole_exercise21_literal_and_current_all_claims'];live=next(x for x in owner['exercises'] if x['inventory_key']=='cmdp.html::exercise-21');assert row==live
for k in ['source_text','source_sha256','text_sha256']:assert row[k]==ex['cmdp.html::exercise-21'][k]
rows=d['entire_node1141_current_all_claims'];actual=[x for x in owner['material_claims'] if 'cmdp.html::node-1141' in x.get('source_unit_keys',[])]
assert rows==actual
for x in rows:
 for k in ['source_text','source_sha256','text_sha256']:assert x[k]==units['cmdp.html::node-1141'][k]
assert d['whole_exercise21_or_node1141_approval_requested'] is False
selected=['CompleteMonitoringDeterministicPath23.lean','CompleteMonitoringFaceClassification23.lean','CompleteFiniteMarkovPathCorrespondence.lean','CompleteFiniteControlledPathMeasure.lean','CompleteFiniteControlledPathMeasureLaws.lean','CompleteFiniteControlledPathFlow.lean','CompleteMonitoringMeans22.lean','CompleteMonitoringGeometry21.lean']
for name in selected:add(R/'verification/lean/SafeLearning'/name)
api=R/'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean';add(api)
assert 'theorem integral_congr_ae' in api.read_text()
components=[
 {'component_id':'actual_stationary_selector_all_prices_and_initial_states','lean_declarations':[q['name'] for q in parsed[:9] if q['kind']=='theorem'],'hypotheses':['Every real l1,l2; every initial R0/R1/R2. The finite source transition is unchanged and only the initial Dirac mass varies.','The action rule chooses R1 at an R0 price tie, stays in a region only above 1 and at least the competing price, and returns at threshold equality.'],'reason':'InitialModel retains the actual original source transition. The policy is stationary and normalized. Actual state marginal induction and the constructed controlled-path joint-mass theorem derive probability-one orbit agreement, then countable AE intersection gives all times simultaneously. No desired controlled outcome is supplied.','approved':True,'missing_clauses':[]},
 {'component_id':'derived_periodic_tail_and_all_horizon_fractions','lean_declarations':[q['name'] for q in parsed[9:23] if q['kind']=='theorem'],'hypotheses':['Every real price pair and initial state. Tail inverse-horizon bound uses N>0; full 3/T bound uses T>=2.','The probability law is the actual stationary controlled law constructed from those prices and the initial state.'],'reason':'Finite price/state case analysis proves advance^4=advance^2 and induction proves a period-one-or-two tail after two steps. The alternating-indicator relation derives the bounded potential telescope and true full running fractions with 3/T error. Their convergence is proved, then transferred along the almost-sure orbit agreement. Periodicity, limiting frequencies and all-time agreement are conclusions, not hypotheses.','approved':True,'missing_clauses':[]},
 {'component_id':'actual_expected_fractions_and_global_lagrangian_maximality','lean_declarations':[q['name'] for q in parsed[23:] if q['kind']=='theorem'],'hypotheses':['Every real price pair, including negative prices, price ties and equality at threshold 1. Every initial state.','IsMaximizer is exactly the original linear monitoring Lagrangian on the full source achievable quadrilateral.'],'reason':'Each finite expected count equals the actual deterministic count by AE congruence of the integral and the probability law; the limit follows without exchanging limits and integrals. Explicit limiting fractions lie in the full quadrilateral. Four direct global vertex bounds and complete price/state case analysis prove maximality. At equal prices above 1 an initial region may stay there, while initial R0 selects R1; each tied endpoint is a maximizer. Equality at threshold chooses a returning endpoint. No claim of a unique maximizing policy or forced transient route is made.','approved':True,'missing_clauses':[]}
]
guard();assert before=={n:sha(R/n) for n in pins}
out=Path('/tmp/monitoring-selector29-independent-applied-findings-v1.json');assert not out.exists()
result={'status':'passed_independent_full_monitoring_fixed_selector29_component_semantic_review','reviewer':'/root/applied_next','review_completed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'proof_source':d['final_actual_source'],'all29_public_declarations_16_theorems_and_all_full_bodies_and_definitions_read':True,'exact_source_literal_keys':['cmdp.html::exercise-21','cmdp.html::node-1141'],'full_current_exercise_and_node_and_section3_section7_context_read':True,'components':components,'whole_exercise21_or_node1141_approved':False,'remaining_gaps':['Generic Section7 stochastic feasibility and expected near-optimality under exact-maximizer A1-A3, including genuine conditional epoch association and limits.','The new proof closes only the arbitrary-price fixed-selector route; prior explicit changing-price cycle and finite-epoch bias remain separate immutable components.'],'original_six_actual_trials_body_times_and_sources_preserved':natives,'actual_exit_codes':[1,1,0,1,0,0],'actual_warning_header_counts':warnings,'historical_trials_context':'All six actual Lean receipts retain their original Source64 context and timestamps. This independent reader is a new Source65 guarded read; it does not relabel those compiler executions. The entire CMDP literal/page is unchanged by Source65.','current65_guard_scope':{'held_selected_sources':1186,'current_assets':31,'owner_ledgers':5,'context':ref(C)},'selected_sources_used':list(map(lambda n:ref(R/'verification/lean/SafeLearning'/n),selected)),'used_integral_congruence_API':ref(api),'no_Lean_rerun_or_source_owner_canonical_publication_mutation':True,'closed_evidence_sha256':closed,'errors':[]}
out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'findings':ref(out),'components_approved':True,'whole_exercise_or_node':False,'warnings':warnings}))
