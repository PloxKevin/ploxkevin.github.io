"""Fresh whole eight-clause exercise review; exact TMP standalone evidence only."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def check(r):assert H(path(r['file']))==r['sha256'];return path(r['file'])
def ref(n):return {'file':str(n),'sha256':H(path(n))}
OLD='/tmp/landscape15-selected-source52-full-gap-audit26-independent-foundations-v2.json'
assert H(OLD)=='9ab8efe7fbdd7e6d3f820f27999a743440f1adf2977b8a2754b5d9fbc0269fcd'
old=json.loads(Path(OLD).read_text())
CV='/tmp/applied-cvar-fractional-selector26-independent-foundations-eight-body-component-review-v1.json'
assert H(CV)=='8d0a85ce07e5c564e76847d5fc9fc96f6d2595d2691b50efcf2a1d9dcd4b7913'
cv=json.loads(Path(CV).read_text());assert 'passed'in cv['status']and cv['errors']==[]and len(cv['components'])==8
inv=json.loads((ROOT/'book/coverage/inventory.json').read_text());assert H(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
unit=next(x for x in inv['exercises']if x['key']=='landscape.html::exercise-15');assert unit==old['entire_inventory_record']
html=(ROOT/unit['source']).read_text();assert H(ROOT/unit['source'])==unit['source_sha256'];lines=html.splitlines(keepends=True)
contexts={'entire_section1_original_html':''.join(lines[74:174]),'entire_section3_original_html':''.join(lines[236:307]),'entire_exercise15_original_html':''.join(lines[636:659])};assert contexts==old['full_context']
ledger=json.loads((ROOT/'book/coverage/modules.json').read_text());pending=next(x for x in ledger['exercises']if x['inventory_key']==unit['key']);assert pending==old['entire_original_pending_row_body_and_all_identity_fields']
assert pending['status']=='pending'and pending['claims'][0]['status']=='pending'
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-24-selection.json').read_text());audit=json.loads(check(old['actual_selected24_audit']).read_text());assert audit['status']=='passed'and audit['proof_file_count']==1144and audit['theorem_count']==9279
for name,row in old['selected24_sources_and_entire_bodies'].items():
 assert H(ROOT/name)==row['sha256']==selection['proof_files'][name]['sha256']and(ROOT/name).read_text()==row['entire_source_text_read']
 assert row['original_selected_evidence_sha256']==selection['proof_files'][name]['evidence_sha256']
 assert row['selected24_public_declarations']==sorted(d['name']for d in audit['declarations']if d['file']==name)
wind=Path('/tmp/CompleteModulesLandscapeWindClassification26.lean');assert H(wind)=='804c80ef5a6b743c752efe130616174690736abd08267d5f7bdf45bbdd635545'
wbody=wind.read_text();assert len(re.findall(r'^theorem ',wbody,re.M))==4and not re.search(r'\b(sorry|admit|axiom)\b',wbody)
actual_name='/tmp/root-landscape-wind-classification26-trial1.json';actual=json.loads(Path(actual_name).read_text());assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0
assert actual['actual_command']==['lake','env','lean',str(wind)]and actual['actual_workdir']==str(ROOT/'verification/lean')
assert actual['source_sha256_before']==actual['source_sha256_after']==H(wind)
assert H(actual['source_snapshot'])==actual['source_snapshot_sha256']==H(wind)
assert H(actual['raw_log'])==actual['raw_log_sha256']and Path(actual['raw_log']).read_bytes()==b''
check(actual['original_actual_runner'])
check(cv['proof_source']);assert path(cv['proof_source']['file']).read_text()==cv['complete_source_body']
for row in cv['all_original_actual_trials_and_raw_history']:
 assert json.loads(check(row['record']).read_text())==row['entire_original_actual_record'];check(row['raw_log']);check(row['source_snapshot'])
components=copy.deepcopy(old['eight_literal_clause_decisions'])
for row in components:
 row['decision']='approved_complete_whole_exercise_clause';row['missing_clauses']=[];row['remaining_gaps']=[]
 if row['clause']==3:
  row['lean_declarations']=['SafeLearning.CompleteModulesLandscapeWindClassification26.'+s for s in ['actual_source_wind_guarantee_is_same_controller_robust_forward_invariance','actual_robust_certificate_protects_each_admissible_initial_gust_and_time','actual_fixed_controller_robust_safety_implies_gustwise_controller_existence','actual_gustwise_recovery_does_not_supply_one_robust_controller']]
  row['hypotheses']=['Arbitrary time/state/controller trajectory family representing the stated closed loop; arbitrary normed wind space and source model-specific admissible wind class.','The same fixed controller is chosen before gust; all certified initial states, every admitted wind sequence with pointwise norm<=2, and every relevant time are quantified.','Classification of the hypothesized robust guarantee; no unprovided drone dynamics, independent distribution or physical invariant cage certificate is inferred.']
  row['reason']='The two complete definitions and genuine iff preserve all quantifiers and the exact norm2 bound. A robust certificate directly protects each admitted run. The existential implication and true +/-2 cancellation counterexample verify that choosing a new controller after seeing each gust is weaker. This closes exactly the earlier all-initial/same-controller/all-gust/all-time classification gap.'
 if row['clause']==4:
  row['lean_declarations']=cv['public_theorems']+row['lean_declarations']
  row['hypotheses']=['A genuine underlying episode probability law; measurable integrable real episode cost, including arbitrary atomic distributions.','The average of the worst fractional1/20 outcomes uses an explicit fractional threshold atom; alpha=19/20 and the bound is strict<10.']
  row['reason']='All eight complete new bodies derive an attained quantile from true CDF right continuity, the actual pushed-forward strict-tail and atom masses, and a valid mass-matched measurable selector even at zero boundary mass. Complete selected duality then derives an attained greatest tail value equal to the global least RU objective. The exact factor20 yields worst fractional5% cost<10 iff an attained RU certificate q+20E[(Z-q)+]<10. Selector existence and equality are conclusions, not premises; no finite-support, continuity or empirical-law assumption is added.'
# Check all exact declarations of earlier clauses and the distinct new bodies.
new_names=set(cv['public_theorems'])|set(components[2]['lean_declarations']);selected_names={d['name']for d in audit['declarations']}
for row in components:
 assert row['lean_declarations']and all(n in selected_names|new_names for n in row['lean_declarations'])
 assert row['missing_clauses']==[]
for n,r in selection['proof_files'].items():assert H(ROOT/n)==r['sha256']
for n,h in inv['source_sha256'].items():assert H(ROOT/n)==h
report={'status':'independent_source52_landscape15_complete_eight_clause_full_source_review26_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent','inventory':ref('book/coverage/inventory.json'),'source_html':ref(unit['source']),'entire_inventory_record':unit,'full_context':contexts,'whole_exercise_approved':True,'missing_clauses':[],'remaining_gaps':[],'exercise_components':components,'eight_literal_clause_decisions':components,'empirical_vs_population_caveat':old['empirical_vs_population_caveat'],'original_source52_gap_audit':ref(OLD),'entire_original_gap_audit_body_time_and_two_missing_bridges_retained':old,'current_modules_ledger_at_read':ref('book/coverage/modules.json'),'entire_original_pending_row_body_and_all_identity_fields':pending,'all_original_pending_row_bytes_unchanged':True,'selected24_sources_and_entire_bodies':old['selected24_sources_and_entire_bodies'],'actual_selected24_audit':old['actual_selected24_audit'],'wind_source':ref(wind),'complete_wind_source_body':wbody,'wind_original_actual_standalone':ref(actual_name),'wind_entire_actual_record_and_time':actual,'cvar_independent_eight_body_component_peer':ref(CV),'entire_cvar_component_peer_body_and_time_retained':cv,'new_TMP_public_theorem_count':12,'new_TMP_sources':2,'coverage_complete':False,'scope':'Fresh whole exercise15 classification only: every question/answer clause and empirical-law caveat reviewed with full Section1/3 context and original complete selected dependencies. The objects being classified are hypothesized guarantees; no physical model or actual drone behavior is invented. Stability requires the explicit positive compact strict certificate, initialized SafeOpt safety retains all genuine source RKHS/confidence/noise/query rules, and empirical data is not silently a population law. New wind4 and cumulative CVaR8 have actual standalone0 only. No canonical/named/aggregate26 execution, whole CVaR material156/1351 endpoint/inverse-transform theorem, current25 offer amendment or live owner/HTML/inventory mutation is inferred. Original pending status and every old review/body/time remain exact history.'}
OUT=Path('/tmp/landscape15-source52-twelve-new-bodies-independent-foundations-whole-observations26-v1.json');assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'whole_exercise_approved':True,'missing_clauses':[],'new_public_theorems':12,'observation':ref(OUT)}))
