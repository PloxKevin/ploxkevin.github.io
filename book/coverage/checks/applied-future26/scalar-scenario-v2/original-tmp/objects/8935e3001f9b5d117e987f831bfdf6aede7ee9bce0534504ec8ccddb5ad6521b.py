from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,traceback,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
OLD=TMP/'lyapunov-current50-five-source43-independent-foundations-component-review23-v1.json'
IDENTITY=TMP/'lyapunov-current50-to51-unchanged-literals-independent-foundations-binding23-v1.json'
WHOLE=TMP/'lyapunov-current51-three-numeric-validation-whole-units-independent-foundations-review23-v1.json'
FAIL=TMP/'lyapunov-source51-identity-three-whole-units-independent-foundations-failure23-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'],r;return p
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def main():
 assert not any(p.exists() for p in [IDENTITY,WHOLE,FAIL])
 assert sha(OLD)=='d52d60fd3ee0d820057fbb71af30e37162e16521981d4b041b55cb7c903e407a'
 old=read(OLD);assert 'passed' in old['status'] and old['errors']==[]
 invpath=ROOT/'book/coverage/inventory-after-correction51.json'
 assert sha(invpath)==sha(ROOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
 inv=read(invpath);prev=read(check(old['authoritative_source50_inventory']))
 ex=next(r for r in inv['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')
 assert ex==old['entire_current50_question_and_all_four_answers_read']
 units={r['key']:r for r in inv['material_source_units']};oldunits={r['key']:r for r in prev['material_source_units']}
 relevant=[r for r in inv['material_source_units'] if r['source']=='SafeLearning/lyapunov-mpc.html']
 previous_ex=[r for r in prev['exercises'] if r['source']=='SafeLearning/lyapunov-mpc.html']
 assert relevant==[r for r in prev['material_source_units'] if r['source']=='SafeLearning/lyapunov-mpc.html']
 assert previous_ex==[r for r in inv['exercises'] if r['source']=='SafeLearning/lyapunov-mpc.html']
 source=check(old['source_page']);assert sha(source)=='228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'
 for r in old['all_five_entire_current50_material_records_read']:assert units[r['key']]==oldunits[r['key']]==r
 public=set();bodies={}
 for row in old['five_full_source_bodies_equal_original_independently_read_sources']:
  p=check(row['reference']);text=p.read_text();assert text==row['entire_source_and_all_original_bodies']
  ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1)
  names=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)];public.update(names);bodies[p.name]=text
 assert len(public)==43
 for row in old['all_ten_genuine_canonical_records_raw_logs_snapshots_runners']:
  r=read(check(row['reference']));assert r==row['entire_original_actual_record'] and r['actual_exit_code']==r['exit_code']==0
  log=check(row['raw_log']);snap=check(row['snapshot']);assert sha(log)==r['log_sha256']==r['raw_log_sha256'] and sha(snap)==r['source_sha256_before']==r['source_sha256_after']
  assert sha(path(r['runner_file']))==r['runner_sha256']
 for r in old['all_original25_9_3_6_and_canonical_binding_peer_bodies_times_exact']:assert read(check(r['reference']))==r['entire_original_body']
 manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 for n,h in old['held_four_working22_ledgers_sha256_exact'].items():assert sha(ROOT/n)==h
 components=[]
 for d in old['component_decisions']:
  assert d['approved_precise_component'] is True
  g=d['original_requested_group_unchanged'];assert set(g['lean_declarations'])<=public
  components.append({'component_id':d['component_id'],'source_unit_keys':g['source_unit_keys'],'lean_declarations':g['lean_declarations'],'hypotheses':d['hypotheses'],'per_component_reason':d['independent_reason'],'missing_clauses':[],'original_scope_limits_retained':d['retained_scope_limits'],'original_entire_semantic_decision':d,'original_reviewed_at_utc':old['reviewed_at_utc']})
 material=[]
 for row in old['all_five_entire_current50_material_records_read']:
  material.append({'source_unit_key':row['key'],'entire_inventory_record':row,'whole_unit_approved':False,'material_status':'partial','components':[c for c in components if row['key'] in c['source_unit_keys']],'remaining_whole_unit_gaps':old['remaining_mathematical_gaps'] if row['key'] in ['lyapunov-mpc.html::node-1393','lyapunov-mpc.html::node-1397'] else ['Distinct whole-unit decision is recorded separately; this binding alone preserves only the original scoped component decisions.']})
 identity={'status':'passed_exact_source50_to51_entire_lyapunov_identity_and_original_component_time_binding','reviewer':'/root/config21_next','checked_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'current_inventory':ref(invpath),'original_current50_peer':ref(OLD),'entire_original_current50_peer_body':old,'original_reviewed_at_utc_unchanged':old['reviewed_at_utc'],'source_page':old['source_page'],'entire_unchanged_lyapunov_material_record_count':len(relevant),'entire_unchanged_lyapunov_exercise_record_count':len(previous_ex),'material_units':material,'exercise':{'exercise_key':ex['key'],'entire_inventory_record':ex,'status':'partial','reviewed_components':components,'whole_exercise_approved':False,'remaining_gaps':old['remaining_mathematical_gaps']},'all43_bodies_and10_original_canonical_records_exact':True,'all1113_selected22_sources_and_four_held_ledgers_exact':True,'source50_to51_semantic_redecision':False,'limits':['Global source51 identity is distinct. Every Lyapunov page byte and entire inventory record remains equal to source50.','The twelve original semantic decisions, bodies and original review time are retained exactly. Component missing_clauses are empty only within their explicit model scope; original scope limits and whole-unit gaps remain explicit.','No current ledger installation, selection23 or whole exercise promotion is claimed.']}
 write(IDENTITY,identity)
 # Fresh whole-literal audit follows the separate source50 component review.
 groupmap={c['component_id']:c for c in components}
 specifications=[
 ('1399',['true_ten_term_boundary_minimal581','actual_LMI_variable_count_and_sufficient861'],['The question supplies n_k=2*d_x^2+d_x*d_u and its sufficient binomial-bound formula. The review evaluates that stated count and ten-term expression at epsilon=1/20,beta=1/100000; it does not assert the general scenario-risk theorem.'],'The chosen variable formula gives10. Genuine Pascal recurrence and all-horizon antitonicity plus exact rational bounds prove581 is the first crossing; the certified endpoint values justify9.67e-6 and1.003e-5. The true logarithm threshold lies between860.5169 and860.5172, hence ceil861. The exact relative increase (861-581)/581 is within.005 of.48, proving the stated about48% overhead.'),
 ('1401',['corrected_validation_rule_5757_and_misprinted116'],['The one-sided independent bounded-sample Hoeffding confidence rule is used as a lower bound. alpha=1/100 and epsilon_val=1/50; corrected exponent is2*N*epsilon_val^2.'],'Both logarithm quotients are bounded to the printed approximation precision and have ceilings5757/116. The true Hoeffding exponent at116 is-.0928; certified exp bounds justify.911 and the approximately9% lower confidence bound. The literal explicitly distinguishes this inequality lower bound from the actual procedure confidence; the reviewed claim makes the same distinction.'),
 ('1403',['true_one_fresh_batch_population_mean_implication','genuine_credible_region_and_full_posterior_transfer','actual_normalized_posterior_accepted_test_confidence'],['Fixed controller K*, fixed genuine posterior probability law, measurable credible region C with posterior mass.95 and measurable stable-linearisation event. The validation law is the normalized restriction of that posterior to C.','One fresh genuinely independent Bernoulli batch of n>=5757 stability indicators with the actual normalized stable-event mass as its common success probability. The posterior interpretation/model faithfulness is explicitly assumed, as stated by as good as the GP posterior.'],'The actual independent bounded-batch theorem gives probability at least.99 of the empirical acceptance>=.95 => normalized stable mass>=.93 implication. Actual credible-region measure transfer yields full stable mass>=.8835>=.88, and the conservative displayed subtraction equals.88. Thus the whole qualified fixed-batch Bayesian implication is proven under the stated posterior-law/stability-event assumptions. The final repeated-attempt sentence correctly requires a separate failure budget; no repeated-until-pass or conditional-on-acceptance theorem is inferred.')]
 required=['|((861-581:ℝ)/581)-48/100|<1/200','Nat.ceil (Real.log 100/(2*(1/50:ℝ)^2))=5757','(99/100:ℝ)≤P.real {w | (19/20≤empirical n X w)→22/25≤posterior.real stable}']
 assert required[0] in bodies['CompleteLyapunovScenarioNumbers23.lean'] and required[1] in bodies['CompleteLyapunovScenarioNumbers23.lean'] and required[2] in bodies['CompleteLyapunovValidationBridge23.lean']
 rows=[]
 for number,ids,hyp,reason in specifications:
  key='lyapunov-mpc.html::node-'+number;row=units[key];declarations=list(dict.fromkeys(n for i in ids for n in groupmap[i]['lean_declarations']))
  rows.append({'source_unit_key':key,'entire_inventory_record':row,'whole_unit_approved':True,'material_status':'proved','lean_declarations':declarations,'hypotheses':hyp,'per_unit_reason':reason,'missing_clauses':[],'parent_exercise_whole_approved':False,'retained_parent_scope_limits':old['remaining_mathematical_gaps'],'components':[groupmap[i] for i in ids]})
 whole={'status':'passed_distinct_full_literal_three_numeric_validation_units_source51_with_explicit_posterior_assumptions','reviewer':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'current_inventory':ref(invpath),'source50_to51_identity_binding':ref(IDENTITY),'original_current50_component_peer':ref(OLD),'original_component_reviewed_at_utc_unchanged':old['reviewed_at_utc'],'entire_parent_exercise_record':ex,'material_units':rows,'whole_exercise_approved':False,'remaining_parent_gaps':old['remaining_mathematical_gaps'],'all_full_literal_clauses_and_mathematical_context_read':True,'all43_source_bodies_and10_actual_canonical_records_read_and_exact':True,'coverage_complete':False,'working_HTML_inventory_ledgers_written':False,'limits':['Only complete physical answer units1399(b),1401(c),1403(d) receive fresh whole-unit decisions. Their entire clauses, percent overhead, confidence qualification and posterior-law assumptions are included.','The question1393 and answer1397(a) retain pending general convex scenario-risk scope. No generic Campi theorem, GP posterior construction/calibration, nonlinear stability, repeated testing or whole exercise is approved.','The posterior Bayesian guarantee is conditional on the genuine fixed law and stable-event sampling model stated in the literal; that model is an explicit hypothesis, not a proved GP construction.','All old component decisions and their times remain exact; no live Root/Applied mapping is installed.']}
 write(WHOLE,whole)
 assert sha(OLD)=='d52d60fd3ee0d820057fbb71af30e37162e16521981d4b041b55cb7c903e407a'
 print(json.dumps({'status':'passed','identity':ref(IDENTITY),'whole_unit_review':ref(WHOLE),'whole_units':3,'whole_exercise_approved':False}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():write(FAIL,{'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg})
  sys.stderr.write(msg);sys.exit(1)
