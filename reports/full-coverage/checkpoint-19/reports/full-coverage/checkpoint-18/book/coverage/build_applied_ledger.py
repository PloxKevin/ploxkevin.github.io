#!/usr/bin/env python3
"""Conservative source ledger for the C/D/E completion work.

Unreviewed source clauses stay pending. A theorem candidate is not coverage.
The explicit reviewed claim records below are the only promotion mechanism.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from validate import Document, clean_text
ROOT=Path(__file__).resolve().parents[2]
PAGES=['SafeLearning/primer-probability.html','SafeLearning/primer-systems.html','SafeLearning/primer-rl-nn.html']
NS={k:'SafeLearning.CompleteApplied'+k+'.' for k in ['Policy','Network','Systems','Probability','Elementary','Concentration','Dynamics','PolicyModel','ProbabilityModel']}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def declaration(group,*names): return [NS[group]+n for n in names]
def claim(id,text,group,names,*,hypotheses=(),gaps=(),status=None,correspondence=None):
 return dict(id=id,statement_in_prose=text,kind='mathematical_conclusion',lean_declarations=declaration(group,*names),status=status or ('pending' if gaps else 'proved'),hypotheses=list(hypotheses),correspondence=correspondence or 'The named declaration encodes this specific mathematical conclusion; physical model validity remains an explicit premise of the example.',remaining_gaps=list(gaps))
REVIEWED={
 'book-c-b1':[
  claim('alarm-law','The changed fault/alarm law has alarm mass 0.0882, quiet mass 0.9118, alarm posterior 5/49 and quiet posterior 5/4559.','Probability',['changed_conveyor_events'],hypotheses=['Four joint outcomes encode the stated fault rate 0.01, sensitivity 0.9 and false-alarm rate 0.08.']),
  claim('action-choice','Expected release loss is below six after either observation, so release is preferred.','Probability',['conveyor_action_optimality','inspection_decision_threshold']),
  claim('rule-comparison','Always releasing has expected loss 0.30; the old inspect-on-alarm rule has expected loss 0.5592.','Probability',['changed_rule_worse']),
 ],
 'book-c-b2':[
  claim('predictive-variance','Under the conditional Gaussian posterior, independent fresh noise increases total variance from 2/3 to 5/3.','Probability',['shared_offset_numbers'],gaps=['Derive the conditional Gaussian posterior from the joint prior/likelihood measure and prove conditional independence of the fresh noise. Arithmetic 2/3+1=5/3 alone does not establish this law.']),
  claim('predictive-tolerance','The predictive tolerance probability is 2 Phi(2/sqrt(5/3))-1 approximately 0.87866, below 0.98.','Probability',[],gaps=['Prove the predictive Gaussian law, standardization and a certified Gaussian-CDF enclosure establishing the strict requirement failure.']),
 ],
 'book-c-b3':[
  claim('average-noise','An average of n pairwise independent, square-integrable fresh noises each of variance one has variance 1/n.','Probability',['independent_average_variance'],hypotheses=['n>0; actual probability measure; MemLp 2; pairwise independent noises; each variance one.']),
  claim('shared-error','The shared offset plus the independent noise average has variance 2/3+1/n.','Probability',['shared_offset_average_variance'],hypotheses=['Conditional offset has variance 2/3; it and the noise average are square-integrable and independent.'],gaps=['Connect these explicit conditional-measure hypotheses to the calibration joint model, rather than assuming a posterior law.']),
  claim('floor-limit','The expression 2/3+1/n tends to 2/3; its value at n=100 is 203/300, distinct from (5/3)/100.','Probability',['shared_offset_limit','shared_offset_numbers']),
  claim('cross-covariance','Distinct reading errors have covariance 2/3 because both contain the same offset.','Probability',[],gaps=['Expand covariance for the actual conditional reading random variables and derive all zero cross terms from independence.']),
 ],
 'book-c-b4':[
  claim('union','For any fifty failure events of probability at most q, their union has probability at most 50q; q<=1/2500 suffices.','Probability',['finite_batch_union_bound','batch_sufficient_bound']),
  claim('independent','Under independence the exact batch failure probability is 1-(1-q)^50 and its maximum feasible q is 1-0.98^(1/50).','Probability',[],gaps=['Derive the joint event product from independence and invert the power on [0,1], including necessity of the largest admissible q.']),
  claim('original-failure','The original rate q=1/250 fails the independent requirement.','Probability',['batch_original_fails'],gaps=['Connect this exact algebra to the independent product-event probability and certify the displayed decimal 0.18160.']),
 ],
 'book-d-b1':[
  claim('first-reading','Starting at error -2, readings zero and one fail the 0.3 tolerance; reading two meets it.','Systems',['deadline_readings','geometric_trajectory'],hypotheses=['Specified sampled feedback recursion; initial error -2.']),
  claim('inputs-and-time','Two sampling intervals are ten minutes; the first two commanded inputs are admissible.','Systems',['actuator_admissible','sampled_thermal_invariant'],gaps=['Explicitly encode the clock conversion and certify the displayed second-input decimal against the rigorous q enclosure.']),
  claim('between','The full held-input trajectory remains inside the temperature-error interval before the deadline.','Systems',['intersample_thermal_invariant','heldThermal_derivative','heldThermal_initial'],gaps=['Prove that every solution of the specified scalar ODE equals this checked initial-value trajectory; derivative and initial-value checks alone provide a solution, not uniqueness.']),
 ],
 'book-d-b2':[
  claim('robust-gains','For 0<=k<=1/2, the sampled interval is robustly invariant iff (a-1/2)/b<=k.','Systems',['disturbed_gain_interval','robust_scalar_interval'],hypotheses=['Exact sampled update; disturbance absolute value at most 1/10; initial state in the proposed interval.']),
  claim('actuator','Every state with |x|<=2 has admissible command 1-kx when 0<=k<=1/2.','Systems',['actuator_admissible']),
  claim('rounded-endpoint','The gain endpoint is approximately 0.315101.','Systems',[],gaps=['Prove a rational enclosure for (a-1/2)/b tight enough to validate the displayed rounding.']),
 ],
 'book-d-b3':[
  claim('worst-state','The allowed state d=0.72,v=1.1,a=1 with delay 0.2 requires travel 0.825, exceeding clearance.','Systems',['braking_examples','stopping_distance']),
  claim('largest-delay','All allowed states meet the stopping-distance inequality when 0<=tau<=23/220; the extremal state makes this bound necessary.','Systems',['uncertain_braking_guarantee','worst_case_delay'],hypotheses=['d in [0.72,0.78]; v in [0.9,1.1]; constant braking a>=1; coasting through the delay.']),
  claim('all-time','The braking trajectory is safe at every time if its initial stopping clearance is nonnegative.','Systems',['braking_all_time_safe','brake_dynamics','brake_clearance_constant'],gaps=['Join the coasting, constant-deceleration and stopped phases, and prove equivalence for every admissible physical trajectory including the stop-and-hold boundary condition.']),
 ],
 'book-d-b4':[
  claim('saturated-map','The actual saturated sampled map preserves [-2,2] for every state in that interval.','Systems',['saturated_map_invariant']),
  claim('propagation','Repeated preservation proves sampled invariance by induction.','Systems',['saturated_map_invariant'],gaps=['Apply the old general invariant_along_iterates theorem to the exact saturated map and initial region, with an explicit declaration/correspondence.']),
  claim('first-update','At initial error -2, the unclipped and clipped first updates differ, with the displayed values about 0.211992 and -0.672805.','Systems',[],gaps=['Prove the exact clipping identity and rational enclosures for both first-update values.']),
  claim('intersample','Each held-input trajectory stays between its initial and terminal values, so full-time invariance also holds.','Systems',[],gaps=['Prove the monotonic/convex-combination property for arbitrary held deviation and use it for all three clipped branches; add scalar ODE uniqueness.']),
 ],
 'book-e-b1':[
  claim('budget','For p>=0, the quarter maintenance budget is equivalent to p<=5/19.','Policy',['quarter_budget','nominal_maintenance_semantics'],hypotheses=['Specified two-state Markov model with wear probability 1/4 and discount 4/5; p in [0,1].']),
  claim('optimum','Production increases strictly with p, so p=5/19 is the best feasible parameter in this policy family.','Policy',['J_strictMono','tightened_optimal','nominal_production_semantics']),
  claim('value','At p=5/19 the maintenance return is 1/4 and production return is 12.','Policy',['policy_values']),
 ],
 'book-e-b2':[
  claim('uncertain-law','The expected discounted maintenance return is (4/5 rho p)/(1/5+4/25 rho p).','Policy',['maintenanceReturn_formula','readyProbability_transition','discounted_ready_sum'],hypotheses=['Stationary fresh randomized actions and fixed wear rho; initial state ready; rho*p in [0,1].']),
  claim('robust-optimum','The half budget holds for every rho in [1/5,3/10] iff p<=25/54.','Policy',['robust_budget_equivalence','wear_cost_derivative'],hypotheses=['p in [0,1].']),
  claim('half-fails','At p=1/2,rho=3/10, cost is 15/28>1/2.','Policy',['robust_half_fails']),
 ],
 'book-e-b3':[
  claim('nominal','At y0=2.8, normalized input is 0.8 and score is 0.3.','Network',['biased_nomination_values']),
  claim('combined','Noise magnitude 0.2 and bias magnitude 0.15 allow total magnitude 0.35; the score is globally 1-Lipschitz.','Network',['noise_bias_combination','score_abs_bound']),
  claim('counterexample','An allowed positive noise and bias give input 1.15 and a negative score -0.05.','Network',['allowed_actual_flip','biased_nomination_values']),
  claim('tie','In the positive direction, strict positivity holds exactly below distance 0.3; a tie occurs at y=3.1, and the closed allowed uncertainty interval cannot certify positivity.','Network',['tie_distance_exact','biased_nomination_values','closed_interval_not_strictly_positive']),
 ],
 'book-e-b4':[
  claim('balance','The stationary worn fraction uniquely solves w=(1-w)5/36, giving 5/41; the stated probabilities are stationary under the transition law.','Policy',['stationary_balance_unique','stationary_values']),
  claim('rates','The stationary per-shift repair mean is 5/41 and production mean is 112/41; twenty stationary shifts have expected repairs 100/41.','Policy',['stationary_values'],gaps=['Encode the stationary Markov initialization and the random count, and apply expectation linearity to its twenty indicators. Balance and scalar products alone do not establish this count expectation.']),
  claim('comparison','The stationary twenty-shift expectation differs from the ready-initialized infinite discounted budget 1/2.','Policy',['stationary_values','policy_values','nominal_maintenance_semantics'],gaps=['Complete the stationary count-expectation semantics in the preceding claim.']),
 ],
}

def clauses(text):
 # Split prose only outside TeX; preserve decimal points and mathematical content.
 pieces=[]; start=0; math=False; i=0
 while i<len(text):
  if text[i]=='$' and (i==0 or text[i-1]!='\\'): math=not math
  if not math and text[i] in '.;':
   decimal=text[i]=='.' and i>0 and i+1<len(text) and text[i-1].isdigit() and text[i+1].isdigit()
   if not decimal and i-start>25:
    pieces.append(text[start:i+1].strip());start=i+1
  i+=1
 if text[start:].strip(): pieces.append(text[start:].strip())
 return pieces or [text]

def pending_gap(text):
 patterns=[('Gaussian','Gaussian law, conditioning/standardization or Gaussian probability conclusion'),('indep','independence implication for the stated joint random variables/events'),('martingale','filtration, conditional expectation and martingale conclusion'),('conditional','conditional probability/expectation conclusion with its specified information'),('converg','stated convergence and its required domain/time hypotheses'),('minimum','global minimization and attainment/uniqueness conclusion'),('optimal','optimality conclusion relative to the specified admissible class'),('Lipschitz','global Lipschitz/operator bound and any asserted exactness'),('variance','distribution-level variance/covariance calculation'),('probability','probability law/event implication'),('eigen','spectral and dynamical classification conclusion'),('derivative','derivative claim with the actual function and evaluation domain'),('invarian','trajectory-level invariant-region conclusion'),('entropy','entropy/divergence definition, values and comparison'),('KL','directional divergence, support and inequality conclusion'),('confidence','statistical confidence procedure and its sampling-law guarantee'),('norm','norm/operator assertion, including supremum/attainment where claimed')]
 typ=next((v for k,v in patterns if k.lower() in text.lower()),'exact mathematical assertion and all of its stated quantifiers')
 return 'A complete checked correspondence is still needed for this '+typ+': '+text

def build():
 inv=json.loads((ROOT/'book/coverage/inventory.json').read_text())
 old=json.loads((ROOT/'reports/lean-verification/applied-coverage.json').read_text())
 old_by_label={e['label']:e for e in old['exercises']}
 docs={p:Document((ROOT/p).read_text()) for p in PAGES}
 promotions_path=ROOT/'book/coverage/applied-promotions.json'
 promotions=json.loads(promotions_path.read_text()) if promotions_path.exists() else {'exercises':{},'material':{}}
 out=[]
 for e in inv['exercises']:
  if e['source'] not in PAGES: continue
  row={k:e[k] for k in ['source','locator','label','source_sha256','source_text','text_sha256','line']}
  row['inventory_key']=e['key']
  anchor=e['anchor']
  if e['key'] in promotions['exercises']:
   promoted=promotions['exercises'][e['key']]
   assert promoted['source_text_sha256']==e['text_sha256'],e['key']
   row['claims']=promoted['claims']
   row['source_correspondence']=promoted['correspondence']
  elif anchor in REVIEWED:
   row['claims']=REVIEWED[anchor]
   row['source_correspondence']='Reviewed against complete question, hint and worked solution in the canonical source_text.'
  else:
   oe=old_by_label.get(e['label'])
   assert oe, e['label']
   row['question']=oe['current_question']
   row['worked_solution']=oe['current_worked_solution']
   row['claims']=[]
   for n,text in enumerate(clauses(oe['current_worked_solution']),1):
    row['claims'].append(dict(id=f'{oe["claim_id"]}.solution.{n}',statement_in_prose=text,kind='source_clause_pending_review',status='pending',lean_declarations=[],hypotheses=['Use the complete source question and its stated probability/dynamics/input assumptions.'],correspondence='Exact source clause is frozen; no promotion follows from an earlier numerical check or theorem-name association.',remaining_gaps=[pending_gap(text)]))
   row['previous_partial_evidence']={'lean_candidates':oe['lean_declarations'],'claim':'Historical selected propositions only; candidates are not automatically assigned to these finer clauses.'}
   if oe['claim_id']=='primer-probability-original-35':
    row['previous_partial_evidence']['rejected_mappings']=['SafeLearning.PrimersApplied.bayes_alarm_legacy proves sensitivity .95, base rate .01, false-alarm .05; original C.2 states .9, .02, .01.']
    row['claims'].append(claim('original-c2-exact-fraction','The source Bayes fraction with sensitivity .9, base rate .02 and false-alarm .01 equals 90/139.','Probability',['original_c2_bayes'],gaps=['Construct the source joint event law and derive the conditional probability; the arithmetic declaration alone does not close all multi-step C.2 claims.']))
  row['status']='complete_math' if all(c['status'] in ['proved','definition_encoded','not_a_formal_claim'] for c in row['claims']) else ('partial' if any(c['status']=='proved' or c['lean_declarations'] for c in row['claims']) else 'pending')
  out.append(row)
 material=[]
 grouped={}
 for u in inv['material_source_units']:
  if u['source'] not in PAGES: continue
  needs_surrounding_review=u.get('inventory_kind')=='surrounding_prose_needs_semantic_classification'
  # Newly inventoried surrounding prose requires its own semantic review.
  # Identical text is not enough to transfer a prior exercise correspondence.
  sig=(u['source'],u['text_sha256'],needs_surrounding_review)
  if sig in grouped:
   grouped[sig]['source_unit_keys'].append(u['key']);continue
  record=dict(id='material.'+u['key'],source=u['source'],source_unit_keys=[u['key']],source_sha256=u['source_sha256'],text_sha256=u['text_sha256'],statement_in_prose=u['source_text'],kind='source_unit_pending_claim_split',status='pending',lean_declarations=[],hypotheses=['Read surrounding section definitions and assumptions; source unit may overlap other recorded units.'],correspondence='Canonical material queue retained. This record is not a claim that the unit is one theorem or that prior manual review is a formal proof.',remaining_gaps=[pending_gap(u['source_text'])],source_clauses=clauses(u['source_text']))
  owners=[e for e in out if e['source']==u['source'] and clean_text(u['source_text']) in clean_text(e['source_text'])]
  if owners and not needs_surrounding_review:
   owner=min(owners,key=lambda e:len(e['source_text']))
   record.update(kind='exercise_claim_correspondence',exercise_inventory_key=owner['inventory_key'],claim_ids=[c['id'] for c in owner['claims']],lean_declarations=sorted({d for c in owner['claims'] for d in c['lean_declarations']}),status='proved' if owner['status']=='complete_math' else 'pending',correspondence='This exact nested question/hint/solution unit belongs to the linked exercise. Its mathematical premises and conclusions use the reviewed granular exercise records; overlap does not create another proof obligation.',remaining_gaps=[g for c in owner['claims'] for g in c['remaining_gaps']])
  if u['key'] in promotions['material']:
   promoted=promotions['material'][u['key']]
   assert promoted['source_text_sha256']==u['text_sha256'],u['key']
   record.update(promoted['claim'])
  # Explicit syllabus language is a curriculum statement, not a mathematical assertion.
  if not needs_surrounding_review and u['source_text'].startswith('A first course in linear algebra'):
   record.update(kind='pedagogical_prerequisite',status='not_a_formal_claim',hypotheses=[],correspondence='This sentence specifies prerequisite study topics; it asserts no mathematical result about them.',remaining_gaps=[])
  grouped[sig]=record;material.append(record)
 # Working files enter proof metadata only after actual source-matching success.
 verified_hashes={}
 for report_path in (ROOT/'reports/full-coverage').glob('lean-*/verification*.json'):
  report=json.loads(report_path.read_text())
  if report.get('status')=='passed' and report.get('checks') and all(c.get('exit_code')==0 for c in report['checks']):
   for rel,digest in report.get('proof_sha256',{}).items():
    verified_hashes.setdefault(rel,set()).add(digest)
 for manifest_path in (ROOT/'book/coverage/checks').rglob('*.json'):
  record=json.loads(manifest_path.read_text())
  if not isinstance(record,dict) or record.get('exit_code')!=0 or not record.get('source','').endswith('.lean'): continue
  before=record.get('sha256_before',record.get('source_sha256_before'))
  after=record.get('sha256_after',record.get('source_sha256_after'))
  if not before or before!=after or 'lean' not in record.get('command',[]): continue
  log=ROOT/record.get('log','missing-log')
  if not log.is_file() or sha(log)!=record.get('log_sha256'): continue
  verified_hashes.setdefault(record['source'],set()).add(after)
 files=[p for p in sorted((ROOT/'verification/lean/SafeLearning').glob('CompleteApplied*.lean'))
        if sha(p) in verified_hashes.get(str(p.relative_to(ROOT)),set())]
 report=dict(schema_version=1,generated_at_utc=datetime.now(timezone.utc).isoformat(),scope_pages=PAGES,source_sha256={p:sha(ROOT/p) for p in PAGES},proof_files={str(p.relative_to(ROOT)):sha(p) for p in files},status='partial_completion_work_in_progress',exercises=out,material_claims=material,corrections=[dict(id='historical-C2-Bayes-map',source='SafeLearning/primer-probability.html',inventory_key='primer-probability.html::exercise-39',defect='Earlier applied ledger mapped another detector law to original C.2.',source_fraction='(.9*.02)/(.9*.02+.01*.98)=90/139',rejected_declaration='SafeLearning.PrimersApplied.bayes_alarm_legacy',replacement_arithmetic='SafeLearning.CompleteAppliedProbability.original_c2_bayes',status='mapping_corrected; model and multi-step claims remain separately pending')],limits=['Every canonical applied exercise and material source unit is retained, including pending work.','Historical candidates and numerical scripts do not promote exact clauses to proved.','All newly proved claims require independent source-to-proposition review and final build/kernel/axiom audit by the root.','Surrounding mathematical prose without TeX still requires a fresh exhaustive semantic pass.','A pedagogical or physical-model classification must name the particular statement; no blanket exemption is applied.'])
 report['counts']={'exercises':len(out),'complete_math':sum(e['status']=='complete_math' for e in out),'partial':sum(e['status']=='partial' for e in out),'pending':sum(e['status']=='pending' for e in out),'exercise_claims':sum(len(e['claims']) for e in out),'material_claim_records':len(material),'material_source_units':sum(len(m['source_unit_keys']) for m in material)}
 (ROOT/'book/coverage/applied.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps(report['counts']))
if __name__=='__main__': build()
