from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,traceback,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
REQUEST=TMP/'lyapunov-current50-five-source43-component-review-request23-v1.json'
OUT=TMP/'lyapunov-current50-five-source43-independent-foundations-component-review23-v1.json';FAIL=TMP/'lyapunov-current50-five-source43-independent-foundations-checker-failure23-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def main():
 assert not OUT.exists() and not FAIL.exists() and sha(REQUEST)=='249b3c2a11484f9095337acff63cf4d09c556f7e590309c08041c318bc3573b8'
 q=read(REQUEST);inv=read(check(q['current_authoritative_inventory']));assert q['current_authoritative_inventory']['sha256']=='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
 assert next(r for r in inv['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')==q['entire_current_exercise']
 units={r['key']:r for r in inv['material_source_units']};keys={r['key'] for r in q['exact_current_material_units']}
 assert keys=={f'lyapunov-mpc.html::node-{n}' for n in [1393,1397,1399,1401,1403]}
 for row in q['exact_current_material_units']:assert units[row['key']]==row
 sourcepage=check(q['source_page']);assert sha(sourcepage)=='228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'
 current=read(ROOT/'book/coverage/inventory.json');current_inv_sha=sha(ROOT/'book/coverage/inventory.json')
 assert next(r for r in current['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')==q['entire_current_exercise']
 currentunits={r['key']:r for r in current['material_source_units']}
 assert all(currentunits[r['key']]==r for r in q['exact_current_material_units'])
 assert q['whole_exercise_approval_requested'] is False and q['whole_answer_a_approval_requested'] is False and len(q['proposed_precise_component_groups'])==12
 oldpeers=[];bodymap={}
 for row in q['preserved_original_component_and_binding_reviews']:
  old=read(check(row['reference']));assert old==row['entire_original_body'] and 'passed' in old['status'] and old['errors']==[];oldpeers.append(row)
  if 'full_source_proof_reviews' in old:
   for proof in old['full_source_proof_reviews']:bodymap[proof['proof_source']['sha256']]=proof['entire_source_and_all_proof_bodies']
  for field in ['full_source_and_all_nine_bodies','full_source_and_all_three_proof_bodies','full_source_and_all_six_theorem_bodies']:
   if field in old:bodymap[(old.get('source') or old.get('proof_source'))['sha256']]=old[field]
 paired=[];public=set();sourcebodies=[]
 for row in q['proof_rows']:
  source=check(row['proof_source']);original=check(row['original_tmp_source']);assert source.read_bytes()==original.read_bytes();text=source.read_text();assert text==bodymap[sha(source)]
  ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1);names=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)];assert names==row['public_declarations'] and len(names)==row['public_theorem_count'];public.update(names)
  sourcebodies.append({'reference':row['proof_source'],'entire_source_and_all_original_bodies':text})
  for index,rref in enumerate(row['actual_paired_records']):
   r=read(check(rref));assert r['actual_exit_code']==r['exit_code']==0 and r['source_unchanged'] is True
   command=['lake','env','lean',f'SafeLearning/{source.stem}.lean'] if index==0 else ['lake','build',f'SafeLearning.{source.stem}'];assert r['actual_command']==r['command']==command and r['cwd']==r['actual_workdir']==str(ROOT/'verification/lean')
   assert r['source_sha256_before']==r['source_sha256_after']==sha(source)
   snapshot=ROOT/r['source_snapshot'];assert sha(snapshot)==r['source_snapshot_sha256']==sha(source) and snapshot.read_bytes()==source.read_bytes()
   log=ROOT/r['log'];assert r['log']==r['raw_log_file'] and sha(log)==r['log_sha256']==r['raw_log_sha256'] and not re.search(r'\berror(?:\(|:)',log.read_text())
   assert sha(path(r['runner_file']))==r['runner_sha256'];paired.append({'reference':rref,'entire_original_actual_record':r,'raw_log':ref(log),'snapshot':ref(snapshot)})
 assert len(public)==q['public_export_count']==43 and len(paired)==q['genuine_canonical_execution_record_count']==10
 decisions=[];mapped=set()
 reasons=['The dimension-one expression and true independent count law match the sufficient binomial-bound calculation. General optimized convex-program risk is not derived from this arithmetic.','The exact logarithmic iff and all-natural least135 remain true; the corrected source properly marks the certified finite decimals/ratio as approximations.','Actual convex scalar support-count is derived from strict removal witnesses and an attained feasible least optimizer. It supplies this precise support-count clause while preserving the separate random optimizer risk/existence/measurability conditions.','The actual minimize-x sampled lower-bound model has its constructed unique attained sample-maximum optimizer, including the true strict-maximum support equivalence, singleton and tie cases.','The fixed threshold all-miss event has true independent common-probability factors. A fixed region is not reinterpreted as every random optimized-violation event.','In the precise continuous-CDF iid lower-bound scalar model, the optimizer and violation are constructed. Genuine PIT and whole-family independence derive the exact random optimized-risk probability, with all hypotheses explicit and no general Campi conclusion.','Actual all-horizon tail monotonicity and rational boundary enclosures prove581 is the least count for the specified ten-term expression and justify the approximate displayed endpoint values.','The exact chosen source variable-count formula specializes to10 and the supplied sufficient expression has least integer861 and the displayed relative increase. No general optimized controller scenario-risk theorem is attached to the arithmetic.','The corrected and misprinted ceilings5757/116, exact exponent-.0928 and true exponential enclosure give the stated Hoeffding lower-confidence bound. It is explicitly a bound from the inequality rather than actual procedure confidence.','For one fixed independent common-mean batch, the true population lower-mean event has probability≥.99. Empirical acceptance≥.95 implies population mean≥.93 on the same event; this is not confidence conditional on acceptance.','An actual measurable credible region of posterior mass.95 and normalized stable mass≥.93 yields full stable mass≥.8835≥.88. The arithmetic also proves the printed conservative additive bound. GP posterior construction/calibration remains an assumption.','For the actual normalized credible-posterior iid Bernoulli validation model, one fresh batch of at least5757 samples has probability≥.99 of the accepted-test implication in corrected(d). Neither repeated-until-pass nor a conditional-on-accept guarantee is inferred.']
 for group,reason in zip(q['proposed_precise_component_groups'],reasons):
  assert set(group['lean_declarations'])<=public and set(group['source_unit_keys'])<=keys; mapped.update(group['lean_declarations'])
  decisions.append({'component_id':group['component_id'],'approved_precise_component':True,'original_requested_group_unchanged':group,'independent_reason':reason,'hypotheses':group['hypotheses'],'retained_scope_limits':group['missing_clauses'],'whole_unit_or_exercise_approved':False})
 contrast=q['historical_false_decimal_contrast_declaration'];assert public-mapped=={contrast} and contrast.endswith('actual_printed_decimal_equalities_are_false')
 for r in q['canonical_readiness']:check(r)
 check(q['actual_preparer']);manifest=read(check(q['protected_selected22']['manifest']));assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 held={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/core.json','book/coverage/modules.json','book/coverage/applied.json','book/coverage/foundations.json'}}
 for n,h in held.items():assert sha(ROOT/n)==h
 assert sha(sourcepage)==q['source_page']['sha256']
 result={'status':'passed_fresh_independent_current50_corrected_scenario19_twelve_scoped_components_five_sources43_exports_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'request':ref(REQUEST),'original_request_created_at_utc':q['created_at_utc'],'authoritative_source50_inventory':q['current_authoritative_inventory'],'observed_current_global_inventory_sha256_at_review':current_inv_sha,'source_page':q['source_page'],'entire_current50_question_and_all_four_answers_read':q['entire_current_exercise'],'all_five_entire_current50_material_records_read':q['exact_current_material_units'],'component_decisions':decisions,'five_full_source_bodies_equal_original_independently_read_sources':sourcebodies,'all_ten_genuine_canonical_records_raw_logs_snapshots_runners':paired,'all_original25_9_3_6_and_canonical_binding_peer_bodies_times_exact':oldpeers,'historical_false_decimal_contrast_export':{'name':contrast,'valid_original_proof_retained':True,'used_as_corrected_current50_clause':False},'protected_all1113_selected22_sources_exact':True,'held_four_working22_ledgers_sha256_exact':held,'whole_exercise_approved':False,'whole_material_unit_promotions':[],'remaining_mathematical_gaps':q['retained_missing_clauses'],'selection_ownership':q['selection_ownership'],'coverage_complete':False,'working_HTML_inventory_or_ledgers_written':False,'limits':['Fresh current50 source-to-component decisions are distinct from all original48/49 peer bodies/times. No old decision is rewritten or retimed.','Corrected finite decimals and fixed-batch accepted-test implication are reviewed as written. Numeric/scalar optimized-risk evidence is not promoted to generic Campi–Garatti risk or GP construction.','Forty-three immutable public exports are evidenced;42 are assigned to the12 precise current groups and the valid false-old-decimal contrast remains historical.','No complete exercise/material-unit promotion, live Root or Applied mapping installation, aggregate23/selection or publication is claimed. Only new TMP independent review/helper files are written.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':ref(OUT),'precise_groups':12,'sources':5,'exports':43,'actual_records':10}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg},indent=2)+'\n')
  sys.stderr.write(msg);sys.exit(1)
