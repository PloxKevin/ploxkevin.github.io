from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/foundations-allocation19-full-review28-v1/foundations-allocation19-full-review28-v2.json')
OUT=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-observations28-v2.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(REQUEST)=='6b394c72daf03743881e78fc9da023fbda5d6c703c979331aa762ffb5ea77c51'
d=json.loads(REQUEST.read_bytes())
for field in ['current_inventory','current_foundations_owner','proof_source','actual_successful_trial','previous_author_packet_retained']:
 r=d[field];assert sha(Path(r['file']))==r['sha256'],field
source=Path(d['proof_source']['file']).read_text();assert source==d['entire_source']
names=re.findall(r'^theorem\s+(\w+)',source,re.M);assert len(names)==len(set(names))==d['public_theorem_count']==19
assert not re.search(r'\b(sorry|admit|axiom)\b',source)
for original,row in d['original_closed_byte_aliases'].items():assert sha(Path(original))==sha(Path(row['file']))==row['sha256'],original
for r in d['full_reused_dependency_sources']:
 p=Path(r['source']['file']);assert sha(p)==r['source']['sha256'] and p.read_text()==r['entire_source']
inventory=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());units={r['key']:r for r in inventory['material_source_units']}
keys={f'primer-optimization.html::node-{i}' for i in [1552,1553,1557,1563,1566,1570,1578,1640]}
assert {r['key'] for r in d['full_source_units']}==keys
for r in d['full_source_units']:assert r==units[r['key']]
html=(ROOT/'SafeLearning/primer-optimization.html').read_text()
assert d['full_teaching_context_lines1417_to1486']=='\n'.join(html.splitlines()[1416:1486])
owner=json.loads((ROOT/'book/coverage/foundations.json').read_bytes())
def walk(x):
 if isinstance(x,dict):
  if 'id' in x:yield x
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
old={r['id']:r for r in walk(owner)}
assert len(d['current_existing_claims_unchanged'])==17
for row in d['current_existing_claims_unchanged']:assert row==old[row['id']],row['id']
trials=[]
for row in d['actual_trials_original_bodies_and_times']:
 r=json.loads(Path(row['record']['file']).read_bytes());assert r==row['entire_original_record_and_time'] and sha(Path(row['record']['file']))==row['record']['sha256']
 assert r['protection_errors']==[] and type(r['actual_exit_code']) is int
 raw=Path(row['raw_log']['file']).read_text();assert raw==row['entire_raw_log'] and sha(Path(row['raw_log']['file']))==row['raw_log']['sha256']==r['raw_log_sha256']
 snapshot=Path(row['source_snapshot']['file']);assert snapshot.read_text()==row['entire_original_source'] and sha(snapshot)==row['source_snapshot']['sha256']==r['source_snapshot_sha256']
 assert r['source_sha256_before']==r['source_sha256_after']==r['source_snapshot_sha256']
 assert r['actual_command']==['lake','env','lean',r['source']] and r['actual_workdir']==str(ROOT/'verification/lean')
 assert r['protected_selected27_proof_sources']==1175 and r['unchanged_current55_book_assets']==31 and r['unchanged_installed27_live_owners']==5
 for field in ['pinned_installed27_provenance_sha256','installed27_owner_sha256']:
  for n,h in r[field].items():assert sha(ROOT/n)==h,n
 warnings=len(re.findall(r'^.+\.lean:\d+:\d+: warning:',raw,re.M));assert warnings==row['actual_warning_count']
 trials.append({'record':row['record'],'actual_exit_code':r['actual_exit_code'],'actual_warning_diagnostics':warnings,'original_body_and_time':r})
assert [r['actual_exit_code'] for r in trials]==[1,0] and trials[1]['actual_warning_diagnostics']==d['actual_successful_warning_count']==5
assert Path(trials[1]['original_body_and_time']['source_snapshot']).read_text()==source
namespace='SafeLearning.CompleteFoundationsAllocationClearanceWholeUnits28.'
new={namespace+n for n in names};dep_names=set()
for r in d['full_reused_dependency_sources']:
 t=r['entire_source'];namespace0=re.search(r'^namespace\s+(\S+)',t,re.M).group(1)
 dep_names.update(namespace0+'.'+n for n in re.findall(r'^(?:theorem|lemma)\s+(\w+)',t,re.M))
for r in d['complete_literal_clause_correspondences']:
 assert all(n in new for n in r['new']) and all(n in dep_names for n in r['reuse'])
reasons={
1552:'The same normalized unit error costs1/2 and2 in the two source channels. The original hard triangle and genuine finite quadratic excess-flow penalty are distinct optimization problems: the explicit infeasible23/9,8/9 point has penalized cost2/9 below every feasible source point. This proves why feasibility requires a separate check; it does not assert that every conceivable finite exact penalty fails. Stipulated design weights carry no empirical device claim.',
1553:'Actual allocationObjective equals weights1,4/request3,1; the derivative of its genuine gradient is the matrix diag1,4 and its quadratic form is strictly positive in each nonzero Fin2 direction. StrictConvexOn is proved for this full objective. The actual nonnegative supply triangle is closed, bounded, convex and nonempty; compactness and polynomial continuity give attained minimum. Book allocation_cost_identity/allocation_kkt/allocation_unique_optimum separately derive the true feasible KKT point and unique all-competitor minimum, so the concluding certification statement is justified for this exact model.',
1557:'The unconstrained zero-cost request3,1 has total4. For every nonnegative slack feasible allocation, the explicit positive t=(3-u-v)/(2(4-u-v)) produces a nonnegative move toward that request with total still below3 and strictly reduced actual cost. A minimizer therefore cannot leave the supply slack. Actual KKT positivity and sum3 at11/5,4/5 justify the attempted positive active boundary without assuming the conclusion.',
1563:'The proportional source request reduction9/4,3/4 sums to3 and costs13/32=.40625; the real optimum11/5,4/5 costs2/5=.4. The source-matched global identity applies to every feasible allocation and gives the unique lower bound, beyond comparison with one alternative. Its errors4/5 and1/5 explain protection of the second, weight4 channel in the stated model.',
1566:'For1/4<b<4 the complete existing KKT and all-competitor identity yield the printed multiplier and both positive command formulas. New all-competitor small-budget identity yields unique0,b on0<=b<=1/4, including the transition; negative budgets are infeasible. Forb>=4 the true request3,1 is feasible and is the unique zero-cost optimum, slack above4. Endpoint4 and1/4 are handled without silently extending an interior active set.',
1570:'Actual HasDerivAt clearance is-1/5-a/5 for every command, and value/derivative at0 yield the stated tangent. The full existing all-command clearance_tangent_error gives exact nonnegative remaindera^2/10. At1 the tangent meets1/10 while true clearance is0, so the warning about accepting a finite tangent boundary is an actual source witness within the stipulated endpoint model.',
1578:'Actual g=a^2/10+a/5-1/5 is proved convex by its chord gap and has genuine derivativea/5+1/5. At sqrt3-1, the theorem proves inactive0/1 bounds, exact zero constraint, positive10/sqrt3-5 multiplier, derivative-based stationarity and complementary slackness. Existing rational bounds give the printed approximate multiplier, and existing clearance_optimum proves the unique all-feasible command bound on[0,1]. It certifies this modeled endpoint optimization only.',
1640:'For everyd>=0 the actual worst disturbance-d belongs to the symmetric uncertainty interval and attains the minimum clearance over all permittedw. The universal clearance requirement is exactly the single genuine ConvexOn constraint; the Book root/global-cost proof uses the decreasing quadratic distance-to-one on the actual command interval to select the maximum feasible command. This approves the complete hint in its surrounding robust clearance exercise; it is not a promotion of the whole parent exercise.'}
decisions=[]
for r in d['full_source_units']:
 node=int(r['key'].split('-')[-1]);mapping=next(c for c in d['complete_literal_clause_correspondences'] if c['node']==node)
 decisions.append({'key':r['key'],'entire_inventory_record':r,'whole_source_unit_approved':True,'missing':[],'reason':reasons[node],'new_declarations':mapping['new'],'selected_reused_declarations':mapping['reuse'],'hypotheses':['Exactly the stipulated allocation objective/request(3,1), weights(1,4), nonnegative hard supply triangle; positive/interior budgets only where specified, outer regimes explicit.','Clearance h=.3-.2a-.1a^2+w on modeled[0,1], target>=.1, symmetric|w|<=d withd>=0; nonrobust KKT atd0 and robust optimum only within feasible0<=d<=.2.','Full-unit mathematical coverage in this model; no empirical performance, continuous-motion clearance, generic finite-penalty impossibility or parent-exercise approval.']})
body={'status':'passed_independent_full_allocation_clearance_eight_literal_semantic_review28','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Applied independent of Foundations author','request':{'file':str(REQUEST),'sha256':sha(REQUEST)},'proof_source':d['proof_source'],'public_theorem_count':19,'full_source_read':True,'full_context_read':True,'material_units':decisions,'entire_prior17_claim_rows_unchanged':d['current_existing_claims_unchanged'],'entire_native_trial_bodies_and_times':trials,'previous_author_packet_retained':d['previous_author_packet_retained'],'warning_count_qualification':d['warning_count_qualification'],'entire_original_author_packet_body_and_time':d,'current55_unchanged':True,'coverage_complete':False,'parent_exercise_approval':False,'canonical_or_aggregate_execution':False,'scope':'Fresh full mathematical source/context correspondence for eight entire physical units. All19 new theorem bodies and complete reused Book/Constrained/Spectral sources read, exact current units/claims/14 aliases rehashed; actual1 and actual0/five emitted warning diagnostics preserved. This is a read-only semantic checker, not a Lean/canonical rerun or owner promotion.'}
with OUT.open('x') as f:f.write(json.dumps(body,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':body['status'],'observations':str(OUT),'sha256':sha(OUT),'whole_units':len(decisions),'public_theorems':19,'aliases':len(d['original_closed_byte_aliases'])}))
