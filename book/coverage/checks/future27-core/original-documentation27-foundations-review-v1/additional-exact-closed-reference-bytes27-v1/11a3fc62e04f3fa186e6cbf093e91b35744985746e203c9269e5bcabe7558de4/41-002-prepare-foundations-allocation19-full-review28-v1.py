from pathlib import Path
import json,hashlib,re,shutil
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/foundations-allocation19-full-review28-v1');OUT.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):
    p=Path(p)
    if not p.is_absolute():p=ROOT/p
    return {'file':str(p),'sha256':sha(p)}
inv=json.loads((ROOT/'book/coverage/inventory.json').read_text())
found=json.loads((ROOT/'book/coverage/foundations.json').read_text())
assert sha(ROOT/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
source=Path('/tmp/CompleteFoundationsAllocationClearanceWholeUnits28-draft-v3.lean')
assert sha(source)=='19b753ce73b59a50c72a3b6b1cc1af8aefacb763f7237358f8be9d56c6e90af3'
names=re.findall(r'^theorem (\w+)',source.read_text(),re.M);assert len(names)==19
ns='SafeLearning.CompleteFoundationsAllocationClearanceWholeUnits28.'
def decls(indices):return [ns+names[i] for i in indices]
Book='SafeLearning.CompleteFoundationsBook.'
Constrained='SafeLearning.CompleteFoundationsConstrainedModels.'
mapping=[
  {'node':1552,'new':decls([5,6]),'reuse':[Book+'allocation_unique_optimum'],
   'all_literal_clauses':['The actual normalized allocation objective assigns cost1/2 to one unit of first-channel error and2 to the same second-channel error; the ratio is exactly4. These are stipulated decision weights, not a law about devices.','Original feasibility remains u≥0,v≥0,u+v≤3. For an actual finite excess-flow penalty with coefficient1/2, point(23/9,8/9) violates the supply yet has penalized cost2/9, strictly below the cost of every original feasible allocation. Thus a penalty changes the problem; feasibility cannot be inferred from its preference objective. No universal assertion that every possible finite exact penalty fails is made.']},
  {'node':1553,'new':decls([0,1,2,3,4]),'reuse':[Book+'allocation_cost_identity',Book+'allocation_kkt',Book+'allocation_unique_optimum'],
   'all_literal_clauses':['The actual allocation objective on EuclideanSpace R(Fin2) equals the source weightedDistance with weights(1,4) and request(3,1). The Frechet derivative of its gradient is the actual matrix operator diag(1,4); its actual quadratic form is strictly positive in each nonzero direction. The full objective is StrictConvexOn R univ.','The actual feasible nonnegative triangle with sum≤3 is proved closed, bounded, nonempty and convex. Boundedness is derived from individual coordinates between0 and3, not assumed. Heine–Borel gives compactness, true polynomial continuity and compact extreme-value theorem give a minimum.','Existing source-matched Book proofs separately check the actual interior KKT point and give a sum-of-squares-plus-nonnegative-slack global identity and unique all-competitor optimum. In particular, uniqueness is not an oracle or a premise about the new answer.']},
  {'node':1557,'new':decls([7]),'reuse':[Constrained+'actual_weighted_distance_unconstrained_minimum',Book+'allocation_kkt',Book+'allocation_unique_optimum'],
   'all_literal_clauses':['The actual unconstrained zero-cost point is(3,1), which has total4 and is infeasible.','For every nonnegative slack feasible pair u+v<3, choose t=(3-u-v)/(2(4-u-v)). The theorem proves0<t<1; the actual convex move((1-t)u+3t,(1-t)v+t) keeps both commands nonnegative and total strictly below3 while decreasing the actual allocation cost. Therefore a global constrained minimum cannot have slack supply. This is an actual feasible movement argument, not an assumption that the active constraint binds.','The existing KKT point has sum3 and both coordinates positive, justifying the source active-boundary candidate.']},
  {'node':1563,'new':decls([8]),'reuse':[Book+'allocation_cost_identity',Book+'allocation_kkt',Book+'allocation_unique_optimum'],
   'all_literal_clauses':['The actual optimum(11/5,4/5) has cost2/5=.4. Proportional scaling of requests(3,1) by3/4 gives(9/4,3/4), sum3, cost13/32=.40625, strictly larger.','The preferred second channel has less normalized error(.2 instead of.8) according to the stipulated weight4. The all-competitor bound cost≥.4 follows from the existing genuine KKT identity, not just a comparison with the proportional point.']},
  {'node':1566,'new':decls([9,10,11]),'reuse':[Book+'allocation_kkt',Book+'allocation_unique_optimum'],
   'all_literal_clauses':['For1/4<b<4, the original interior formulas lambda=4(4-b)/5, u=(4b-1)/5, v=(b+1)/5 have both commands positive and sumb, and give the genuine unique optimum. These are exactly.8(4-b), .8b-.2, .2b+.2.','The new all-competitor identity proves unique optimum(0,b) for0≤b≤1/4: one nonnegativity constraint is active. It treats the endpoint1/4 explicitly. Negative budgets admit no nonnegative allocation.','For b≥4, the original request point(3,1) is feasible and is the unique zero-cost optimum; the budget is slack for b>4 and binds at the endpoint4 with zero shared multiplier. No interior formula is extended across the active-set changes.']},
  {'node':1570,'new':decls([12,16]),'reuse':[Book+'clearance_tangent_error'],
   'all_literal_clauses':['The derivative of the actual polynomial clearance at every real command is-1/5-a/5. At0 its value is3/10 and genuine derivative-1/5, so the stated affine tangent is exactly.3-.2a.','The exact previously proved all-a remainder is a squared/10, so the tangent overestimates true clearance. At1 the tangent equals.1 but true clearance is0, a concrete source-matched unsafe finite-step witness. The local slope and finite-model conclusion are kept distinct.']},
  {'node':1578,'new':decls([13,14,15,18]),'reuse':[Book+'clearance_optimum',Book+'clearance_kkt',Book+'nonrobust_clearance_decimal_bounds'],
   'all_literal_clauses':['clearanceConstraint0 is the actual g=a squared/10+a/5-1/5. ConvexOn R univ is proved by its actual chord gap aweight*bweight*(x-y) squared/10; no convexity premise supplies the conclusion. Its true derivative is a/5+1/5.','The actual a*=sqrt3-1 lies strictly between0 and1, the original multiplier10/sqrt3-5 is positive, actual g(a*)=0, stationarity uses deriv(g)(a*) and complementary slackness is checked explicitly. Existing rational enclosures bracket the printed.773503.','The existing genuine all-feasible command theorem proves the same unique global minimum, under exactly the modeled [0,1] domain and disturbance0. The decision remains conditional on this endpoint model.']},
  {'node':1640,'new':decls([14,15,17]),'reuse':[Book+'robust_clearance_exact',Book+'clearance_optimum'],
   'all_literal_clauses':['For every nonnegative error bound d, disturbance-d is feasible and produces clearance no larger than any other w with|w|≤d. Thus the minimum over that actual uncertainty interval is attained at its lower endpoint.','The original universal modeled requirement is equivalent to the single actual clearanceConstraint d a≤0. This function is proved ConvexOn R univ for every d.','The source objective is(a-1) squared/2 and decreases on[0,1]; the existing actual all-feasible root optimum proves its selection under the exact robust constraint. The hint uses genuine source error/command domains, not a different constraint fixture.']}
]
keys=['primer-optimization.html::node-'+str(v['node']) for v in mapping]
units=[u for u in inv['material_source_units'] if u['key'] in keys];assert len(units)==8
records=[];files=[source,Path('/tmp/CompleteFoundationsAllocationClearanceWholeUnits28-draft-v1.lean'),Path('/tmp/CompleteFoundationsAllocationClearanceWholeUnits28-draft-v2.lean'),ROOT/'SafeLearning/primer-optimization.html']
for n in [1,2]:
    p=Path('/tmp/foundations-allocation-clearance-whole8-28-trial'+str(n)+'.json');a=json.loads(p.read_text())
    assert type(a['actual_exit_code']) is int and a['actual_exit_code']==(1 if n==1 else 0)
    assert a['actual_runner_exit_code']==a['actual_exit_code'] and a['protection_errors']==[] and a['source_unchanged'] is True
    assert sha(Path(a['raw_log']))==a['raw_log_sha256']
    assert sha(Path(a['source_snapshot']))==a['source_snapshot_sha256']
    log=Path(a['raw_log']).read_text()
    records.append({'record':ref(p),'entire_original_record_and_time':a,'raw_log':ref(Path(a['raw_log'])),'entire_raw_log':log,'source_snapshot':ref(Path(a['source_snapshot'])),'entire_original_source':Path(a['source_snapshot']).read_text(),'actual_warning_count':log.count(' warning:')})
    files += [p,Path(a['raw_log']),Path(a['source_snapshot']),Path(a['original_actual_runner']['file'])]
dependencies=[ROOT/'verification/lean/SafeLearning/CompleteFoundationsBook.lean',ROOT/'verification/lean/SafeLearning/CompleteFoundationsConstrainedModels.lean',ROOT/'verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean']
files+=dependencies
aliases={}
for p in dict.fromkeys(files):
    h=sha(p);target=OUT/'original-closed-bytes'/h/p.name;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==p.read_bytes()
    else:shutil.copyfile(p,target)
    aliases[str(p)]={'file':str(target),'sha256':h}
context=(ROOT/'SafeLearning/primer-optimization.html').read_text().splitlines()
packet={'status':'prepared_tmp_actual19_body_eight_full_literal_source_semantic_review_request','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/foundations_recovery28','current_inventory':ref(ROOT/'book/coverage/inventory.json'),'current_foundations_owner':ref(ROOT/'book/coverage/foundations.json'),'proof_source':ref(source),'entire_source':source.read_text(),'public_theorem_count':19,'full_source_units':units,'full_teaching_context_lines1417_to1486':'\n'.join(context[1416:1486]),'current_existing_claims_unchanged':[c for c in found['material_claims'] if any(k in keys for k in c['source_unit_keys'])],'complete_literal_clause_correspondences':mapping,'actual_trials_original_bodies_and_times':records,'full_reused_dependency_sources':[{'source':ref(p),'entire_source':p.read_text()} for p in dependencies],'original_closed_byte_aliases':aliases,'actual_successful_trial':records[1]['record'],'actual_successful_warning_count':records[1]['actual_warning_count'],'actual_first_failed_trial_preserved':True,'independent_whole_unit_approval':False,'canonical_installation_or_aggregate_verification_claimed':False,'review_request':'Read every full19 proof body and definition, all8 complete literal source units and teaching/exercise context, reused source-matched dependency proofs, old1 genuine failure/2 genuine0 native raw/source snapshots/body/times. Decide all-clause full-unit correspondence independently; no intended conclusion as premise and no smaller component promoted to the whole parent. In particular verify actual finite penalty rather than another scalar model, active-constraint feasible movement, compact triangle, all active regimes, actual clearance derivatives and ConvexOn before any unit approval.','scope':'TMP-only complete source proof and full-literal semantic request; no canonical proof/owner/source changes or count/promotions.'}
p=OUT/'foundations-allocation19-full-review28-v1.json';assert not p.exists();p.write_text(json.dumps(packet,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'packet':ref(p),'public_theorems':19,'full_literal_units':8,'byte_aliases':len(aliases),'actual_warning_count':packet['actual_successful_warning_count']}))
