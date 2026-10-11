from pathlib import Path
import json, hashlib, re
from datetime import datetime, timezone

ROOT=Path('/home/oxrexkevin/SafetyBased')
PACKET=Path('/tmp/mpc-shift15-components-full-review28-v1/mpc-shift15-components-full-review28-v1.json')
OUTPUT=Path('/tmp/mpc-shift15-components-independent-foundations28-v1.json')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(r):
    p=Path(r['file'])
    if not p.is_absolute():p=ROOT/p
    assert p.is_file(),str(p)
    assert sha(p)==r['sha256'],str(p)
    return p
inventory_before=sha(ROOT/'book/coverage/inventory.json')
assert inventory_before=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert sha(PACKET)=='26d030989b9d48dbeb7fa251430511b7f3976943fb437f86e8fae9bd2ca5a649'
j=json.loads(PACKET.read_text())
for a in j['original_closed_byte_aliases'].values():check(a)
groups=[]
assert len(j['proof_groups'])==4
assert [g['theorem_count'] for g in j['proof_groups']]==[2,4,6,3]
assert len(j['actual_standalone_records'])==4
for g,actual in zip(j['proof_groups'],j['actual_standalone_records']):
    p=check(g['source']);body=p.read_text()
    assert body==g['entire_source_body']
    names=re.findall(r'^theorem (\w+)',body,re.M)
    assert len(names)==g['theorem_count']
    ar=check(actual['actual_record']);a=json.loads(ar.read_text())
    assert a==actual['entire_original_actual_record_and_time']
    assert type(a['actual_exit_code']) is int and a['actual_exit_code']==0
    assert type(a['actual_runner_exit_code']) is int and a['actual_runner_exit_code']==0
    assert a['protection_errors']==[] and a['source_unchanged'] is True
    assert a['actual_command']==['lake','env','lean',str(p)]
    assert a['actual_workdir']==str(ROOT/'verification/lean')
    assert a['source_sha256_before']==a['source_sha256_after']==g['source']['sha256']
    log=check(actual['raw_log']);snap=check(actual['source_snapshot'])
    assert sha(log)==a['raw_log_sha256']
    assert snap.read_bytes()==p.read_bytes()
    groups.append({'source':g['source'],'theorem_names':names,'count':len(names),'actual_record':actual['actual_record'],'actual_warning_count':log.read_text().count(' warning:')})
assert [g['actual_warning_count'] for g in groups]==[0,0,0,3]
for refkey,bodykey in [('original_full_gap_audit','entire_original_full_gap_audit_body_and_time'),('original_new_two_components_peer','entire_original_new_two_components_peer_body_and_time'),('domain_clarification_proposal','entire_domain_clarification_proposal_body_and_time'),('independent_domain_interpretation_peer','entire_independent_domain_interpretation_peer_body_and_time')]:
    assert json.loads(check(j[refkey]).read_text())==j[bodykey]
failed=j['genuine_failed_finite_constructor_trial']
fa=json.loads(check(failed['record']).read_text())
assert fa==failed['entire_original_actual_record_and_time']
assert type(fa['actual_exit_code']) is int and fa['actual_exit_code']==1
assert type(fa['actual_runner_exit_code']) is int and fa['actual_runner_exit_code']==1
assert fa['protection_errors']==[]
check(failed['raw_log']);check(failed['source_snapshot'])
check(j['initial_actual_pre_lean_launch_failure'])
assert j['whole_exercise18_approved'] is False and j['whole_material_units_approved'] is False
inventory_after=sha(ROOT/'book/coverage/inventory.json')
assert inventory_before==inventory_after
result={
  'status':'passed_independent_full15_body_scoped_component_semantic_review',
  'errors':[],'reviewer':'/root/foundations_recovery28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
  'packet':{'file':str(PACKET),'sha256':sha(PACKET)},
  'full_all15_public_theorem_bodies_and_private_definitions_structures_read':True,
  'full_current_and_proposed_assumption_and_theorem_context_read':True,
  'full_preserved_primary_domain_and_original_gap_review_context_read':True,
  'all_original_actual_records_logs_failed_trial_and_prior_report_bodies_times_verified':True,
  'actual_source_groups':groups,
  'group_semantic_decisions':[
    {'group':'1','component_approved':True,'scope':'A genuinely distinct normed pair with two quadratic inequalities forces cL≤cU. Under positive cL and that order, sqrt(cU/cL)≥1; multiplying nonnegative row bounds by lambda eta proves the exact first state-row epsilon margin. No constant order is obtained without the distinct pair or another justified geometric argument.'},
    {'group':'2','component_approved':True,'scope':'Actual unit-right-hand-side finite matrix rows contain the explicit positive ball1/(||H||+1), including zero rows. In a nontrivial real normed vector space, continuity at0, V0=0 and a positive local budget yield an actual nonzero local point and hence constant order. The actual erosion relation yields nominal and disturbed input admissibility. The scalar row increment derives the earlier row constraint from the later old row and error bound.', 'qualifications':['The Nontrivial assumption excludes zero-dimensional state space; the full theorem must handle that case separately.','The geometry certificate fixes z=0 and a valid fixed reference input when instantiating the primary V(x,z,v). These domain choices remain explicit full-source interfaces.','Generic normed input erosion must be instantiated with the original infinity norm; no Euclidean/infinity equality is implicit.']},
    {'group':'3','component_approved':True,'scope':'The one-step certificate couples original successor-domain membership and contraction under the explicitly adopted partial-domain interpretation. The induction derives all-stage original domains before invoking the local lower bound. Geometric values plus a positive lower constant and nonnegative scalar radius derive the actual tracking radius. Bounded linear row actions and source tightening increments derive new state and feedback input constraints. Terminal invariance absorbs the actual additive terminal offset. The final theorem constructs a genuine finite prediction from this recursion and the separately stated old-reference/radius-budget interfaces.', 'qualifications':['TypedLocalIncrementalCertificate is a conditional local component of Assumption1, not a full encoding of its continuity, diagonal-zero, upper and positivity clauses.','Old reference states, reference inputs, dynamics, later-tightened rows and the terminal nominal successor are assumptions concerning the old plan. They must be built from the original finite feasible plan and terminal ingredients for a whole recursive-feasibility result.','Scalar radius budgets and state/input increment premises must be instantiated from q=sqrt(rho), B=cU*(lambda*eta)^2 and the exact epsilon formula. No complete scalar instantiation is claimed here.','Terminal invariance is assumed with radius N; the original fixed terminal perturbation set must be shown to include this actual terminal offset.','Current55 has not adopted the explicit x+∈X clarification. This is approval of an expressly adopted partial-domain reading, not a theorem in the weaker total-ambient V model or a uniquely printed author-intent claim.']},
    {'group':'4','component_approved':True,'scope':'The actual old nominal prediction extends by one terminal-control step; that dynamics identity is proved through the horizon. The shifted candidate follows the true f/kappa recursion with old reference index j+1. Initial state and recurrence are genuine definitional identities; induction proves uniqueness of any candidate satisfying the same recurrence.', 'qualifications':['The three exports establish dynamics and construction only; terminal/state/input membership of the new plan is not inferred.','A bridge identifying this indexed recursion with generatedTrackingState at nominal/reference shifted indices is needed in the full construction.']}
  ],
  'desired_shifted_feasibility_or_whole_conclusion_not_assumed_as_a_premise':True,
  'local_certificate_and_old_reference_interfaces_explicit_not_whole_source_approval':True,
  'original_finite_failed_trial_retained_actual1':True,
  'original_prelean_inventory_guard_event_retained':True,
  'current_inventory_before_sha256':inventory_before,'current_inventory_after_sha256':inventory_after,
  'source_unit_or_exercise_whole_approval':False,
  'remaining_whole_source_obligations':j['remaining_whole_source_obligations'],
  'canonical_named_or_aggregate_execution_claimed':False,
  'scope':'Independent mathematical component review and exact native evidence verification only. No compiler invocation, production writer, parser import, canonical source/owner/proof mutation or coverage promotion.'
}
assert not OUTPUT.exists()
OUTPUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':{'file':str(OUTPUT),'sha256':sha(OUTPUT)},'actual_exit_code':0,'public_components':15,'whole_unit_approval':False}))
