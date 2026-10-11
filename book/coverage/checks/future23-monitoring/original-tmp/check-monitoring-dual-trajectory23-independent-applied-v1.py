from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=Path('/tmp/root-monitoring-dual-trajectory23-trial8.lean');r=p.with_suffix('.json');l=p.with_suffix('.log');runner=Path('/tmp/root-monitoring-dual-trajectory23-trial8-run.py')
assert sha(p)=='5bda63b3a3c585ba3180a4c6f65fc5a146a629e85f1404337a1c3ab18b922957'
record=json.loads(r.read_text());assert record['command']==['lake','env','lean',str(p)] and type(record['exit_code']) is int and record['exit_code']==0
assert record['source_sha256']==sha(p) and record['log_sha256']==sha(l)
assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in runner.read_text()
assert l.read_text().count('warning:')==5
oldsource=Path('/tmp/root-monitoring-deterministic-path23-trial6.lean');oldpeer=Path('/tmp/monitoring-deterministic-path23-independent-applied-components-review-v1.json')
assert sha(oldsource)=='c85bafe8e12f10392efee43cbfcb00983b91155ca2cba9819065eacef5e54814' and sha(oldpeer)=='e7a00164cc0a409f1d65d71764c570a7d50d1862613ed33bf4662a7b9ed3a532'
split='\nnamespace SafeLearning.CompleteMonitoringDualTrajectory23\n'
assert p.read_text().count(split)==1
prefix=p.read_text().split(split)[0].replace('import SafeLearning.CompleteMonitoringDeficit22\n','',1)
assert prefix.rstrip()==oldsource.read_text().rstrip()
old=json.loads(oldpeer.read_text());names=re.findall(r'^theorem (\w+)',p.read_text(),re.M);assert len(names)==28
new=['SafeLearning.CompleteMonitoringDualTrajectory23.'+x for x in names[9:]];assert len(new)==19
groupspec=[
 ('actual_projected_augmented_rollout_and_periodicity',new[:5],[], 'The actual Bool selector and Nat scaled-price update define every AugmentedState iterate from (R0,0,0). Direct finite computations establish the first five steps and all six cycle transitions, then induction proves the entire tail period. Each physical transition is an actual model transition of probability one, and the two scaled prices are bounded by5 and4.'),
 ('actual_all_horizon_count_bounds_and_tail_limits',new[5:10],['The fraction error bound requires N>0.'], 'The actual finite six-cycle potential has an exact recurrence and a uniform bound. A genuine finite telescope yields the count identity for every horizon; the proved error bound10/N tends to zero and gives tail visit fraction1/3 for every region.'),
 ('actual_policy_law_and_full_expected_fraction_limits',new[10:14],[], 'The actual admitted physical rollout is realized by a constructed normalized controlled history policy. Its expected visit fractions are true Bochner expected counts divided by T. The explicit finite-prefix/tail identity derives the full, rather than only subsequential or tail, expected fractions1/3.'),
 ('actual_source_projected_deficit_updates',new[14:16],[], 'The Nat price update divided by3 is proved equal at every time to the real projectedStep with step size1, target1/3 and the actual current-region indicator. Induction identifies both real prices with the previously defined source recursive multiplier sequences starting at zero.'),
 ('actual_almost_sure_full_visit_limits',new[16:17],[], 'The constructed history law almost surely realizes the complete physical trajectory simultaneously at all times. Actual sample visit counts therefore equal the proven full deterministic fractions at every horizon; all three sample fractions tend to1/3 almost surely.'),
 ('actual_tie_qualified_selector_correspondence_on_the_rollout',new[17:],[], 'The qualified selector stays in Ri when its price exceeds1 and is at least the other price; R0 chooses the larger price with tieR1, and equality at threshold1 returns. Exhaustive finite initial/cycle cases prove its action equals the original strict selector at every reachable iterate, and its transition is the true model transition. This is an on-orbit equality, not a universal fixed-price maximizing theorem for arbitrary augmented initial states.')
]
groups=[{'component_id':name,'review_status':'approved_complete_mathematical_component','lean_declarations':ds,'hypotheses':hyp,'per_component_reason':reason,'missing_clauses':[]} for name,ds,hyp,reason in groupspec]
assert sum(len(g['lean_declarations']) for g in groups)==19
invpath=ROOT/'book/coverage/inventory-after-correction48.json';assert sha(invpath)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inv=json.loads(invpath.read_text());units={x['key']:x for x in inv['material_source_units']}
assert sha(ROOT/'SafeLearning/cmdp.html')==units['cmdp.html::node-1141']['source_sha256']
out={'status':'passed_independent_augmented_monitoring_trajectory_and_true_policy_components_review_future23','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],
 'proof_source':{'file':str(p),'sha256':sha(p)},'all28_complete_public_theorem_bodies_read':True,'new_public_theorem_count':19,
 'preserved_original_nine_component_review':{'file':str(oldpeer),'sha256':sha(oldpeer),'original_reviewed_at_utc':old['reviewed_at_utc']},'original_nine_theorem_source_bytes_unchanged_except_new_import_and_terminal_blank_lines':True,
 'actual_standalone_evidence':{'record':str(r),'record_sha256':sha(r),'raw_log':str(l),'raw_log_sha256':sha(l),'actual_exit_code':0,'command':record['command'],'actual_workdir_from_runner':'/home/oxrexkevin/SafetyBased/verification/lean','runner':str(runner),'runner_sha256':sha(runner),'started_at_utc':record['started_at_utc'],'finished_at_utc':record['finished_at_utc'],'raw_log_description':'nonempty: four unused-simp warnings and one unnecessarySeqFocus warning','source_identity_scope':'Original genuine record supplies its post-run source_sha256. Current source matches; no nonexistent before-run source hash is claimed.'},
 'inventory':{'file':str(invpath.relative_to(ROOT)),'sha256':sha(invpath)},'source_component_inventory_records':{k:units[k] for k in ['cmdp.html::node-1138','cmdp.html::node-1141']},
 'approved_new_components':groups,'actual_expected_and_almost_sure_fraction_limits':[1/3,1/3,1/3],
 'important_exact_scope':['The admitted schedule gives a genuine nonanticipative time-dependent controlled history law for this proven zero-initial trajectory; no theorem for every augmented initial state or every implementation of a stochastic selector is inferred.','Qualified selector equality is established along the entire actual orbit. It does not prove a globally correct fixed-price optimizer statement simply because the definition name contains Maximizing.','The explicit per-step step-size1 deterministic realization needs no unbiasedness assumption. It neither proves the primary paper\u2019s conditional unbiased epoch assumption A3 nor asserts the stochastic Theorem1 for a general controller.','Every current22 review body/time and source49 draft decision remains untouched; this is new TMP-only future23 evidence.'],
 'whole_current_source_monitoring_exercise_approved':False,'named_or_aggregate_execution_claimed':False,'not_selected_in_checkpoint22':True,
 'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(__file__)}
dest=Path('/tmp/monitoring-dual-trajectory23-independent-applied-components-review-v1.json')
with dest.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'review':str(dest),'sha256':sha(dest),'new_groups':6,'new_public_theorems':19,'preserved_public_theorems':9}))
