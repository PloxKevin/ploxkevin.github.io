"""Read-only independent review of the aligned finite-prefix mean supplement."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re

ROOT=Path('/home/oxrexkevin/SafetyBased')
SOURCE=Path('/tmp/root-monitoring-dual-trajectory23-trial9.lean')
OUT=Path('/tmp/monitoring-mean-prefix23-independent-foundations-review-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
pins={
 str(SOURCE):'187c9475a1d2100af8f5f399065b2d5626d7db87afe765d7d76af985ea4f2d71',
 '/tmp/root-monitoring-dual-trajectory23-trial9.json':'14d29e28ffba8f57fdffe28530af15f20b9ef6d54ac085b89bcb25a0da37ddf6',
 '/tmp/root-monitoring-dual-trajectory23-trial9.log':'f2d967b89e7a65674a88a23cc82e38283ae4d3f41ffeaa918302b15f81d799ed',
 '/tmp/root-monitoring-dual-trajectory23-trial9-run.py':'f7636ccf2de72ea64d5a39e3bfcef89c7b67420b871bae788d2a938bd53345f0',
 '/tmp/root-monitoring-dual-trajectory23-trial8.lean':'5bda63b3a3c585ba3180a4c6f65fc5a146a629e85f1404337a1c3ab18b922957',
 '/tmp/monitoring-dual-trajectory23-independent-applied-components-review-v1.json':'bd5dc5db2c197c5484231381b8de4f64c8227546b5076af5fa8c7015edece4bd',
 '/tmp/monitoring-modes-source49-proposal23-independent-foundations-semantic-review-v2.json':'38e56a11f8f11ce21f5c8f2a788eacf95ebca63b33e90fd0e5c00ee754a25fcd',
 '/tmp/applied-monitoring-modes-source49-qualification-proposal23-v2.json':'125ae48247af82a507ff66309aa51291936efeef72c4f24af4add5461d10f85e',
}
assert not OUT.exists()
for name,digest in pins.items():assert sha(name)==digest
source=SOURCE.read_text()
old_source=Path('/tmp/root-monitoring-dual-trajectory23-trial8.lean').read_text()
marker='\n\ndef average (u : ℕ → ℝ) (N : ℕ) : ℝ :='
assert source.count(marker)==1
prefix=source.split(marker)[0]
end='\nend SafeLearning.CompleteMonitoringDualTrajectory23\n'
assert old_source.endswith(end)
assert prefix.rstrip()==old_source[:-len(end)].rstrip()
old_names=re.findall(r'^theorem (\w+)',old_source,re.M)
names=re.findall(r'^theorem (\w+)',source,re.M)
assert len(old_names)==28 and names[:-1]==old_names and len(names)==29
assert names[-1]=='actual_any_fixed_finite_prefix_change_preserves_time_average_limits'
assert re.findall(r'^private theorem (\w+)',source,re.M)==['finite_prefix_average_transfer']
supplement=source[len(prefix):]
assert 'sorry' not in supplement and 'axiom' not in supplement
record_path=SOURCE.with_suffix('.json')
log_path=SOURCE.with_suffix('.log')
runner_path=Path('/tmp/root-monitoring-dual-trajectory23-trial9-run.py')
record=read(record_path)
assert record['command']==['lake','env','lean',str(SOURCE)]
assert type(record['exit_code']) is int and record['exit_code']==0
assert record['source_sha256']==sha(SOURCE) and record['log_sha256']==sha(log_path)
assert 'source_sha256_before' not in record
assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in runner_path.read_text()
assert log_path.read_text().count('warning:')==5
old_peer=read('/tmp/monitoring-dual-trajectory23-independent-applied-components-review-v1.json')
assert old_peer['errors']==[] and 'passed' in old_peer['status']
assert old_peer['proof_source']['sha256']==pins['/tmp/root-monitoring-dual-trajectory23-trial8.lean']
original_time=old_peer['reviewed_at_utc']
manifest=read(ROOT/'reports/full-coverage/checkpoint-21-manifest.json')
bindings=read(ROOT/'book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json')
protected={**bindings['exact_current48_safelearning_assets_sha256'],**bindings['new_immutable_proof_sources_sha256'],**{p:r['sha256'] for p,r in manifest['proof_files'].items()}}
for name,digest in protected.items():assert sha(ROOT/name)==digest
assert sha(ROOT/'book/coverage/inventory.json')==sha(ROOT/'book/coverage/inventory-after-correction48.json')=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
report={
 'status':'passed_independent_aligned_finite_prefix_mean_supplement_review_future23',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'errors':[],'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),
 'proof_source':{'file':str(SOURCE),'sha256':sha(SOURCE)},
 'new_public_declaration':'SafeLearning.CompleteMonitoringDualTrajectory23.actual_any_fixed_finite_prefix_change_preserves_time_average_limits',
 'new_private_transfer':'SafeLearning.CompleteMonitoringDualTrajectory23.finite_prefix_average_transfer',
 'new_definition':'SafeLearning.CompleteMonitoringDualTrajectory23.average',
 'complete_new_definition_and_both_bodies':supplement,
 'complete_new_definition_and_both_bodies_sha256':hashlib.sha256(supplement.encode()).hexdigest(),
 'per_component_decision':{
  'review_status':'approved_complete_mathematical_component',
  'hypotheses':['u,v are real sequences; K is one fixed natural number; u n=v n for every n>=K; L is a real proposed mean limit.'],
  'reason':'For every horizon N>=K, splitting both finite sums at K cancels the equal aligned tail. Their sum difference is the fixed real constant C from the firstK values, so the mean difference is C/N. The inverse-natural limit yields C/N→0. Adding this vanishing difference transfers any finite real mean limit; swapping u and v gives the displayed equivalence. No boundedness of the infinite sequences is needed because the finite prefix contributes a fixed finite real C. N=0 is irrelevant to the eventual argument; the real division convention introduces no asymptotic gap.',
  'missing_clauses':[],
  'scope':'Aligned eventual equality only. This does not prove a shifted-tail theorem, admissibility of arbitrary modified physical paths, preservation of projected prices, or general feedback convergence.'
 },
 'exact_old28_public_bodies_preserved':True,
 'preserved_original_component_review':{'file':'/tmp/monitoring-dual-trajectory23-independent-applied-components-review-v1.json','sha256':pins['/tmp/monitoring-dual-trajectory23-independent-applied-components-review-v1.json'],'original_reviewed_at_utc':original_time,'original_body':old_peer},
 'actual_original_standalone_evidence':{'record':str(record_path),'record_sha256':sha(record_path),'body':record,'raw_log':str(log_path),'raw_log_sha256':sha(log_path),'actual_exit_code':0,'actual_workdir_from_runner':'/home/oxrexkevin/SafetyBased/verification/lean','runner':str(runner_path),'runner_sha256':sha(runner_path),'raw_log_description':'Nonempty; four unused-simp warnings and one unnecessarySeqFocus warning are retained.','source_identity_scope':'Genuine original execution records its post-run source hash. No unavailable before-run hash is inferred.'},
 'all_exact_reference_bytes_sha256':pins,
 'all31_current48_assets_and1089_old_plus24_reviewed22_proof_sources_checked_exact':True,
 'TMP_only_review_no_canonical_source_inventory_or_HTML_writes':True,
 'named_or_aggregate_execution_claimed':False,'selected_in_checkpoint22':False,
 'whole_source49_exercise_or_formal_coverage_approved':False,
 'source49_proposal_v2_semantic_decision_unchanged':True
}
for name,digest in pins.items():assert sha(name)==digest
for name,digest in protected.items():assert sha(ROOT/name)==digest
with OUT.open('x') as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'review':str(OUT),'sha256':sha(OUT),'new_public_theorem_count':1,'preserved_public_theorem_count':28,'scope':'aligned eventual equality of real sequences only'}))
