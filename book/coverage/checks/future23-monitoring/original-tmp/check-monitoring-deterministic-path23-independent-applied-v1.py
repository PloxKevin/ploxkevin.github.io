from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=Path('/tmp/root-monitoring-deterministic-path23-trial6.lean')
record=source.with_suffix('.json');log=source.with_suffix('.log');runner=Path('/tmp/root-monitoring-deterministic-path23-trial6-run.py')
assert sha(source)=='c85bafe8e12f10392efee43cbfcb00983b91155ca2cba9819065eacef5e54814'
assert sha(record)=='c0f44d2561f133c7eae6b7a233e63584d61ba5a57754e979af6ae944b79248ac'
assert sha(log)=='a28fa5aa308403d993a0f0b2fb6bf8e399d456d5d6bc5fd0fd95d518cd01c5d6'
assert sha(runner)=='95c2c992938b731495f0030b4d8f03db906d8af61c0ceace152ff3181ebeb894'
r=json.loads(record.read_text());assert type(r['exit_code']) is int and r['exit_code']==0
assert r['source_sha256']==sha(source) and r['log_sha256']==sha(log)
assert r['command']==['lake','env','lean',str(source)]
assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in runner.read_text()
assert log.read_text().count('warning:')==4
decls=['SafeLearning.CompleteMonitoringDeterministicPath23.'+x for x in re.findall(r'^theorem (\w+)',source.read_text(),re.M)]
assert len(decls)==9
inventory=ROOT/'book/coverage/inventory-after-correction48.json'
assert sha(inventory)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inv=json.loads(inventory.read_text());units={x['key']:x for x in inv['material_source_units']}
keys=['cmdp.html::node-1138','cmdp.html::node-1139','cmdp.html::node-1141']
assert sha(ROOT/'SafeLearning/cmdp.html')==units[keys[0]]['source_sha256']
for key in keys:
 u=units[key];assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
manifest=ROOT/'reports/full-coverage/checkpoint-21-manifest.json';m=json.loads(manifest.read_text())
sources=m.get('proof_files_sha256',m.get('proof_source_sha256',m.get('proof_files',{})))
if not isinstance(sources,dict):sources=m['source_sha256']
print('manifest keys',list(m))
# Imported canonical monitoring and finite controlled-path declarations were
# independently read in the preserved22 component reviews; this peer adds a
# separate actual23 source and does not rebrand their original executions.
dependencies={str(p.relative_to(ROOT)):sha(p) for p in [ROOT/'verification/lean/SafeLearning/CompleteMonitoringAchievable22.lean',ROOT/'verification/lean/SafeLearning/CompleteModulesMonitoringBlockLimitsClosed22.lean']}
group_specs=[
 ('actual_controlled_path_law',decls[:3],['x is a path in Fin3 beginning at R0','each consecutive transition has an actual Bool action of probability one'], 'The chosen actions define a normalized time-dependent Markov policy. Actual finite joint-mass and marginal identities derive Dirac state marginals; measurable finite partitions and countable AE intersection give a genuine controlled history law realizing the complete path almost surely.'),
 ('growing_blocks_actual_policy_realization',decls[3:6],[], 'The actual admitted source growing-block path is used to construct a nonanticipative history policy. Every horizon expected visit fraction equals its actual deterministic count fraction through the Bochner integral/state-average bridge, and the real policy expected limits are (0,1/2,1/2). The same path holds at every time almost surely.'),
 ('finite_prefix_does_not_force_initial_maximizer_action',decls[6:],[], 'The actual admitted path R0,R2,R0,R1,R1,... has a genuine time-dependent controlled policy law. Cesaro limits are vertex1 while its first region is R2 with probability one; vertex1 maximizes the long-run Lagrangian at prices (2,0). This is an arbitrary history/time-dependent maximizer counterexample, not a statement about every stationary maximizer.')
]
groups=[{'component_id':name,'review_status':'approved_complete_mathematical_component','lean_declarations':ds,'hypotheses':hs,'per_component_reason':reason,'missing_clauses':[]} for name,ds,hs,reason in group_specs]
out={'status':'passed_independent_actual_controlled_path_components_review_future23','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],
 'inventory':{'file':str(inventory.relative_to(ROOT)),'sha256':sha(inventory)},
 'proof_source':{'file':str(source),'sha256':sha(source)},
 'actual_standalone_evidence':{'record':str(record),'record_sha256':sha(record),'raw_log':str(log),'raw_log_sha256':sha(log),'actual_exit_code':0,'command':r['command'],'actual_workdir_from_runner':'/home/oxrexkevin/SafetyBased/verification/lean','runner':str(runner),'runner_sha256':sha(runner),'started_at_utc':r['started_at_utc'],'finished_at_utc':r['finished_at_utc'],'raw_log_description':'nonempty: four genuine unused-simp linter warnings','source_identity_scope':'The genuine original record supplies source_sha256 after compilation. Current immutable source bytes match it; no nonexistent pre-run hash field is claimed.'},
 'imported_canonical_source_sha256':dependencies,
 'all_nine_complete_theorem_bodies_read':True,'approved_components':groups,
 'material_units':[{'source_unit_key':k,'entire_inventory_record':units[k],'whole_unit_approved':False,'material_status':'pending_source_claim_correspondence','review_status':'approved_precise_components_only','lean_declarations':decls[3:6] if k.endswith('1139') else decls,'hypotheses':[],'per_unit_reason':'The new true policy-law and finite-prefix components are approved in their exact scopes. The existing complete paragraph includes other mathematics and universal action wording; this supplemental review does not approve those remaining clauses by association.','missing_clauses':['Complete literal correspondence outside these three explicit components is not decided here.']} for k in keys],
 'not_selected_in_checkpoint22':True,'named_or_aggregate_execution_claimed':False,'whole_monitoring_exercise_approved':False,'original22_peers_and_times_preserved':True,
 'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(__file__)}
dest=Path('/tmp/monitoring-deterministic-path23-independent-applied-components-review-v1.json')
with dest.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'review':str(dest),'sha256':sha(dest),'groups':len(groups),'public_theorems':len(decls)}))
