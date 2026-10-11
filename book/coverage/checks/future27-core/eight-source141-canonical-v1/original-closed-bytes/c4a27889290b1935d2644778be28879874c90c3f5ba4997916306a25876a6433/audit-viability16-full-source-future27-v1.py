from pathlib import Path
import json, hashlib, datetime, time
ROOT=Path('/home/oxrexkevin/SafetyBased')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=datetime.datetime.now(datetime.timezone.utc).isoformat(); tick=time.monotonic()
files=['book/coverage/inventory.json','book/coverage/modules.json','SafeLearning/viability.html','verification/lean/SafeLearning/CompleteModulesValues.lean']
before={p:sha(ROOT/p) for p in files}
inv=json.loads((ROOT/files[0]).read_text()); ledger=json.loads((ROOT/files[1]).read_text())
ex=next(r for r in inv['exercises'] if r['key']=='viability.html::exercise-16')
old=next(r for r in ledger['exercises'] if r['inventory_key']==ex['key'])
keys=['viability.html::node-1113','viability.html::node-1117','viability.html::node-1118']
units=[next(r for r in inv['material_source_units'] if r['key']==k) for k in keys]
assert ex['source_sha256']==before['SafeLearning/viability.html']
assert all(r['source_sha256']==ex['source_sha256'] for r in units)
assert all(hashlib.sha256(r['source_text'].encode()).hexdigest()==r['text_sha256'] for r in [ex,*units])
lines=(ROOT/'SafeLearning/viability.html').read_text().splitlines(keepends=True)
contexts=[{'first_line':a,'last_line':b,'source_text':''.join(lines[a-1:b])} for a,b in [(142,220),(249,285),(357,381),(887,907),(1114,1152),(1174,1230)]]
source=(ROOT/files[3]).read_text()
assert 'Mapping every policy of the explorer' in json.dumps(old)
# Recompute literal JS transition structure, then read off every permissible second action.
slope={(3,2),(3,3),(3,4),(3,5),(2,3),(2,4)}
acts=[('U',-1,0),('D',1,0),('L',0,-1),('R',0,1),('S',0,0)]
av=lambda x:[1,2,3,4] if x in slope else list(range(5))
def step(x,a):
 name,dr,dc=acts[a]; r,c=x
 r=max(0,min(4,r+dr)); c=max(0,min(7,c+dc))
 if x in slope:r=min(4,r+1)
 return 'failure' if r==4 else (r,c)
table=[]
for a in av((2,3)):
 nxt=step((2,3),a)
 row={'first_action_index':a,'first_action':acts[a][0],'first_successor':nxt,'second_successors':[]}
 if nxt!='failure':
  row['second_successors']=[{'action_index':b,'action':acts[b][0],'successor':step(nxt,b)} for b in av(nxt)]
  assert all(r['successor']=='failure' for r in row['second_successors'])
 table.append(row)
assert table[0]['first_successor']=='failure'
assert [r['first_successor'] for r in table[1:]]==[(3,2),(3,4),(3,3)]
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
report={
 'schema_version':1,'status':'completed_full_source_gap_audit_future27_no_whole_promotion','reviewer':'Applied agent /root/applied_next','review_time_utc':end,
 'scope':'Full Viability Exercise 7.2 and all three actual physical question/answer units, selected CompleteModulesValues full source, section hypotheses and literal JS explorer transition/reward/Q-value implementation.',
 'current_inventory':{'file':files[0],'sha256':before[files[0]]},'entire_inventory_record':ex,'material_units':[{'source_unit_key':u['key'],'entire_inventory_record':u,'whole_unit_approved':False} for u in units],
 'original_current_ledger_exercise_record':old,'original_current_ledger_sha256':before[files[1]],'selected_proof':{'file':files[3],'sha256':before[files[3]],'entire_source_text':source},'full_contexts_read':contexts,
 'primary_source':{'url':'https://arxiv.org/pdf/2105.12204','version':'v4, accepted TAC 2023','scope_read':'Page 5: Assumption 1 and complete Lemma 2 statement/proof, equations (12b), (13), (16), (17). Website explicit nonnegative reward bound and one-time failure/sink convention retained.'},
 'already_selected_components':['Exact finite stopped discounted reward bound with 0<=gamma<1, R>=0, p>=0 and failure<=horizon.','Supremum preserves a pointwise bound.','Both candidate returns obey R=0 bound, strict slow/fast comparison and negative-R counterexample.'],
 'remaining_whole_gaps':['Actual transition-derived classification of every admissible zero-slip controller at (2,3), with exact arrival times and zero sink tail, rather than supplied scalar candidate values.','Attainment of both actual trajectory returns and equality of actual controller supremum to their maximum.','Direct infinite counting-sum G/rho correspondence under failure/sink semantics, followed by controller/state suprema, and actual reward bound along unviable trajectories.'],
 'planned_exact_mathematical_scope':['Full source grid dimensions/actions/slope list and clamp/move/slide dynamics.','Arbitrary realized actions with source admissibility, including stationary/history controllers through their realized trajectories.','Actual t=1/t=2 failure classification, all tail states sink, actual finite-support discounted rewards and failure indicator.','Actual max return attained by admissible constant-Down/constant-Stay controllers.','Generic stopped sequence finite-support sums, nonnegative-R extension and two suprema.'],
 'actual_js_recomputed_transition_table':table,
 'limitations':['No Lean source has been compiled for this future27 pack.','No new theorem or whole exercise/material approval is claimed.','The source simulator numerical solver convergence or PRNG behavior is not claimed.','No existing book, owner, HTML, inventory, canonical proof or publication byte was mutated.'],
 'protected_read_inputs_sha256':before,'errors':[]}
after={p:sha(ROOT/p) for p in files}; assert before==after
report['protected_read_inputs_after_sha256']=after
out=Path('/tmp/applied-viability16-future27-full-source-gap-audit-v1.json'); assert not out.exists(); out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
record={'schema_version':1,'label':'Measured read-only source gap audit, not Lean execution or independent approval','actual_command':['python3','/tmp/audit-viability16-full-source-future27-v1.py'],'working_directory':str(ROOT),'started_at_utc':start,'ended_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'actual_exit_code':0,'report':{'file':str(out),'sha256':sha(out)},'source_inputs_before_sha256':before,'source_inputs_after_sha256':after}
rec=Path('/tmp/applied-viability16-future27-full-source-gap-audit-actual-v1.json');assert not rec.exists();rec.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record['report']))
