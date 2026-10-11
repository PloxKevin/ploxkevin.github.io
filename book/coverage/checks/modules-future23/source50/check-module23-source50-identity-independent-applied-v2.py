from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,sys,ast
ROOT=Path('/home/oxrexkevin/SafetyBased');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();P=lambda p:ROOT/p;read=lambda p:json.loads(P(p).read_text());ref=lambda p:{'file':str(p),'sha256':h(P(p))}
OLD='book/coverage/checks/modules-future23/source49';NEW='book/coverage/checks/modules-future23/source50'
oldname=OLD+'/modules23-candidate-source49-identity-v1.json';newname=NEW+'/modules23-candidate-source50-identity-v1.json';side=NEW+'/unchanged-owned-literal-identity-v1.json';guard=NEW+'/candidate-identity-binding-integrity-v1.json';helper='book/coverage/build_modules23_candidate_source50_identity_v2.py';offer=OLD+'/modules-audit23-candidate-source49-additions-v1-reviewed.json';peer=OLD+'/modules23-source49-identity-independent-applied-confirmation-v1.json'
pins={p:h(P(p)) for p in [oldname,newname,side,guard,helper,offer,peer]}
assert pins[oldname]=='61c51d1732d5225fb04f0303619a7ea23adb4522ce722089e8757742746897eb'
assert pins[offer]=='fd9e1e4847135d664cd29c03add3bfd861e32686a3650e3b31a208b20b28bcce'
assert pins[peer]=='601ad7bd1998fa065935030a0bbddc3e3c706b59f7e71f7befe76c088e8cbc01'
# The exact helper hash is observed from the immutable current file and the actual execution record below.
pins.pop(helper)
for p,sha in pins.items():assert h(P(p))==sha,p
ast.parse(P(helper).read_text())
o,n,s,g=read(oldname),read(newname),read(side),read(guard)
identity={'file':side,'sha256':h(P(side))}
back=copy.deepcopy(n)
for r in back['exercises']:
 assert r.pop('source50_unchanged_literal_identity')==identity
for r in back['material_claims']:
 assert r.pop('source50_unchanged_literal_identity')==identity
back.pop('inventory_identity_rebase50')
for k in ['current_inventory','current_inventory_sha256','current_identity_binding_validation']:back[k]=copy.deepcopy(o[k])
assert back==o
inv48=read('book/coverage/inventory-after-correction49.json');inv49=read('book/coverage/inventory-after-correction50.json')
assert h(P('book/coverage/inventory-after-correction50.json'))=='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
assert h(P('book/coverage/inventory.json'))==h(P('book/coverage/inventory-after-correction50.json'))
assert n['current_inventory']=='book/coverage/inventory-after-correction50.json' and n['current_inventory_sha256']==h(P(n['current_inventory']))
assert n['source_sha256']==o['source_sha256']==s['owned_source_sha256']
for p,sha in o['source_sha256'].items():assert h(P(p))==sha==inv48['source_sha256'][p]==inv49['source_sha256'][p]
counts={}
for kind in ['exercises','material_source_units']:
 a={r['key']:r for r in inv48[kind] if r['source'] in o['scope_pages']};b={r['key']:r for r in inv49[kind] if r['source'] in o['scope_pages']};assert a==b
 rows=s['unchanged_owned_literals'][kind];assert len(rows)==len(a) and {r['key'] for r in rows}==a.keys()
 for r in rows:
  original=a[r['key']]
  digest=hashlib.sha256(json.dumps(original,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
  assert digest==r['entire_inventory_record_sha256']
  for f in ['source','line','locator','text_sha256','source_sha256']:assert r[f]==original[f]
 counts[kind]=len(a)
assert counts=={'exercises':217,'material_source_units':4977}
allchanges={}
for kind in ['exercises','material_source_units']:
 a={r['key']:r for r in inv48[kind]};b={r['key']:r for r in inv49[kind]};assert a.keys()==b.keys()
 delta=[k for k in a if {f:v for f,v in a[k].items() if f!='source_sha256'}!={f:v for f,v in b[k].items() if f!='source_sha256'}]
 assert delta==s['changed_other_owner_literal_text_or_structure_keys'][kind]
 assert all(a[k]['source']=='SafeLearning/lyapunov-mpc.html' for k in delta)
 allchanges[kind]=delta
assert allchanges=={'exercises':['lyapunov-mpc.html::exercise-19'],'material_source_units':['lyapunov-mpc.html::node-1397','lyapunov-mpc.html::node-1401','lyapunov-mpc.html::node-1403']}
execution=NEW+'/modules23-candidate-source50-identity-actual-execution-v2.json';er=read(execution)
assert er['actual_exit_code']==0 and er['actual_checker_sha256_before']==er['actual_checker_sha256_after']==h(P(helper))
assert h(P(er['log']))==er['log_sha256'] and er['actual_workdir']==str(ROOT)
assert helper in str(er['actual_command'])
for key in ['actual_root_source50_apply','actual_root_source50_postwrite']:
 rr=s[key];assert h(P(rr['file']))==rr['sha256'];assert read(rr['file'])['actual_exit_code']==0
for p,sha in g['protected_live22_ledgers_sha256'].items():assert h(P(p))==sha
for p,row in n['proof_files'].items():assert h(P(p))==row['sha256']
for p,sha in read(offer)['required_evidence_artifacts_sha256'].items():assert h(P(p))==sha
manifest='reports/full-coverage/checkpoint-22-manifest.json';m=read(manifest);assert len(m['proof_files'])==1113
for p,row in m['proof_files'].items():assert h(P(p))==row['sha256']
history=[NEW+'/source50-wrapper-pre-execution-failure-observation-v1.json',NEW+'/source50-pre-execution-draft-v1.py',NEW+'/modules23-candidate-source50-identity-actual-execution-v1.json',NEW+'/modules23-candidate-source50-identity-actual-execution-v1.log']
for p in history:assert P(p).is_file()
failed=read(history[2]);assert failed['actual_exit_code']!=0 and h(P(failed['log']))==failed['log_sha256']
assert P(helper).read_text().replace('4977','5077')==P('book/coverage/build_modules23_candidate_source50_identity_v1.py').read_text()
report={'status':'passed_independent_module23_source50_identity_only_candidate_mechanics','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[],'original49_candidate':ref(oldname),'current50_candidate':ref(newname),'identity_sidecar':ref(side),'identity_guard':ref(guard),'helper':ref(helper),'original_final49_peer':ref(peer),'original_reviewed49_offer':ref(offer),'actual_identity_preparation_execution':ref(execution),'actual_identity_preparation_raw_log':ref(er['log']),'checked_counts':{'owned_entire_exercise_records':217,'owned_entire_material_records':4977,'candidate_exercise_bodies':len(n['exercises']),'candidate_material_bodies':len(n['material_claims']),'unchanged_proof_rows':len(n['proof_files']),'selected22_sources':1113},'exact_inverse_normalization_restores_entire_source49_candidate':True,'original_semantic_review_bodies_times_hypotheses_and_evidence_unchanged':True,'changed_source50_other_owner_keys':allchanges,'live22_owner_ledgers_exact':g['protected_live22_ledgers_sha256'],'preserved_first_independent_checker_failure':{'file':'/tmp/module23-source50-identity-independent-applied-first-checker-failure-observation-v1.json','sha256':h('/tmp/module23-source50-identity-independent-applied-first-checker-failure-observation-v1.json')},'preserved_original_failed_attempts':[ref(p) for p in history],'helper_v2_changes_only_5077_count_to_actual4977':True,'actual_checker':{'file':str(Path(__file__)),'sha256':h(Path(__file__))},'limits':['Identity/mechanics confirmation only; no repeated semantic review, new Lean execution, current owner installation, global23 validation or aggregate23 claim.','Root actual source50 changes are retained; the seven original source49-bound historical source48 whole decisions and their review times are unchanged historical evidence.']}
out=Path('/tmp/modules23-source50-identity-independent-applied-confirmation-v2.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(str(out),h(out))
