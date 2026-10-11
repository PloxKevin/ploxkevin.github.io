from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def ref(p):return {'file':str(p),'sha256':sha(p)}
inv=read(ROOT/'book/coverage/inventory.json')
assert sha(ROOT/'book/coverage/inventory.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
auditpath=Path('/tmp/applied-viability16-future27-full-source-gap-audit-v1.json');audit=read(auditpath)
ex=next(r for r in inv['exercises'] if r['key']=='viability.html::exercise-16')
assert ex==audit['entire_inventory_record']
keys=['viability.html::node-1113','viability.html::node-1117','viability.html::node-1118']
units=[next(r for r in inv['material_source_units'] if r['key']==k) for k in keys]
assert units==[r['entire_inventory_record'] for r in audit['material_units']]
ledger=read(ROOT/'book/coverage/modules.json')
oldexercise=next(r for r in ledger['exercises'] if r['inventory_key']=='viability.html::exercise-16')
assert oldexercise==audit['original_current_ledger_exercise_record']
selectionpath=ROOT/'reports/full-coverage/checkpoint-26-selection.json';selection=read(selectionpath)
assert selection['proof_file_count']==len(selection['proof_files'])==1167
bindingpath=ROOT/'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json';binding=read(bindingpath)
integrationpath=ROOT/'reports/full-coverage/owner26-reviewed-candidate-integration-v1.json';integration=read(integrationpath)
held={p:r['sha256'] for p,r in selection['proof_files'].items()}
held.update(binding['exact_current53_safelearning_assets_sha256'])
held.update({r['destination']:r['candidate']['sha256'] for r in integration['exact_replacements']})
assert len(binding['exact_current53_safelearning_assets_sha256'])==31
for p,h in held.items():assert sha(ROOT/p)==h,p
source=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v8.lean');text=source.read_text()
assert source.read_bytes().startswith(Path('/tmp/CompleteAppliedExplorerSlope27-draft-v7.lean').read_bytes())
names=re.findall(r'^theorem\s+(\w+)',text,re.M);assert len(names)==42
assert not re.search(r'\b(?:sorry|admit|axiom)\b',text)
dependencies=[]
for p in ['verification/lean/SafeLearning/CompleteModulesValues.lean','verification/lean/SafeLearning/CompleteFoundationsGraphViability.lean']:
 row=selection['proof_files'][p]
 assert sha(ROOT/p)==row['sha256']
 for ep,h in row.get('evidence_sha256',{}).items():assert sha(ROOT/ep)==h,ep
 dependencies.append({'source':ref(ROOT/p),'entire_source':(ROOT/p).read_text(),'entire_selected_proof_row':row})
claims=[r for r in ledger['material_claims'] if any(k in r.get('source_unit_keys',[]) for k in keys)]
trial=Path('/tmp/applied-explorer-slope27-trial1.json');tr=read(trial)
assert tr['actual_exit_code']==1 and tr['protection_errors']==[]
assert tr['source_sha256_before']==tr['source_sha256_after']==sha(source)
assert sha(tr['raw_log'])==tr['raw_log_sha256']
assert 'CompleteModulesValues.olean' in Path(tr['raw_log']).read_text()
packet={
 'status':'prepared_uncompiled_whole_source_future27_request_with_genuine_dependency_failure',
 'created_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/applied_next',
 'scope':'Entire Viability Exercise 7.2 plus all three physical question/answer units; genuine controller/transition/counting-measure correspondence, not scalar candidate assumptions.',
 'current_inventory':ref(ROOT/'book/coverage/inventory.json'),'entire_inventory_record':ex,
 'material_units':[{'source_unit_key':r['key'],'entire_inventory_record':r,'whole_unit_approved':False} for r in units],
 'whole_exercise_approved':False,'new_proved_coverage':0,
 'draft_source':ref(source),'entire_draft_source':text,'public_theorem_draft_names':names,'public_theorem_draft_count':42,
 'compile_status':'First actual trial stopped at missing selected dependency cache; no new theorem body has elaborated.',
 'original_gap_audit':ref(auditpath),'entire_original_gap_audit_body_and_time':audit,
 'original_preliminary_uncompiled_scope_advice':ref('/tmp/applied-viability16-uncompiled-v7-independent-foundations-preliminary-scope-observation-v1.json'),
 'entire_original_preliminary_scope_advice_body_and_time':read('/tmp/applied-viability16-uncompiled-v7-independent-foundations-preliminary-scope-observation-v1.json'),
 'all_original_uncompiled_drafts':[ref(f'/tmp/CompleteAppliedExplorerSlope27-draft-v{i}.lean') for i in range(1,9)],
 'draft_author_helpers':[ref(p) for p in sorted(Path('/tmp').glob('extend-explorer-slope27-draft-v*.py'))],
 'actual_first_dependency_failure':{'record':ref(trial),'entire_actual_record':tr,'raw_log':ref(tr['raw_log']),'source_snapshot':ref(tr['source_snapshot']),'runner':ref('/tmp/root_tmp_lean27_runner_v2.py'),'new_proof_bodies_elaborated':False},
 'full_selected_dependency_sources':dependencies,
 'current_installed26_original_exercise_row':oldexercise,'current_installed26_original_overlapping_material_claims':claims,
 'entire_original_contexts_read':audit['full_contexts_read'],
 'official_primary_archive':{'url':'https://arxiv.org/pdf/2105.12204','version':'v4 accepted TAC2023','pdf':ref('/tmp/applied-safe-value-functions-v4-primary27.pdf'),'text':ref('/tmp/applied-safe-value-functions-v4-primary27.txt'),'scope':'Full page5 Assumption1/Lemma2 proof read; source nonnegative reward and explicit one-time failure/sink convention retained. Text extraction emits one xref reconstruction warning; original PDF unchanged.'},
 'source_hypotheses_to_retain':['0<discount<1','nonnegative penalty and living cost','true uniform failure horizon for every physical unviable state and controller','greatest safe controlled invariant kernel, with actual legal transitions','bounded reward on physical unviable states×actions','one-time failure event followed by zero-reward sink','nonempty feedback controller class; possible empty outer unviable domain represented by EReal supremum','zero slip for the actual explorer calculation','source-cell slope slide and Up unavailable on slope cells'],
 'intended_per_unit_correspondence':{
  keys[0]:'Question requires every general counting-sum/physical-domain/supremum clause and actual explorer trajectory calculation; retain entire scope before any whole decision.',
  keys[1]:'Greatest-kernel forward unviability, stopped finite support, actual Bochner counting integral, arrival-weight risk, both sign directions, selected geometric bound, physical reward supremum and both state/controller suprema.',
  keys[2]:'Full literal JS model, all upper paths classified fast/slow, both stationary feedback attainers, exact maximum, true actual R_XU=0, uniform failure≤2, strict slow threshold and exact negative-bound counterexample.'},
 'limitations':['All42 theorem drafts remain uncompiled.','Preliminary semantic advice is not kernel verification or a whole-source approval.','No current ledger, canonical proof, selected source, browser, HTML, inventory, publication or Git write.','No stronger nonphysical-sink reward bound is required by the three distinct v8 wrappers.'],
 'actual_installed26_selection':ref(selectionpath),'actual_installed26_integration':ref(integrationpath),'protected_source53_and_installed26_inputs_sha256':held,
 'protected_source_counts':{'selected_proofs':1167,'current_source53_assets':31,'installed_live_owner_ledgers_and_promotions':5},'preserved_packet_preparation_failure':{'helper':ref('/tmp/prepare-applied-explorer-slope27-source-packet-v1.py'),'actual_tool_observation':ref('/tmp/applied-viability16-source-packet-preparation-v1-failed-tool-observation.json')},'errors':[]}
out=Path('/tmp/applied-viability16-future27-source-and-uncompiled-draft-request-v1.json');assert not out.exists();out.write_text(json.dumps(packet,indent=2)+'\n')
for p,h in held.items():assert sha(ROOT/p)==h,p
print(json.dumps({'file':str(out),'sha256':sha(out),'whole_approved':False,'theorem_drafts':42,'new_proved_coverage':0}))
