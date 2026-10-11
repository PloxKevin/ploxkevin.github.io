from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def ref(p):return {'file':str(p),'sha256':sha(p)}
trial_number=int(sys.argv[1]); trial=Path(f'/tmp/applied-explorer-slope27-trial{trial_number}.json');tr=read(trial)
assert type(tr['actual_exit_code']) is int and tr['actual_exit_code']==0 and tr['protection_errors']==[]
source=Path(tr['source']);text=source.read_text()
assert tr['source_sha256_before']==tr['source_sha256_after']==tr['source_snapshot_sha256']==sha(source)==sha(tr['source_snapshot'])
assert sha(tr['raw_log'])==tr['raw_log_sha256'];assert not re.search(r'^.*:\d+:\d+: error(?::|\()',Path(tr['raw_log']).read_text(),re.M)
names=re.findall(r'^theorem\s+(\w+)',text,re.M);assert len(names)==42 and len(set(names))==42
assert not re.search(r'\b(?:sorry|admit|axiom)\b',text)
oldpath=Path('/tmp/applied-viability16-future27-source-and-uncompiled-draft-request-v1.json');old=read(oldpath)
inv=read(ROOT/'book/coverage/inventory.json');assert sha(ROOT/'book/coverage/inventory.json')==old['current_inventory']['sha256']
assert next(r for r in inv['exercises'] if r['key']=='viability.html::exercise-16')==old['entire_inventory_record']
for unit in old['material_units']:assert next(r for r in inv['material_source_units'] if r['key']==unit['source_unit_key'])==unit['entire_inventory_record']
for p,h in old['protected_source53_and_installed26_inputs_sha256'].items():assert sha(ROOT/p)==h,p
ledger=read(ROOT/'book/coverage/modules.json');assert next(r for r in ledger['exercises'] if r['inventory_key']=='viability.html::exercise-16')==old['current_installed26_original_exercise_row']
history=[];closure={}
def add(p):p=Path(p);closure[str(p)]=sha(p);return ref(p)
for i in range(1,trial_number+1):
 p=Path(f'/tmp/applied-explorer-slope27-trial{i}.json');d=read(p);assert d['protection_errors']==[]
 assert sha(d['source_snapshot'])==d['source_snapshot_sha256']==d['source_sha256_before'];assert sha(d['raw_log'])==d['raw_log_sha256']
 history.append({'record':add(p),'entire_actual_record':d,'raw_log':add(d['raw_log']),'source_snapshot':add(d['source_snapshot']),'original_source':add(d['source'])})
cachepath=Path('/tmp/root-working27-existing-imports-cache-build-actual-v1.json');cache=read(cachepath)
assert cache['actual_exit_code']==0 and cache['protection_errors']==[] and sha(cache['raw_log'])==cache['raw_log_sha256']
cacheclosure={'record':add(cachepath),'entire_actual_record':cache,'raw_log':add(cache['raw_log']),'actual_runner':add(cache['actual_runner']['file'])}
ns='SafeLearning.CompleteAppliedExplorerSlope27.'
def decls(xs):return [ns+n for n in xs]
units=[]
for u in old['material_units']:
 n=u['source_unit_key'].split('-')[-1]
 group=names if n=='1113' else names[25:]+[names[9],names[11]] if n=='1117' else names[:25]+[names[30]]
 units.append({'source_unit_key':u['source_unit_key'],'entire_inventory_record':u['entire_inventory_record'],'whole_unit_approved':False,'requested_review':'Full literal and all surrounding assumptions; approve only if every clause is covered.','proposed_lean_declarations':decls(group),'source_correspondence':old['intended_per_unit_correspondence'][u['source_unit_key']]})
for p in sorted(Path('/tmp').glob('CompleteAppliedExplorerSlope27-draft-v*.lean')):add(p)
for pat in ['extend-explorer-slope27-draft-v*.py','repair-applied-explorer-slope27-draft-v*.py','prepare-applied-explorer-slope27-source-packet-v*.py']:
 for p in sorted(Path('/tmp').glob(pat)):add(p)
for p in [oldpath,'/tmp/applied-viability16-future27-full-source-gap-audit-v1.json','/tmp/audit-viability16-full-source-future27-v1.py','/tmp/applied-viability16-future27-full-source-gap-audit-actual-v1.json','/tmp/applied-viability16-uncompiled-v7-independent-foundations-preliminary-scope-observation-v1.json','/tmp/applied-viability16-source-packet-preparation-v1-failed-tool-observation.json','/tmp/applied-explorer-slope27-independent-grid-calculation-v1.json','/tmp/root_tmp_lean27_runner_v2.py','/tmp/applied-safe-value-functions-v4-primary27.pdf','/tmp/applied-safe-value-functions-v4-primary27.txt']:
 add(p)
add(__file__)
for dep in old['full_selected_dependency_sources']:assert sha(dep['source']['file'])==dep['source']['sha256']
packet={'status':'ready_actual_standalone_tmp42_full_literal_review_request_not_whole_approved','created_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/applied_next','current_inventory':old['current_inventory'],'entire_inventory_record':old['entire_inventory_record'],'material_units':units,'whole_exercise_approved':False,'requested_whole_exercise_scope':True,'new_selected_coverage':0,'proof_source':ref(source),'entire_proof_source':text,'public_theorem_names':decls(names),'public_theorem_count':42,'actual_standalone':{'record':ref(trial),'entire_actual_record':tr,'raw_log':ref(tr['raw_log']),'source_snapshot':ref(tr['source_snapshot'])},'actual_named_build_or_canonical_installation':False,'genuine_trial_history':history,'actual_existing_selected_import_cache_build':cacheclosure,'original_uncompiled_request':ref(oldpath),'entire_original_uncompiled_request_body_and_time':old,'original_gap_audit':old['original_gap_audit'],'entire_original_gap_audit_body_and_time':old['entire_original_gap_audit_body_and_time'],'original_preliminary_scope_advice':old['original_preliminary_uncompiled_scope_advice'],'entire_original_preliminary_scope_advice_body_and_time':old['entire_original_preliminary_scope_advice_body_and_time'],'full_selected_dependency_sources':old['full_selected_dependency_sources'],'entire_original_contexts_read':old['entire_original_contexts_read'],'official_primary_archive':old['official_primary_archive'],'current_installed26_original_exercise_row':old['current_installed26_original_exercise_row'],'current_installed26_original_overlapping_material_claims':old['current_installed26_original_overlapping_material_claims'],'source_hypotheses_to_retain':old['source_hypotheses_to_retain'],'actual_independent_grid_calculation':ref('/tmp/applied-explorer-slope27-independent-grid-calculation-v1.json'),'closed_original_evidence_sha256':closure,'protected_source53_and_installed26_inputs_sha256':old['protected_source53_and_installed26_inputs_sha256'],'protected_source_counts':old['protected_source_counts'],'limitations':['Actual TMP standalone proof is not a canonical paired build or selected whole coverage.','Original gap/preliminary/uncompiled decisions and timestamps remain exact and are not rewritten.','Physical domain excludes the bookkeeping sink; only physical visited rewards are bounded by its reward supremum.','Generic true uniform horizon and source feedback/allowed-action/failure-sink conventions remain explicit.','No current owner, selected source, inventory, browser/manual report, publication or Git write.'],'errors':[]}
out=Path('/tmp/applied-viability16-future27-actual42-full-source-review-request-v2.json');assert not out.exists();out.write_text(json.dumps(packet,indent=2)+'\n')
for p,h in old['protected_source53_and_installed26_inputs_sha256'].items():assert sha(ROOT/p)==h,p
print(json.dumps({'file':str(out),'sha256':sha(out),'actual_standalone_exit':0,'public_theorems':42,'whole_approved':False,'closed_originals':len(closure)}))
