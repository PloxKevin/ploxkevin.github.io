from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,copy
R=Path('/home/oxrexkevin/SafetyBased');Q=Path('/tmp/foundations-balanced-sensor27-three-literals-full-source-review-request-v1.json');OUT=Path('/tmp/foundations-balanced-sensor27-three-literals-independent-modules-full-source-review-v1.json')
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':str(n),'sha256':sha(n)}
def checkref(row):assert sha(row['file'])==row['sha256'];return path(row['file'])
assert sha(Q)=='15bc3ada3fac9223915f222b9c720c4903bcd7df78ddae563a86cf8df30b03aa'
d=read(Q);selection=read(checkref(d['actual_installed26_selection']));checkref(d['actual_installed26_global']);checkref(d['current_inventory'])
source=checkref(d['source']);assert source.read_text()==d['entire_lean_source'];assert 'sorry'not in source.read_text()and 'axiom 'not in source.read_text()
names=re.findall(r'^theorem (\w+)',source.read_text(),re.M);assert len(names)==d['public_theorem_count']==16
prefix='SafeLearning.CompleteFoundationsBalancedSensorReconstruction27.';decls=[prefix+x for x in names];assert decls==d['all_public_declarations']
a=read(checkref(d['actual_standalone']));assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['source_sha256_before']==a['source_sha256_after']==d['source']['sha256']==sha(a['source_snapshot'])==a['source_snapshot_sha256']
assert sha(a['raw_log'])==a['raw_log_sha256']==d['actual_raw_log']['sha256'];checkref(a['original_actual_runner']);assert path(a['raw_log']).read_text().count('warning:')==d['real_warning_groups']==4
for n,h in d['all_original_history_sha256'].items():assert sha(n)==h,n
old=read('/tmp/foundations-balanced-sensor27-trial1.json');assert type(old['actual_exit_code'])is int and old['actual_exit_code']==1 and old['protection_errors']==[]
selected=d['selected_full_dependency'];checkref(selected);assert path(selected['file']).read_text()==selected['entire_lean_source'];assert selection['proof_files'][selected['file']]['sha256']==selected['sha256']
for n,h in selected['entire_original_selected_proof_row']['evidence_sha256'].items():assert sha(n)==h,n
ctx=d['full_context'];checkref(ctx);excerpt=''.join(path(ctx['file']).read_text().splitlines(keepends=True)[ctx['first_line']-1:ctx['last_line']]);assert excerpt==ctx['exact_excerpt']and hashlib.sha256(excerpt.encode()).hexdigest()==ctx['excerpt_sha256']
inventory=read(d['current_inventory']['file']);index={r['key']:r for r in inventory['material_source_units']};ledger=read('book/coverage/foundations.json');oldindex={r['id']:r for r in ledger['material_claims']};units=[]
reasons={
'primer-linalg.html::node-1266':'Both actual matrix inverse products identify the genuine inverse of the displayed H. The continuous linear matrix action and cancellation prove H inverse applied to (Hz+eta), minus z, equals inverseH eta for every real displacement and additive error. This is the entire literal conditional known-H model; no physical calibration conclusion is inferred.',
'primer-linalg.html::node-1268':'The actual inverse matrix acts as half the sum and difference. The Euclidean norm square identity and nonnegative square-root argument prove the exact norm ratio norm(eta)/sqrt2; the two closed absolute sensor bounds imply the real Euclidean reconstructed norm is at most1/10. The millimetre notation is the stated coordinate unit of the teaching model.',
'primer-linalg.html::node-1269':'The exact readings(6,2) reconstruct(4,2). The inverse image of the sensor box is exactly {|e0+e1|<=1/10,|e0-e1|<=1/10}; all four corner images and the forbidden independent box corner are explicit. At |e0|=1/10, e1 must be zero. The attained permitted error(-1/10,0) gives worst true first displacement41/10, every permitted value satisfies83/20, and an actual permitted witness exceeds81/20. These are the entire conditional upper-limit and coupling clauses, without a sampling or physical model-validity guarantee.'}
for row in d['literal_units']:
 key=row['source_unit_key'];literal=row['entire_inventory_record'];assert literal==index[key];assert sha(literal['source'])==literal['source_sha256'];assert hashlib.sha256(literal['source_text'].encode()).hexdigest()==literal['text_sha256']
 for oldrow in row['original_current_ledger_records']:assert oldindex[oldrow['id']]==oldrow
 components=[copy.deepcopy(c)for c in d['precise_component_groups']if key in c['source_unit_keys']]
 used=list(dict.fromkeys(n for c in components for n in c['lean_declarations']));assert set(used)<=set(decls)
 units.append({'source_unit_key':key,'entire_inventory_record':copy.deepcopy(literal),'status':'proved','decision':'whole_literal_approved','whole_literal_approved':True,'components':components,'lean_declarations':used,'hypotheses':[h for c in components for h in c['hypotheses']],'reason':reasons[key],'missing_clauses':[],'remaining_gaps':[],'original_current_ledger_records':copy.deepcopy(row['original_current_ledger_records'])})
held={n:r['sha256']for n,r in selection['proof_files'].items()};held.update(inventory['source_sha256']);held.update(a['installed26_owner_sha256']);assert len(selection['proof_files'])==1167 and len(inventory['source_sha256'])==31 and len(a['installed26_owner_sha256'])==5
for n,h in held.items():assert sha(n)==h,n
output={'status':'passed_independent_full_three_literal_balanced_sensor_source_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','request':ref(Q),'original_request_body':d,'source':d['source'],'entire_source_body_read':d['entire_lean_source'],'all16_full_theorem_bodies_read':True,'selected_dependency_entire_body_read':selected,'actual_standalone':d['actual_standalone'],'actual_raw_log':d['actual_raw_log'],'genuine_warning_groups':4,'original_trial1_failure_preserved':True,'all_original_history_sha256':d['all_original_history_sha256'],'material_units':units,'complete_literal_approved_keys':[u['source_unit_key']for u in units],'whole_literal_count':3,'public_theorem_count':16,'precise_component_groups':d['precise_component_groups'],'protected_current1167_sources31_assets5_owners_exact':True,'not_reviewed_adjacent_unit':d['whole_unit_not_in_request'],'scope':'Full semantic review of only three exact source53 material literals and all16 theorem bodies, selected exact Euclidean dependency, context, actual TMP compiler evidence and retained failures. No parent exercise, adjacent singular-value/condition-number, named/canonical/installation, fresh aggregate or physical calibration claim.'}
assert not OUT.exists();OUT.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps({'file':str(OUT),'sha256':sha(OUT),'whole_literals':3,'theorem_bodies':16}))
