from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
inv=read(ROOT/'book/coverage/inventory.json');ledger=read(ROOT/'book/coverage/foundations.json')
assert sha(ROOT/'book/coverage/inventory.json')=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
source=TMP/'foundations-semicontinuity23-trial2.lean'
assert sha(source)=='280be25369c9cc9b3336d87ada8e5cf4d899cd454da1a4cabcf33725cb612b14'
record=TMP/'foundations-semicontinuity23-trial2.json';actual=read(record)
assert actual['actual_exit_code']==0 and actual['source_sha256_before']==actual['source_sha256_after']==sha(source)
assert sha(Path(actual['raw_log']))==actual['raw_log_sha256']
ns='SafeLearning.CompleteFoundationsSemicontinuity23'
names=[ns+'.'+m.group(1) for m in re.finditer(r'^theorem ([A-Za-z0-9_]+)',source.read_text(),re.M)]
assert len(names)==10
units={r['key']:r for r in inv['material_source_units']}
keys=['primer-basics.html::node-1202','primer-basics.html::node-1237']
rows=[]
for key in keys:
 literal=units[key];pending=[r for r in ledger['material_claims'] if key in r['source_unit_keys'] and r['status']=='pending']
 assert pending and sha(ROOT/literal['source'])==literal['source_sha256']
 rows.append({'source_unit_key':key,'entire_inventory_record':literal,'entire_original_pending_claim_rows':pending,'whole_unit_requested':True,'candidate_missing_clauses':[], 'proposed_precise_groups':(['genuine_first_countable_sequence_EReal_liminf_iff','all_real_closed_sublevel_iff','actual_nonempty_compact_minimum_and_compact_sublevel','actual_printed_step_all_sublevels_and_lower_semicontinuity','Module8_cross_reference_only'] if key.endswith('1202') else ['general_continuous_nonempty_compact_minimum','actual_continuous_square_unique_minimum_on_noncompact_real_line','Find_the_infimum_first_proof_guidance_only'])})
parent=next(r for r in inv['exercises'] if r['key']=='primer-basics.html#mb-ex-topology-2')
html=(ROOT/'SafeLearning/primer-basics.html').read_text().splitlines(keepends=True)
hist=[]
for n in [1,2]:
 p=TMP/f'foundations-semicontinuity23-trial{n}.json';r=read(p)
 assert sha(Path(r['source']))==r['source_sha256_before']==r['source_sha256_after']
 assert sha(Path(r['raw_log']))==r['raw_log_sha256']
 hist.append({'record':{'file':str(p),'sha256':sha(p)},'entire_original_actual_record':r,'source_snapshot':{'file':r['source'],'sha256':r['source_sha256_after']},'raw_log':{'file':r['raw_log'],'sha256':r['raw_log_sha256']}})
protected=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')
for name,row in protected['proof_files'].items():assert sha(ROOT/name)==row['sha256']
guards={n:h for n,h in protected['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/inventory.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}}
for name,digest in guards.items():assert sha(ROOT/name)==digest
primary=[]
for name,scope in [('Mathlib/Topology/Semicontinuity/Basic.lean','Lines75–111 actual compact minimum filter proof; lines234–246 closed sublevel equivalence; lines255–264 continuous→semicontinuous; lines306–315 compact sublevels.'),('Mathlib/Topology/Semicontinuity/Defs.lean','LowerSemicontinuousAt threshold definition and of_frequently equivalence, lines280–335/563–575.'),('Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean','Lines110–122 genuine sequence with all prescribed frequent values.'),('Mathlib/Order/LiminfLimsup.lean','Complete-order liminf/limsup comparison and eventual-bound lemmas, lines105–142.'),('Mathlib/Topology/Order/Compact.lean','Lines228–231 genuine compact continuous minimum via actual image IsLeast; dual maximum theorem used to disprove compactness of real line.')]:
 p=ROOT/'verification/lean/.lake/packages/mathlib'/name
 primary.append({'file':str(p.relative_to(ROOT)),'sha256':sha(p),'direct_read_scope':scope})
result={'status':'genuine_TMP_standalone_zero_complete_literals_basics1202_1237_peer_requested_future23','created_at_utc':datetime.now(timezone.utc).isoformat(),'review_request':'Independently read all ten complete theorem bodies and helpers, both entire current48 literals, all source context and full parent exercise. Approve whole source units only if every mathematical clause is covered with the true assumptions. Sequence liminf lives in EReal and requires first countable topology, which covers the source Euclidean setting. Do not promote the parent exercise or rewrite any earlier semantic review. Retain original warning/failure execution bytes.','inventory':{'file':'book/coverage/inventory.json','sha256':sha(ROOT/'book/coverage/inventory.json')},'held_foundations22_ledger':{'file':'book/coverage/foundations.json','sha256':sha(ROOT/'book/coverage/foundations.json')},'material_units':rows,'full_parent_exercise_record':parent,'full_source_HTML_context':{'file':'SafeLearning/primer-basics.html','sha256':sha(ROOT/'SafeLearning/primer-basics.html'),'first_line':1274,'last_line':1325,'exact_lines':''.join(html[1273:1325])},'new_proof_source':{'file':str(source),'sha256':sha(source),'entire_source':source.read_text()},'public_theorem_names':names,'public_theorem_count':10,'actual_original_standalone':hist[1],'all_actual_unique_trial_history':hist,'trial1_failure_description':'Genuine original proof diagnostics: using strict-order le_of_forall_lt where dense nonstrict version was required, missing order type annotation, and negated-iff simplification before arithmetic. Trial2 corrects these proof steps without weakening statements.','actual_runner':{'file':actual['actual_runner'],'sha256':actual['actual_runner_sha256']},'local_primary_Mathlib_semantics':primary,'protected_selected22_source_count':1113,'protected_selected22_manifest':{'file':'reports/full-coverage/checkpoint-22-manifest.json','sha256':sha(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')},'protected_current48_assets_inventory_and_four_working22_ledger_sha256':guards,'whole_parent_exercise_approved':False,'canonical_source_or_named_execution_claimed':False,'coverage_complete':False,'limits':['The current literal is in Euclidean space. Sequence criterion is proved for arbitrary first-countable topological domains and real functions, using genuine EReal liminf so unbounded subsequences remain meaningful.','No conclusion is assumed as a hypothesis: lower semicontinuity is characterized both ways, compact minimum comes from actual lower semicontinuity, and the step sublevels are calculated exactly.','The hint is reviewed as a whole mathematical statement plus its narrow proof-guidance phrase, with explicit continuous square on noncompact real line counterexample. Parent exercise remains independently selected and is not promoted again.','Only immutable TMP trial/request files are written. Canonical/named executions, mapping/candidate and aggregate23 remain separate.']}
out=TMP/'foundations-semicontinuity23-basics1202-1237-full-source-review-request-v1.json'
with out.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'request':str(out),'request_sha256':sha(out),'public_theorems':10,'whole_units_requested':2}))
