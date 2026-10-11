from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n):return json.loads(path(n).read_text())
reqname='/tmp/foundations-finite-prefix23-source-review-request-v1.json';q=read(reqname)
assert sha(reqname)=='a4b50adbef83edc70fa674beef20fb478a0bc4c810c558b2cea3d70c73361708'
invref=q['current48_inventory'];assert sha(invref['file'])==invref['sha256']
inv=read(invref['file']);r=next(r for r in inv['material_source_units'] if r['key']==q['literal_unit_key'])
assert r['source_text']==q['exact_pending_claim']['source_text'] and r['text_sha256']==q['exact_pending_claim']['source_text_sha256']
assert sha(r['source'])==r['source_sha256']==q['current48_source_sha256']
assert q['full_parent_exercise_HTML_context'] in path(r['source']).read_text()
src=q['new_proof_source'];assert sha(src)==q['new_proof_source_sha256'];body=path(src).read_text()
assert body.count('\ntheorem ')==q['public_theorem_count']==6
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',body)
for t in q['full_public_theorem_bodies']:assert t['full_statement_and_body'] in body
history=[]
for h in q['actual_original_Lean_trial_history']:
 for name,key in [('original_execution_record','original_execution_record_sha256'),('actual_source','actual_source_sha256'),('actual_raw_log','actual_raw_log_sha256')]:assert sha(h[name])==h[key]
 x=read(h['original_execution_record']);assert x['actual_exit_code']==h['actual_exit_code'];assert x['source_sha256_before']==x['source_sha256_after']==h['actual_source_sha256'];assert x['log_sha256']==h['actual_raw_log_sha256']
 history.append(h)
assert history[-1]['actual_exit_code']==0 and path(history[-1]['actual_raw_log']).read_bytes()==b''
failed=q['original_request_assembly_observed_failure'];assert sha(failed['file'])==failed['sha256']
math=q['direct_local_Mathlib_semantics'];assert sha(math['file'])==math['sha256']
selected=q['selected21_exercise_source'];assert sha(selected['file'])==selected['sha256']
basename='reports/full-coverage/checkpoint-21-selection.json';base=read(basename);row=base['proof_files'][selected['file']];assert row['sha256']==selected['sha256']
for n,h in row['evidence_sha256'].items():assert sha(n)==h
held=q['unchanged_current22_foundation_candidate'];assert sha(held['file'])==held['sha256']
decls=[x['name'] for x in q['full_public_theorem_bodies']]
reason='The actual printed additive sequence is split into its genuine even and odd subsequences, with respective limits1 and−1. For every EReal-valued sequence and any finite offset, the true limsup is invariant under deleting that prefix; arbitrary replacement of finitely many initial entries likewise leaves limsup unchanged. This covers both complete hint sentences, with no real boundedness premise or finite-value restriction on the generic extended result.'
hyp=['Source sequence a_t=(-1)^t+1/(t+1), indexed by natural numbers t≥0.','For the generic prefix statements, arbitrary a,b:ℕ→EReal and finite N; replacement requires equality for all n≥N.']
unit={'source_unit_key':r['key'],'source':r['source'],'source_sha256':r['source_sha256'],'line':r['line'],'locator':r['locator'],'unit_text_sha256':r['text_sha256'],'source_text':r['source_text'],'entire_inventory_record':r,'material_status':'proved','whole_unit_approved':True,'lean_declarations':decls,'hypotheses':hyp,'per_unit_reason':reason,'missing_clauses':[],'approved_components':[{'id':'finite-prefix1075-complete-hint','source_unit_keys':[r['key']],'source_clause':r['source_text'],'lean_declarations':decls,'hypotheses':hyp,'per_component_reason':reason,'review_status':'approved_complete_source_clause','missing_clauses':[]}]}
out={'status':'independent_complete_literal_source_review_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':invref['file'],'inventory_sha256':invref['sha256'],'source':r['source'],'source_sha256':r['source_sha256'],'original_review_request':{'file':reqname,'sha256':sha(reqname)},'full_parent_exercise_HTML_context':q['full_parent_exercise_HTML_context'],'material_units':[unit],'actual_new_proof_evidence':{'source':src,'sha256':sha(src),'standalone_record':history[-1]['original_execution_record'],'standalone_record_sha256':history[-1]['original_execution_record_sha256'],'actual_exit_code':0,'actual_record_body':read(history[-1]['original_execution_record']),'raw_log':history[-1]['actual_raw_log'],'raw_log_sha256':history[-1]['actual_raw_log_sha256'],'empty_log':True,'named_execution_claimed':False,'canonical_execution_claimed':False},'actual_original_failure_history':history[:-1],'original_request_assembly_observed_failure':failed,'retained_selected21_dependencies':{selected['file']:row},'local_primary_Mathlib_semantics':math,'held_current22_candidate':held,'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(str(Path(__file__))),'errors':[],'limits':['This is a fresh semantic approval of one complete physical hint1075 only. No parent-exercise or other descendant mapping is inferred.','The old pending component and its original time/body remain historical. No owner ledger, current22 offer, candidate, HTML or inventory is mutated.','The new proof has genuine TMP standalone0 evidence only; canonical and named executions require separate actual records.','Existing selected21 sequence proofs remain unchanged; their retained aggregate evidence is reused without a new compiler run.'],'coverage_complete':False}
dest=Path('/tmp/foundations-finite-prefix1075-independent-modules-source-review23-v1.json');assert not dest.exists();dest.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':out['status'],'file':str(dest),'sha256':sha(str(dest))}))
