from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
ROOT=Path('/home/oxrexkevin/SafetyBased');ORIGINAL=Path('/tmp/modules-nn-corrected52-answer-b-independent-foundations-full-source-review25-v1.json');OUT=Path('/tmp/modules-nn-answer-b-selected-universal-monotonicity-evidence-supplement25-v1.json')
def P(p):
 p=Path(p);return p if p.is_absolute()else ROOT/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def R(p):return json.loads(P(p).read_text())
def ref(p):return {'file':str(p),'sha256':H(p)}
assert H(ORIGINAL)=='3aee3315750d7fd05328e2708cf44b58bf8da534806a59e1e12286c6ae5bcc9c';original=R(ORIGINAL)
source='verification/lean/SafeLearning/CompleteFoundationsInequalityChains.lean';digest='4569617c44334a36a51c3fcde01df1926392481684248ffffc077a02c489e957'
assert H(source)==digest;body=P(source).read_text();short=re.findall(r'^theorem\s+(\w+)',body,re.M);assert len(short)==11
ns='SafeLearning.CompleteFoundationsInequalityChains.'
names=[ns+n for n in short]
chosen=[ns+'actual_monotone_function_preserves_weak_order',ns+'actual_nonnegative_multiplication_preserves_weak_order',ns+'actual_negative_multiplication_reverses_order']
assert all(n in names for n in chosen)
compiler_manifest='book/coverage/checks/foundations-held19-source44-actual-compiler-manifest-v1.json'
binding=next(x for x in R(compiler_manifest)['records']if x['source']==source)
standalone=R(binding['canonical_execution_record_copy'])
assert H(binding['canonical_execution_record_copy'])==binding['canonical_execution_record_copy_sha256']==binding['original_execution_record_sha256']
assert standalone==binding['raw_execution_record'] and standalone['exit_code']==binding['actual_exit_code']==0
assert standalone['source']==source and standalone['source_sha256_before']==standalone['source_sha256_after']==digest
assert standalone['command']==binding['original_command']==['/home/oxrexkevin/.elan/bin/lake','env','lean','SafeLearning/CompleteFoundationsInequalityChains.lean']
assert H(binding['canonical_log_copy'])==binding['canonical_log_copy_sha256']==standalone['log_sha256']
snapshot='book/coverage/checks/foundations-held19/source33-originals/foundations-inequality-chains-trial1-source.lean'
assert H(snapshot)==digest
audits=[];original_kernel=None
for n in [19,20,23]:
 path=f'reports/full-coverage/lean-checkpoint-{n}/verification-original.json';audit=R(path)
 assert audit['status']=='passed' and audit['proof_sha256'][source]==digest
 decls=[x['name']for x in audit['declarations']if x['file']==source];assert decls==names
 for name in names:assert set(audit['axiom_dependencies'][name]) <= {'propext','Classical.choice','Quot.sound'}
 assert audit['axiom_dependencies'][chosen[0]]==[]
 row=next(x for x in audit['checks']if x.get('module')=='SafeLearning.CompleteFoundationsInequalityChains')
 assert row['exit_code']==0 and row['command']==['lake','env','leanchecker','-v','SafeLearning.CompleteFoundationsInequalityChains']
 log=f'reports/full-coverage/lean-checkpoint-{n}/'+('kernel-parallel19/'if n==19 else'')+'kernel-SafeLearning-CompleteFoundationsInequalityChains.log'
 assert H(log)==row['log_sha256']=='611abfb0c8061e840cc5a615e2c0eed0e3704d577163cad90aab2a67cf3c13f4'
 if n==19:
  assert row['evidence_mode']=='fresh_kernel_replay';original_kernel=row
 else:
  assert row['evidence_mode']=='reused_identical_module_and_transitive_local_imports'
  assert row['reused_from']['original_check']==original_kernel
  assert row['reused_from']['verified_local_import_sha256']=={source:digest}
 audits.append({'audit':ref(path),'entire_original_module_check_and_time':row,'exact_kernel_log':ref(log),'all11_public_declarations':decls,'axiom_dependencies':{name:audit['axiom_dependencies'][name]for name in names}})
for n in [19,20,23]:
 manifest=R(f'reports/full-coverage/checkpoint-{n}-manifest.json');assert manifest['proof_files'][source]['sha256']==digest
 assert H(f'reports/full-coverage/checkpoint-{n}/'+source)==digest
selected24=R('reports/full-coverage/checkpoint-24-selection.json');assert source in selected24['proof_files']
inventory=R('book/coverage/inventory-after-correction52.json');unit=original['material_units'][0]['entire_inventory_record']
assert unit==next(x for x in inventory['material_source_units']if x['key']==unit['key'])
out={'status':'independent_selected_universal_monotonicity_declaration_and_original_evidence_binding_supplement_passed_future25_tmp_only','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','errors':[],'original_whole_answer_b_peer':ref(ORIGINAL),'entire_original_peer_body_decisions_and_time':original,'original_reviewed_at_utc':original['reviewed_at_utc'],'original_whole_decision_unchanged':True,'source':{'file':source,'sha256':digest},'entire_selected_source_and_all11_bodies_read':body,'selected_lean_declarations':chosen,'actual_original_standalone':{'compiler_manifest':ref(compiler_manifest),'entire_original_binding_row':binding,'canonical_record':ref(binding['canonical_execution_record_copy']),'canonical_raw_log':ref(binding['canonical_log_copy']),'canonical_source_snapshot':ref(snapshot)},'actual19_fresh_and20_23_reused_kernel_records':audits,'current_selected24':ref('reports/full-coverage/checkpoint-24-selection.json'),'component_id':'different_channels_can_reverse_order_but_one_common_monotone_function_cannot','hypotheses':['An arbitrary common monotone function between preorders; for the real product interpretation, all-real inputs and real monotonicity.'],'binding_reason':'The genuinely selected universal export proves a≤b⇒f(a)≤f(b) for arbitrary preorders/functions, not only equal-center tanh. Thus a common monotone real function cannot reverse the two inputs’ weak order. The same selected source gives nonnegative multiplication preservation and negative multiplication reversal, supporting the real product interpretation in the two sign cases (zero difference is immediate). The actual two different shifted channels and concrete strict negative witness remain established by the original exact static source bodies. Original whole node1260 decision, time and direct Mathlib reading remain exact; this is an evidence/declaration supplement only.','scope':'No new proof/compilation, new whole semantic decision or reviewer-time replacement. Checkpoint19 kernel execution is fresh actual0 and checkpoints20/23 explicitly reuse that identical original command/body/time and transitive source hash. Existing selected24 source is unchanged; current24 offers, ledgers and node1260 mapping are not amended.'}
with OUT.open('x')as f:f.write(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'output':ref(OUT),'status':out['status'],'selected_declarations':chosen}))
