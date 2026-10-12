from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, ast

R=Path('/home/oxrexkevin/SafetyBased')
H=Path('/tmp/checkpoint29-publication-helpers-v1/root_prepare_checkpoint29_documents_v1.py')
O=Path('/tmp/checkpoint29-documents-full-independent-modules-peer-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):
    return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
assert not O.exists()
assert sha(H)=='849fae0db6feacdaa10576a4b6efafea1dc8532a748b1d290c29cbcd6821f308'
s=H.read_text(); ast.parse(s)
assert 'actual_overflow_container_count\'] == 4' in s
assert "progress['live_delivery_evidence'] = None" in s
assert '526 of 556 exercises are complete, 11 partial' in s
assert '4,663 are reviewed and' in s and '8,111 pending' in s
assert 'all four overflowing containers' in s
assert '20 fresh viewport' in s and '125 exact retained checks' in s
assert '1197' in s and '10114' in s
assert "'propext', 'Classical.choice', 'Quot.sound'" in s
assert '1,186 earlier modules retained successful replays after exact source' in s
assert 'transitive import and dependency fingerprints matched' in s
assert "with safe(ROOT, backup).open('xb')" in s
assert 'whole-page visual coverage is not claimed' in s
assert 'Checkpoint 29 is prepared; its push, actual Pages workflow and live hashes' in s
refs={}
for name in ['reports/full-coverage/root-source65-final-owner-integration29-v1.json','reports/full-coverage/browser-checkpoint-29.json','reports/full-coverage/source65-four-page-math-scroll29-v2.json','reports/full-coverage/source65-four-page-math-scroll29-execution-v2.json','book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json','book/coverage/progress.json','reports/full-coverage/README.md']:
    refs[name]=sha(R/name)
g=json.loads((R/'reports/full-coverage/root-source65-final-owner-integration29-v1.json').read_bytes())
assert g['integrity_status']=='passed' and g['errors']==[] and g['mathematical_coverage_complete'] is False
assert g['counts']['material_review_statuses']=={'reviewed':4663,'pending':8111}
assert {k:g['counts']['statuses'][k]for k in ['exercise:complete_math','exercise:partial','exercise:pending']}=={'exercise:complete_math':526,'exercise:partial':11,'exercise:pending':19}
b=json.loads((R/'reports/full-coverage/browser-checkpoint-29.json').read_bytes())
assert b['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
assert (b['page_count'],b['verified_viewport_count'],b['fresh_verified_viewport_count'],b['retained_verified_viewport_count'])==(29,145,20,125)
assert (b['screenshot_count'],b['skipped_capture_target_count'])==(48,10)
v=b['manual_visual_inspection'];assert (v['fresh_actual_captures'],v['retained_exact_capture_count'])==(8,40)and v['whole_page_visual_approval']is False
scroll=json.loads((R/'reports/full-coverage/source65-four-page-math-scroll29-v2.json').read_bytes());assert scroll['status']=='passed'and scroll['errors']==[]and scroll['actual_overflow_container_count']==4
n=json.loads((R/'reports/full-coverage/source65-four-page-math-scroll29-execution-v2.json').read_bytes())
assert n['actual_exit_code']==0 and n['status']=='passed'and n['actual_command']==['node','book/coverage/checks/root_check_math_scroll29_v2.mjs']and n['actual_workdir']==str(R)
assert n['helper_sha256_before']==n['helper_sha256_after']=={n['actual_command'][1]:sha(R/n['actual_command'][1])}
assert sha(R/n['log'])==n['log_sha256']
c=json.loads((R/'book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json').read_bytes());assert c['status']=='passed_actual_checkpoint28_content_and_metadata_delivery'
assert c['content_commit']=='c3245229f722a678927d2f95fd756286a100598d'and c['metadata_commit']=='fa1e92e55ea0b8fac9ba30ef2b0450b5e5281702'
for name,h in c['exact_native_evidence_sha256'].items():assert sha(R/name)==h
out={
 'status':'passed_independent_checkpoint29_documents_full_code_native_schema_and_factual_review','errors':[],
 'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),
 'full_helper_and_all_output_text_read':True,'production_document_helper_or_readiness_invoked':False,'synthetic_fixtures_run':False,
 'actual_future29_frozen_lean_audit_assumed_passed':False,
 'findings':[
  'The readiness guard binds genuine current65 inventory/corrections, selected1197 exact source hashes and10114 distinct theorem/axiom keys, exactly11 fresh kernel replays and1186 unchanged/transitive-import reuse, and the three permitted standard axioms.',
  'Literal native aliases require every supplied code/command/cwd alias to agree. Actual current four-container wheel receipt uses the expected node command, helper-before/after map and raw log hash. Future verification/export/static/frozen-ledger receipts remain mandatory prerequisites, not reviewed executions.',
  'Current global counts526complete/11partial/19pending and4663reviewed/8111pending are guarded and reflected in the full output README/progress text. Complete28 content and metadata delivery is retained through exact native hashes and whole original-document backups.',
  'Browser claims preserve20fresh+125retained/48captured8fresh40retained/10skipped scope; four wheel containers reached both ends. Static captured-region reviews and all original times remain distinct from whole-page visual approval.',
  'All prior documents are authenticated before fresh exclusive-create byte backups. Only progress and README change; selected proofs, five owners and current31 assets are held. New29 publication and live evidence stay explicitly pending/None.'
 ],
 'actual_current_factual_inputs_sha256':refs,'producer_execution_approval_scope':'Code review only; Root must satisfy every real future29 prerequisite before execution.',
 'coverage_complete':False,'actual_finalizer':None
}
O.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'peer':ref(O),'status':out['status'],'errors':[]}))
