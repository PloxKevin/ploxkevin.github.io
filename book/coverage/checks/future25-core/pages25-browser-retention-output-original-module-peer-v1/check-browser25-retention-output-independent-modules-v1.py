from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');PUB=R/'reports/book/publication-repo';OUT=Path('/tmp/pages25-browser-retention-independent-modules-output-review-v1.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((R/n).read_text())
def ref(n):return {'file':n,'sha256':h(R/n)}
def zero(d):
 x=[d[k] for k in ('actual_exit_code','exit_code') if k in d];assert x and all(type(v)is int and v==0 for v in x)
assert not OUT.exists();N='reports/full-coverage/browser-checkpoint-25.json';A='reports/full-coverage/retain-browser25-exact24-execution-v1.json';H='book/coverage/checks/root_retain_browser25_exact24_v2.py';P='book/coverage/checks/pages25-browser-retention-helper-independent-modules-review-v1.json';a=read(A);b=read(N);p=read(P);m=read('reports/full-coverage/checkpoint-25-manifest.json')
zero(a);assert a['actual_command']==['python3',H];assert a['helper_sha256_before']==a['helper_sha256_after']=={H:h(R/H)};assert h(R/H)=='9e33b019d0aeb245535f39d15222923190695972a98c9fb70f67d40d9e0908a5';assert h(R/a['log'])==a['log_sha256']
assert p['errors']==[] and 'passed' in p['status'] and p['helper_sha256']==h(R/H)
assert h(R/N)==h(PUB/N);assert b['status']=='passed_actual_exact_retained24_browser_evidence_for_unchanged25_assets' and b['coverage_complete']is False
assert b['page_count']==29 and b['requested_viewport_count']==b['verified_viewport_count']==b['retained_verified_viewport_count']==145 and b['fresh_verified_viewport_count']==0 and b['screenshot_count']==48 and b['skipped_capture_target_count']==10
old=read(b['original_browser_report']['file']);assert h(R/b['original_browser_report']['file'])==b['original_browser_report']['sha256']=='94749a4dfbab2dd12bdcdb213e9d42b8abdb3ff1a682729fa0978c0cd59f8625';assert b['original_browser_report_body']==old
assert b['manifest']==ref('reports/full-coverage/checkpoint-25-manifest.json')
assets={n:v for n,v in m['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert b['source_sha256']==old['source_sha256']==assets and len(assets)==31
for n,v in assets.items():assert h(R/n)==h(PUB/n)==v
assert b['qa_source_sha256']==old['qa_source_sha256'] and len(b['qa_source_sha256'])==2
for n,v in b['qa_source_sha256'].items():assert h(R/n)==h(PUB/n)==v
shots={s['path']:s['sha256'] for q in old['pages'] for s in q['screenshots'] if s['status']=='passed'};assert len(shots)==48 and b['screenshot_files_sha256']==shots
for n,v in shots.items():assert h(R/n)==v
assert sum(s['status']=='skipped' for q in old['pages'] for s in q['screenshots'])==10
# Recheck the actual original execution/raw input. Whole old body/time is equality-bound above.
oa=read(old['actual_execution']);zero(oa);assert h(R/old['actual_execution'])==old['actual_execution_sha256'];assert h(R/oa['log'])==oa['log_sha256'];assert h(R/old['fresh_run_inputs'])==old['fresh_run_inputs_sha256']
body={'status':'passed_independent_actual_browser25_retention_output_review','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'browser_report':ref(N),'actual_retention':ref(A),'actual_retention_raw_log':ref(a['log']),'helper':ref(H),'independent_helper_peer':ref(P),'manifest':b['manifest'],'original_browser_report':b['original_browser_report'],'retained_viewports':145,'fresh_viewports':0,'screenshots':48,'skipped_targets':10,'all31_source_assets_and_two_QA_inputs_exact':True,'entire_original_report_body_and_original_times_unchanged':True,'scope':'Actual retention metadata only. Entire prior browser report is preserved and all current source/QA/screenshot inputs match. No new browser execution, screenshot, visual inspection or delivery outcome is claimed.'}
OUT.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps({'peer':str(OUT),'sha256':h(OUT)}))
