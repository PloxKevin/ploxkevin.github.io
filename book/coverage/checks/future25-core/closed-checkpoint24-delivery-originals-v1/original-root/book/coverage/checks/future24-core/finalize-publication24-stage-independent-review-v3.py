"""Close genuine checker5 output and exact publisher failure without rerunning helpers."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[4];BASE=Path(__file__).parent
OUT=BASE/'publication24-stage-independent-review-v3.json'
FAIL=BASE/'publication24-stage-independent-wrapper-v5-report-write-failure-observation-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def read(p):return json.loads(p.read_text())
assert not OUT.exists() and not FAIL.exists()
obs=BASE/'publication24-stage-independent-observations-v5.json'
a=BASE/'publication24-stage-independent-foundations-actual-v5.json'
actual=read(a);review=read(obs)
assert actual['actual_exit_code']==0 and review['fixture_count']==34 and review['errors']==[]
assert actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']==sha(BASE/'check-publication24-stage-independent-foundations-v5.py')
assert sha(ROOT/actual['raw_log'])==actual['raw_log_sha256']
old=BASE/'publication24-stage-independent-review-v2.json'
assert sha(old)=='6ab0c8e8eec3cabb3232f53673b63a3fe16266923921c94bfaf3b6716e8ae8d2'
failure={'status':'observed_independent_wrapper_report_write_failure_after_actual_checker0',
         'observed_at_utc':datetime.now(timezone.utc).isoformat(),'observed_outer_wrapper_exit_code':1,
         'command':['python3','book/coverage/checks/future24-core/run-publication24-stage-independent-foundations-v5.py'],
         'workdir':str(ROOT),'source':'Actual tools.exec_command result from this independent review turn; this is a copied stderr observation, not a fabricated PTY raw log or a second compiler record.',
         'exact_reported_stderr':'Traceback (most recent call last):\n  File "/home/oxrexkevin/SafetyBased/book/coverage/checks/future24-core/run-publication24-stage-independent-foundations-v5.py", line 18, in <module>\n    with out.open(\'x\')as f:f.write(json.dumps(review,ensure_ascii=False,indent=2)+\'\\n\')\n         ^^^^^^^^^^^^^\n  File "/home/oxrexkevin/.local/oss-cad-suite/lib/python3.11/pathlib.py", line 1044, in open\n    return io.open(self, mode, buffering, encoding, errors, newline)\n           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\nFileExistsError: [Errno 17] File exists: \'/home/oxrexkevin/SafetyBased/book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json\'\n',
         'independent_checker_passed_record':ref(a),'original_v2_peer_remained_exact':ref(old),
         'reason':'The independent checker succeeded. The reused outer publisher still pointed to the prior exclusive v2 peer and stopped without overwriting it. This new finalizer binds the actual checker5 body/time rather than repeating or relabelling that run.'}
with FAIL.open('x') as f:json.dump(failure,f,indent=2);f.write('\n')
review['status']='independent_publication24_stage_v3_helper_code_and_focused_fixtures_passed'
review['original_observations']=ref(obs);review['actual_independent_code_checker_execution']=ref(a)
review['preserved_original_wrapper_report_write_failure']=ref(FAIL)
review['finalization_scope']='The genuine independent checker5 EXIT0/34 fixtures supplies code validation. Reader4 absence failure and wrapper5 exclusive-target failure remain unchanged. This finalizer only publishes a new v3 peer; no Root helper, Git, Pages, PUB, selected source or live metadata execution.'
closed={}
for version in [1,2,3,4,5]:
    for name in [f'check-publication24-stage-independent-foundations-v{version}.py',f'run-publication24-stage-independent-foundations-v{version}.py',
                 f'publication24-stage-independent-foundations-actual-v{version}.json',f'publication24-stage-independent-foundations-actual-v{version}.log',
                 f'publication24-stage-independent-observations-v{version}.json']:
        p=BASE/name
        if p.exists():closed[p.relative_to(ROOT).as_posix()]=sha(p)
for p in [BASE/'publication24-stage-independent-review-v1.json',old,FAIL,Path(__file__)]:closed[p.relative_to(ROOT).as_posix()]=sha(p)
review['closed_evidence_sha256']=closed
assert review['helper_sha256']=='92b4428e569fc6acbd4a1388d1f9d821e7309f056f76ff245d8c1ef0714b7e29'
assert sha(ROOT/review['helper']['file'])==review['helper_sha256']
with OUT.open('x') as f:json.dump(review,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'status':'passed','peer':ref(OUT),'actual_checker_exit_code':0,'fixture_count':34}))
