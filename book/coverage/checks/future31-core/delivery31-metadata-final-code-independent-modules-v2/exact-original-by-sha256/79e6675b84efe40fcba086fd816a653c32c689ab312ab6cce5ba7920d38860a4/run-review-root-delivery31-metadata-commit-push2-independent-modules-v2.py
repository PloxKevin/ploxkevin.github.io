from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');CONTEXT=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json');CONTEXT_SHA='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
HELPER=Path('/tmp/review-root-delivery31-metadata-commit-push2-independent-modules-v2.py');CODE=ROOT/'book/coverage/checks/root_commit_push_delivery31_metadata_v2.py';CODE_SHA='11910d522ccf71de68fc096e910df0cc4c1a0b7e1706a1d5b667f32e0e675fb8'
RECORD=Path('/tmp/modules-delivery31-metadata-commit-push2-independent-code-review-actual-v2.json');LOG=RECORD.with_suffix('.log');REVIEW=Path('/tmp/modules-delivery31-metadata-commit-push2-independent-code-review-v2/delivery31-metadata-commit-push2-full-unexecuted-code-independent-modules-v2.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(CONTEXT)==CONTEXT_SHA and sha(CODE)==CODE_SHA
c=json.loads(CONTEXT.read_bytes());pins={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']};extra={str(p):sha(p) for p in [HELPER,Path(__file__),CONTEXT,CODE,ROOT/'book/coverage/checks/root_commit_push_delivery31_metadata_v1.py',Path('/tmp/modules-delivery31-metadata-commit-push1-independent-code-review-v1/delivery31-metadata-commit-push1-full-unexecuted-code-independent-modules-v1.json'),Path('/tmp/modules-delivery31-metadata-commit-push1-independent-code-review-actual-v1.json'),Path('/tmp/modules-delivery31-metadata-commit-push1-independent-code-review-actual-v1.log'),Path('/tmp/modules-delivery31-metadata-commit-push2-independent-code-review-actual-v1.json'),Path('/tmp/modules-delivery31-metadata-commit-push2-independent-code-review-actual-v1.log'),Path('/tmp/modules-delivery31-metadata-commit-push2-independent-code-review-v1/delivery31-metadata-commit-push2-full-unexecuted-code-independent-modules-v1.json')]}
def guard():
 for n,h in pins.items():
  p=ROOT/n;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p)==h,n
 for n,h in extra.items():assert sha(n)==h,n
assert not RECORD.exists() and not LOG.exists() and not REVIEW.exists()
guard();cmd=['python3',str(HELPER)];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick;errors=[]
try:guard()
except Exception as e:errors.append(str(e))
passed=r.returncode==0 and not errors and REVIEW.is_file()
out={'status':'passed_actual_readonly_full_code_reader_only_findings_pending' if passed else 'failed_actual_readonly_code_reader_or_guard','actual_exit_code':r.returncode,'actual_runner_exit_code':0 if passed else 1,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':elapsed,'actual_current81_installed31_context':ref(CONTEXT),'full_original_reviewed_unexecuted_helper':ref(CODE),'actual_independent_reader':ref(HELPER),'actual_independent_wrapper':ref(Path(__file__)),'raw_log':ref(LOG),'review':ref(REVIEW) if REVIEW.exists() else None,'protected_context_files':len(pins),'protected_selected31_proof_sources':1248,'unchanged_current81_final_css_book_assets':31,'unchanged_installed_source81_raw_owner31_files':5,'all_context_sha256':pins,'all_reader_helper_context_sha256':extra,'protection_errors':errors,'reviewed_producer_helper_import_or_execution':False,'PUB_or_index_or_live_source_owner_canonical_write':False,'code_approved_for_commit_push':False,'actual_content31_Pages_or_all31_live_success_claimed':False,'coverage_complete':False}
with RECORD.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'actual_exit_code':r.returncode,'actual_runner_exit_code':out['actual_runner_exit_code'],'elapsed_seconds':elapsed,'review':out['review'],'native':ref(RECORD),'raw_log':ref(LOG),'protection_errors':errors,'code_approved_for_commit_push':False}))
raise SystemExit(0 if passed else 1)
