from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
DEST=ROOT/'book/coverage/checks/future29-applied/publication29-four-helper-independent-v3'
FINDINGS=Path('/tmp/checkpoint29-publication-four-helpers-independent-applied-findings-v4.json')
NATIVE=Path('/tmp/checkpoint29-publication-four-helpers-independent-applied-actual-v4.json')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
PREVIOUS=ROOT/'book/coverage/checks/future29-applied/publication29-four-helper-independent-v2/checkpoint29-publication-four-helpers-independent-applied-peer-v2.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return p.relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(p),'sha256':sha(p)}
assert not DEST.exists() and sha(CONTEXT)==CONTEXT_SHA
c=json.loads(CONTEXT.read_bytes());guards={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
def guard():
 assert sha(CONTEXT)==CONTEXT_SHA
 for n,h in guards.items():assert sha(ROOT/n)==h,n
guard()
f=json.loads(FINDINGS.read_bytes());native=json.loads(NATIVE.read_bytes());old=json.loads(PREVIOUS.read_bytes())
assert f['status'].startswith('passed_') and f['errors']==[] and f['case_count']==36
assert native['status']=='passed' and native['actual_exit_code']==native['actual_runner_exit_code']==0
assert native['protection_errors']==[] and native['helper_sha256_before']==native['helper_sha256_after']
assert sha(Path(native['log']))==native['log_sha256']
assert len(f['reviewed_helpers_sha256'])==4
for n,h in f['reviewed_helpers_sha256'].items():assert sha(ROOT/n)==h,n
assert [x['actual_exit_code'] for x in f['original_failed_plan_native_history']]==[1,1]
for n,h in f['original_readonly_history_sha256'].items():assert sha(ROOT/n)==h,n
assert sha(PREVIOUS)=='6e94576a378884eb800297a5c772fad8b856dc63292405f3b65fc91b89ad1ac5'
assert old['errors']==[]
for n,h in old['closed_evidence_sha256'].items():assert sha(ROOT/n)==h,n
paths=[*(ROOT/n for n in f['reviewed_helpers_sha256']),
 Path('/tmp/check-checkpoint29-publication-four-helpers-independent-applied-v4.py'),
 Path('/tmp/run-checkpoint29-publication-four-helpers-independent-applied-v4.py'),
 FINDINGS,NATIVE,Path(native['log']),CONTEXT,
 Path('/tmp/root-publication29-budget-helper-authorship-v1.json'),Path(__file__),
 *(ROOT/n for n in f['original_readonly_history_sha256'])]
DEST.mkdir(parents=True)
catalog={};closed={}
for i,p in enumerate(dict.fromkeys(paths)):
 h=sha(p);target=DEST/'originals'/h/(str(i).zfill(2)+'-'+p.name)
 target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(p.read_bytes());assert sha(target)==h
 r=ref(target);catalog[str(p)]=r;closed[r['file']]=h
alias=DEST/'original-closed-byte-aliases-v1.json'
alias.write_text(json.dumps({'status':'exact_original_byte_aliases_only_no_execution_relabeling',
 'original_to_closed_byte_aliases':catalog},indent=2)+'\n');closed[rel(alias)]=sha(alias)
required={**old['closed_evidence_sha256'],**closed,rel(PREVIOUS):sha(PREVIOUS)}
out={
 'status':'passed_independent_full_checkpoint29_publication_four_helper_code_review',
 'errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'reviewed_helpers_sha256':f['reviewed_helpers_sha256'],
 'reviewed_exact_source_byte_aliases':{n:catalog[str(ROOT/n)] for n in f['reviewed_helpers_sha256']},
 'full_complete_helper_bodies_read':['documents1','supplement_copy2','stage_plan3','stager3'],
 'actual_reader':catalog[str(NATIVE)],'reader_findings':catalog[str(FINDINGS)],
 'original_reader_helper':catalog['/tmp/check-checkpoint29-publication-four-helpers-independent-applied-v4.py'],
 'original_reader_wrapper':catalog['/tmp/run-checkpoint29-publication-four-helpers-independent-applied-v4.py'],
 'actual_checker_exit_code':native['actual_exit_code'],
 'actual_runner_exit_code':native['actual_runner_exit_code'],
 'original_started_at_utc':native['started_at_utc'],
 'original_finished_at_utc':native['finished_at_utc'],
 'original_elapsed_seconds':native['elapsed_seconds'],
 'original_raw_log':catalog[native['log']],
 'focused_case_count':f['case_count'],'focused_cases':f['focused_cases'],
 'actual_current_inputs_guarded':{'selected29_proof_sources':1197,
  'source_pages_and_assets':31,'raw_installed29_owners':5,'protection_errors':[]},
 'code_scope':[
  'Complete unchanged documents1 and copy2 bodies and all complete plan3/stager3 bodies read. Exact1197/10114/218 audit gates, retained1186 prior modules and all31 assets/five raw owners are preserved.',
  'Strict integer exit aliases, equal all-present command/cwd/log aliases and exact helper-before/after maps were tested with explicitly synthetic schemas; wrong/missing/conflicting aliases reject.',
  'The exact four reviewed helper map is required by both plan3 and stager3. New output paths/versioned config2 report/177-backup/nativeapplication2 avoid overwriting old outputs.',
  'Failed original plan natives1/2 [1,1], raw logs and original config1 helper/report/application/backup remain exact readonly history. Their results/times are not converted into successful prerequisites.',
  'Plan3 requires the separate delivery4 peer and exact helper pointer, preserves its entire closed evidence in supplementary paths and records its independent review in the plan. This review does not substitute for that separate full delivery-helper peer.',
  'Actual current site scan uses exactly177 literal exclusions, omits excluded archive files before included symlink checks, and checks prospective/actual included bytes against850MB before writes. An isolated excluded archive-index fixture contributes zero site bytes.',
  'Only exact progress/README overrides are allowed. Source/frozen/PUB hashes, explicit literal Git staging, index object bytes and archived whitespace are checked. No commit or push occurs in these four helpers.'
 ],
 'previous_original_four_helper_peer':ref(PREVIOUS),
 'original_failed_plan_native_history':f['original_failed_plan_native_history'],
 'original_readonly_publication_history_sha256':f['original_readonly_history_sha256'],
 'original_closed_byte_aliases':catalog,'original_alias_catalog':ref(alias),
 'publication_evidence_sha256':required,'closed_evidence_sha256':required,
 'production_prepare_or_stage_executed':False,'producer_invoked_by_reviewer':False,
 'git_invoked_by_reviewer':False,'publication_mutated_by_reviewer':False,
 'actual_new_config2_application_or_plan3_or_stager3_success_claimed':False,
 'actual_kernel_or_content_metadata_delivery_success_claimed':False,
 'production_disposition':'Conditional code/schema approval only. Root must execute real config2 application, plan3 and stager3, then actual content/metadata delivery checks. Original mathematical correspondence decisions and execution times remain unchanged.',
 'coverage_complete':False,
 'scope':'Independent entire four-helper code/native-schema review and36 actual focused pure guard cases. Original native/read-only checker/log/history bytes are archived verbatim under physical Root-relative aliases. No future producer result is invented.'}
guard()
p=DEST/'checkpoint29-publication-four-helpers-independent-applied-peer-v3.json'
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'record':rel(p),'sha256':sha(p),'status':out['status'],
 'actual_checker_exit_code':0,'focused_cases':36,'protection_errors':[]}))
