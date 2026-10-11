from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,shutil
R=Path('/home/oxrexkevin/SafetyBased');F=R/'reports/full-coverage';O=Path('/tmp/publication28-supplementary-plan-modules-v1');O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selection_path=F/'checkpoint-28-selection.json';selection=json.loads(selection_path.read_text());selection_bytes=selection_path.read_bytes();extras=set(selection['extra_frozen_inputs'])
auto_suffix={'.py','.json','.md','.log','.html','.lean','.js'}
def automatic(n):
 return n in extras or (n.startswith('book/coverage/') and Path(n).suffix in auto_suffix and '__pycache__' not in n) or n.startswith('SafeLearning/') or n in {'qa/learning_review.mjs','qa/book_browser_checks.mjs'}
groups={}; auto={}; warnings=[]
def add(group,n,expected=None):
 p=R/n
 assert p.is_file(),n
 assert p.resolve().is_relative_to(R.resolve()),n
 digest=sha(p)
 if expected is not None:assert digest==expected,(n,digest,expected)
 row={'file':n,'sha256':digest,'bytes':p.stat().st_size}
 if automatic(n):auto[n]=row;return
 groups.setdefault(group,{})[n]=row

def files(group,patterns):
 for pattern in patterns:
  for p in sorted(F.glob(pattern)):
   if p.is_file():add(group,str(p.relative_to(R)))
files('source56_60_application_and_native_readiness',['source56-60-corrections-application-v1.json','source56-60-corrections-application28-execution-v1.*','source56-60-readiness28-execution-v*.json','source56-60-readiness28-execution-v*.log','source56-60-contract-preparation28-execution-v1.*'])
history=F/'source-history/approved-corrections56-60-20261011';h=json.loads((history/'preserved-history-v1.json').read_text())
for p in sorted(history.rglob('*')):
 if p.is_file():add('source56_60_exact_original_correction_history',str(p.relative_to(R)))
# Exact original root and absolute alias routes are verified without recursively adding auto-frozen ledgers.
for v in list(h['original_root_files'].values())+list(h['original_absolute_byte_aliases'].values()):
 add('source56_60_exact_original_correction_history',v['file'],v['sha256'])
files('source60_static_native_failures_and_pass',['integration28-source60-static-execution-v*.json','integration28-source60-static-execution-v*.log','integration-28-source60-static-v*.json','prepare-static-validator28-execution-v1.*'])
files('source60_math_scroll_native_failures_and_pass',['source60-math-scroll28-execution-v*.json','source60-math-scroll28-execution-v*.log','source60-four-page-math-scroll28-v*.json'])
for i in (1,2,3):add('source60_scroll_helpers_mjs_missing_freeze_suffix',f'book/coverage/checks/root_check_math_scroll28_v{i}.mjs')
files('fresh20_browser_original_inner_outer_and_merge',['browser-source60-28-v1.json','browser-source60-28-v1-execution.*','browser-source60-28-v1-inputs.json','browser28-source60-helper-execution-v1.*','browser28-evidence-merge-execution-v1.*','source60-eight-captured-regions-manual-review28-v1.json'])
for p in sorted((F/'browser-input28-source60/SafeLearning').glob('*')):
 if p.is_file():add('fresh20_browser_exact31_site_command_inputs',str(p.relative_to(R)))
merged_inputs=json.loads((F/'browser-corrections-28-inputs.json').read_text())
for x in merged_inputs['screenshot_aliases']:
 original=x['original'];add('fresh20_eight_original_pngs' if '/browser-artifacts-source60-28-v1/' in original else 'retained40_original_pngs_for_original_report_links',original,x['sha256'])
 for n in [x['file']]:assert sha(R/n)==x['sha256']
files('retained125_browser_original_reports_and_native',['browser-checkpoint-27.json','browser-corrections-27-inputs.json','browser-checkpoint-26.json','browser-source55-27-v1.json','browser-source55-27-v1-execution.*','source55-four-captured-regions-manual-review27-v1.json'])
files('current60_canonical_sources_actual_outer_receipts',['current60-canonical-pairs28-execution-v1.*','current60-canonical-pairs28-readiness-execution-v*.json','current60-canonical-pairs28-readiness-execution-v*.log','current60-commissioning17-canonical-pair28-execution-v1.*','prepare-current60-canonical-plan28-execution-v1.*','prepare-current60-commissioning17-canonical28-execution-v1.*','prepare-source60-tmp-runner28-execution-v1.*'])
files('actual_owner28_install_global_and_true_failed_preflights',['owner28-binding-preflight-execution-v*.json','owner28-binding-preflight-execution-v*.log','owner28-candidate-integrity-diagnostic-execution-v1.*','owner28-isolated-candidate-integrity-diagnostic-v1.json','owner28-reviewed-candidate-integration-execution-v1.*','owner28-reviewed-candidate-integration-v1.json','prepare-owner28-binding-execution-v*.json','prepare-owner28-binding-execution-v*.log','root-source60-final-owner-integration28-execution-v1.*','root-source60-final-owner-integration28-v1.json','close-preintegration28-originals-execution-v1.*'])
closure_path='book/coverage/checks/future27-core/completed27-content-and-metadata-delivery-closure-v1.json';add('completed27_actual_delivery_bounded_provenance',closure_path);c=json.loads((R/closure_path).read_text());mutable={};old_snapshot_copies=[]
for n,digest in c['exact_original_evidence_sha256'].items():
 if n in {'book/coverage/progress.json','reports/full-coverage/README.md'}:
  assert sha(R/n)==digest,(n,'old completed27 bytes already changed')
  filename='progress-checkpoint28-before-preparation-original-v1.json' if n.endswith('progress.json') else 'README-checkpoint28-before-preparation-original-v1.md'
  tmp=O/filename;shutil.copyfile(R/n,tmp);assert sha(tmp)==digest
  dest='reports/full-coverage/'+filename
  old_snapshot_copies.append({'original_file':n,'sha256':digest,'bytes':tmp.stat().st_size,'temporary_exact_byte_copy':str(tmp),'proposed_immutable_root_destination':dest,'reason':'Completed27 closure pins these old bytes; current progress/README will describe28. Preserve an immutable alias before mutating them.'})
 else:add('completed27_actual_delivery_bounded_provenance',n,digest)
files('completed27_actual_delivery_bounded_provenance',['close-completed27-delivery-execution-v1.*','publication27-delivery-metadata-staged-completion-v1.json','publication27-staged-byte-and-archival-whitespace-completion-v1.json','progress-checkpoint27-delivery-update-v1.json'])
# Helper and real native records are retained byte-exact, with failures still labelled by their original records.
allrows={n:row for group in groups.values() for n,row in group.items()}
for n,row in allrows.items():assert sha(R/n)==row['sha256']
assert selection_path.read_bytes()==selection_bytes,'Selection changed during plan construction'
plan={'status':'explicit_read_only_supplementary_publication28_path_plan_no_pub_copy_no_freeze_mutation','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author_scope':'Only TMP plan and two exact old27 mutable-original byte copies written. No book/coverage, PUB, owner, selection or production source writes.','selection':{'file':str(selection_path.relative_to(R)),'sha256':sha(selection_path),'proof_file_count':selection['proof_file_count'],'new_file_count':selection['new_file_count']},'publication_helper':{'file':'book/coverage/prepare_publication.py','sha256':sha(R/'book/coverage/prepare_publication.py')},'freeze_helper':{'file':'book/coverage/freeze_checkpoint28_v1.py','sha256':sha(R/'book/coverage/freeze_checkpoint28_v1.py')},'automatic_publication_scope':'Frozen manifest inputs; README/integration28/selection28/manifest28/ledger28/browser28/corrections28, direct lean-checkpoint28 files, and all48 browser-artifacts-28 PNG aliases. Supplement paths below are outside current28 selection extras and theoretical auto freeze bookcoverage/site/QA rules.','supplementary_rootpaths_sha256':{n:r['sha256'] for n,r in sorted(allrows.items())},'groups':[{ 'group':g,'file_count':len(rows),'bytes':sum(r['bytes'] for r in rows.values()),'files':[rows[n] for n in sorted(rows)]} for g,rows in groups.items()],'totals':{'unique_supplementary_files':len(allrows),'supplementary_bytes':sum(x['bytes'] for x in allrows.values()),'automatic_references_checked_not_duplicated':len(auto)},'automatic_references_checked_not_duplicated':[auto[n] for n in sorted(auto)],'immutable_old27_progress_readme_aliases_needed':old_snapshot_copies,'review_scope_limits':['Source60 manual8 capture review retains its original horizontal-scroll false observation and crop limits; genuine scroll3 separately demonstrates wheel motion in eight overflow containers.','Fresh20 plus125 exact retained browser checks are145 checks; eight new original PNGs plus40 retained original PNGs have all48 existing current aliases.','Root must append actual28 freeze/audit/preparation/publication/deployment native records once they exist; this plan does not predict pass receipts.','Old27 manifest/selection and old26 Lean audit may remain Git archives; this plan adds compact original completed27 real Git/Pages/live/failure evidence without old frozen audit/worktree expansion.','Three scroll .mjs helpers do not match the auto-frozen .py/.json/.md/.log/.html/.lean/.js suffix list; publish them explicitly.','No recursive embedding of source history. Source56–60 group is an explicit finite physical path list with hashes; its old owner-ledger aliases are already auto-frozen and omitted from supplementary copies.'],'warnings':warnings,'coverage_complete':False}
out=O/'publication28-supplementary-rootpath-plan-modules-v1.json';out.write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'file':str(out),'sha256':sha(out),'bytes':out.stat().st_size,'totals':plan['totals'],'groups':[{k:g[k]for k in ('group','file_count','bytes')}for g in plan['groups']],'mutable_old27_copies':old_snapshot_copies},indent=2))
