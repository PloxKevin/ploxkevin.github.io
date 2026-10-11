from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, json, subprocess, tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/checks/root_prepare_checkpoint24_documentation_v2.py'
PIN='5be2f720eaa9797d66aeb495af76d862c162dee41ba397a068f3f161f0a9bd69'
OUT=Path('/tmp/checkpoint24-documentation-helper-independent-applied-review-v2.json')
assert not OUT.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=(ROOT/HELPER).read_text();assert sha(ROOT/HELPER)==PIN
old=(ROOT/'book/coverage/checks/root_prepare_checkpoint24_documentation_v1.py').read_text()
tree,old_tree=ast.parse(source),ast.parse(old)
def assignment(t,key):
 return next(n for n in t.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id==key for x in n.targets))
assert ast.dump(assignment(tree,'text'),include_attributes=False)==ast.dump(assignment(old_tree,'text'),include_attributes=False)
assert source.index('binding=read(selection') < source.index("with (ROOT/backup).open('xb')")
assert source.index("manifest['successful_verification']") < source.index("with (ROOT/backup).open('xb')")
progress_original=json.loads((ROOT/'book/coverage/progress.json').read_text())
readme_original=(ROOT/'reports/full-coverage/README.md').read_bytes()
guard_names=['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json','reports/full-coverage/README.md','book/coverage/progress.json']
before={n:sha(ROOT/n) for n in guard_names}
actual_manual_name='book/coverage/checks/future24-core/root24-corrected-NN-paragraphs-manual-visual-inspection-v1.json'
actual_manual=json.loads((ROOT/actual_manual_name).read_text())
for n,h in actual_manual['images_sha256'].items():assert sha(ROOT/n)==h
for n,h in actual_manual['actual_capture_evidence'].items():assert sha(ROOT/n)==h
actual_static=json.loads((ROOT/'reports/full-coverage/integration-24.json').read_text())
actual_browser=json.loads((ROOT/'reports/full-coverage/browser-checkpoint-24.json').read_text())
assert actual_static['status']=='PASS' and actual_static['errors']==[]
assert (actual_browser['verified_viewport_count'],actual_browser['fresh_verified_viewport_count'],actual_browser['retained_verified_viewport_count'])==(145,5,140)

def fixture(name,mutate=None):
 with tempfile.TemporaryDirectory(prefix='documentation24-independent-'+name+'-') as tmp:
  base=Path(tmp)
  def write(n,b):
   p=base/n;p.parent.mkdir(parents=True,exist_ok=True)
   p.write_text(json.dumps(b,indent=2)+'\n');return sha(p)
  def bytes_(n,b):
   p=base/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return sha(p)
  def read(n):return json.loads((base/n).read_text())
  bytes_(HELPER,source.encode())
  inv={'counts':{'exercises':556,'material_source_units':12774},'fixture_only':True}
  invhash=write('book/coverage/inventory.json',inv)
  write('book/coverage/inventory-after-correction52.json',inv)
  proofs={f'fixture-source-{i}.lean':{'sha256':hashlib.sha256(str(i).encode()).hexdigest()} for i in range(1144)}
  binding_name='book/coverage/checks/fixture-content-binding24.json'
  binding_hash=write(binding_name,{'original_input_count':36910,'new_unique_snapshot_alias_count':123,'fixture_only':True})
  selection={'proof_files':proofs,'previous_frozen_input_content_binding':{'file':binding_name,'sha256':binding_hash},'fixture_only':True}
  selection_hash=write('reports/full-coverage/checkpoint-24-selection.json',selection)
  checks=[{'exit_code':0,'evidence_mode':'fresh_kernel_replay'} for _ in range(13)]+[{'exit_code':0,'evidence_mode':'reused_identical_module_and_transitive_local_imports'} for _ in range(1131)]
  checks.append({'exit_code':0,'command':['lake','env','lean',str(base/'reports/full-coverage/checkpoint-24/verification/lean/AxiomAudit.lean')]})
  audit={'status':'passed','proof_file_count':1144,'theorem_count':9279,'checks':checks,
   'proof_sha256':{n:r['sha256'] for n,r in proofs.items()},'lean_version':'Lean (version 4.34.1, synthetic fixture)',
   'mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','declarations':[str(i) for i in range(9279)],
   'axiom_dependencies':{str(i):['propext','Classical.choice','Quot.sound'] for i in range(9279)},
   'allowed_standard_axioms':['propext','Classical.choice','Quot.sound'],'fixture_only':True}
  audit_hash=write('reports/full-coverage/lean-checkpoint-24/verification-original.json',audit)
  manifest={'status':'formal_verification_passed_partial_coverage','selection_sha256':selection_hash,'proof_files':proofs,
   'frozen_inputs_sha256':{'fixture-input':hashlib.sha256(b'fixture').hexdigest()},
   'successful_verification':{'report_sha256':audit_hash},'fixture_only':True}
  write('reports/full-coverage/checkpoint-24-manifest.json',manifest)
  ledger={'integrity_status':'passed','errors':[],'mathematical_coverage_complete':False,'inventory_sha256':invhash,
   'counts':{'exercises':556,'material_source_units':12774,'statuses':{'exercise:complete_math':430,'exercise:partial':40,'exercise:pending':86},
   'material_review_statuses':{'reviewed':5000,'pending':7774}},'fixture_only':True}
  write('reports/full-coverage/lean-checkpoint-24/ledger-audit.json',ledger)
  write('reports/full-coverage/integration-24.json',{'status':'PASS','errors':[],'counts':{'html_pages':29,'all_current_exercises':556},'fixture_only':True})
  write('reports/full-coverage/browser-checkpoint-24.json',{'status':'passed_actual_changed_pages_and_exact_unchanged_evidence','verified_viewport_count':145,'fresh_verified_viewport_count':5,'retained_verified_viewport_count':140,'screenshot_count':48,'skipped_capture_target_count':10,'fixture_only':True})
  nn_hash=bytes_('SafeLearning/nn-in-the-loop.html',b'isolated fixture source only')
  image_map={f'reports/full-coverage/fixture-{i}.png':bytes_(f'reports/full-coverage/fixture-{i}.png',f'not a real image {i}'.encode()) for i in range(4)}
  captured=write('reports/full-coverage/fixture-capture.json',{'fixture_only':True})
  write(actual_manual_name,{'status':'manual_inspection_completed_for_four_actual_corrected_NN_paragraph_captures','images_sha256':image_map,
   'actual_capture_evidence':{'reports/full-coverage/fixture-capture.json':captured},'source_sha256':{'SafeLearning/nn-in-the-loop.html':nn_hash},'fixture_only':True})
  for stem in ['verify-checkpoint24-execution-v1','export-checkpoint24-execution-v1','frozen-ledger-checkpoint24-execution-v1','static-checkpoint24-execution-v1','browser-source52-24-runner-execution-v1','browser-checkpoint24-binding-execution-v1','source52-corrected-paragraphs24-capture-execution-v2']:
   log='reports/full-coverage/'+stem+'.log'
   log_hash=bytes_(log,b'synthetic schema fixture, no actual audit or build')
   write('reports/full-coverage/'+stem+'.json',{'actual_exit_code':0,'log':log,'log_sha256':log_hash,'fixture_only':True})
  original=copy.deepcopy(progress_original)
  original['fixture_preserved_user_metadata']={'sentinel':['unchanged',{'nested':True}]}
  write('book/coverage/progress.json',original)
  bytes_('reports/full-coverage/README.md',readme_original)
  original_progress=(base/'book/coverage/progress.json').read_bytes()
  if mutate:mutate(base,read,write)
  result=subprocess.run(['python3',HELPER],cwd=base,capture_output=True,text=True)
  report='reports/full-coverage/progress-checkpoint24-preparation-update-v1.json'
  backup='reports/full-coverage/progress-checkpoint24-before-preparation-original-v1.json'
  backup_readme='reports/full-coverage/README-checkpoint24-before-preparation-original-v1.md'
  if mutate:
   assert result.returncode!=0,(name,result.stdout)
   assert not any((base/n).exists() for n in [report,backup,backup_readme]),(name,result.stderr)
   assert (base/'book/coverage/progress.json').read_bytes()==original_progress
   assert (base/'reports/full-coverage/README.md').read_bytes()==readme_original
  else:
   assert result.returncode==0,result.stderr
   assert (base/backup).read_bytes()==original_progress
   assert (base/backup_readme).read_bytes()==readme_original
   changed=read('book/coverage/progress.json')
   allowed={'inventory_sha256','inventory_counts','verified_checkpoint','current_frozen_audit','publication_status','live_delivery_status','live_delivery_evidence','current_documented_material_corrections','working_coverage_report','current_published_ledger_candidate','previous_checkpoint23_delivery','working_next_checkpoint_preparation'}
   assert {k for k in changed if changed[k]!=original.get(k)}<=allowed
   for k,v in original.items():
    if k not in allowed:assert changed[k]==v,k
   assert changed['previous_checkpoint23_delivery']['live_evidence']==original['live_delivery_evidence']
   assert changed['previous_checkpoint23_delivery']['content_commit']==original['last_published_content_commit']
   assert changed['live_delivery_evidence'] is None and 'awaiting' in changed['live_delivery_status']
   text=(base/'reports/full-coverage/README.md').read_text()
   for required in ['430 of 556','40 partial and 86 pending','5,000 are reviewed','7,774 remain pending','Temporal multiplier assumptions','full neural-network exercise remain unfinished','Gaussian-mixture worked example remains only partly reviewed','awaits an actual GitHub Pages build','Isolated future25 work adds no coverage']:
    assert required in text,required
  return {'case':name,'synthetic_schema_only':True,'expected':'reject_before_backups_or_owner_writes' if mutate else 'preserve_originals_and_prepare_explicitly_pending_delivery','observed_process_exit_code':result.returncode,'passed':True}

def change_file(name,key,value):
 def change(base,read,write):
  body=read(name);body[key]=value;write(name,body)
 return change
cases=[fixture('accepted_qualified_synthetic_schema')]
cases.append(fixture('missing_content_binding',lambda b,r,w:(b/'book/coverage/checks/fixture-content-binding24.json').unlink()))
cases.append(fixture('failed_actual_audit_wrapper',change_file('reports/full-coverage/verify-checkpoint24-execution-v1.json','actual_exit_code',1)))
cases.append(fixture('wrong_lean_version',change_file('reports/full-coverage/lean-checkpoint-24/verification-original.json','lean_version','Lean (version 0.0.0, fixture)')))
cases.append(fixture('bad_axiom_dependency',change_file('reports/full-coverage/lean-checkpoint-24/verification-original.json','allowed_standard_axioms',['propext','unsafe'])) )
cases.append(fixture('static_failed',change_file('reports/full-coverage/integration-24.json','status','FAIL')))
cases.append(fixture('browser_count_drift',change_file('reports/full-coverage/browser-checkpoint-24.json','verified_viewport_count',144)))
cases.append(fixture('manual_image_hash_drift',lambda b,r,w:(b/'reports/full-coverage/fixture-0.png').write_bytes(b'changed fixture')))
cases.append(fixture('manifest_proof_map_drift',change_file('reports/full-coverage/checkpoint-24-manifest.json','proof_files',{})))
cases.append(fixture('bad_content_binding_hash',lambda b,r,w:w('book/coverage/checks/fixture-content-binding24.json',{'original_input_count':36909,'new_unique_snapshot_alias_count':123})))
for n,h in before.items():assert sha(ROOT/n)==h,n
assert sha(ROOT/HELPER)==PIN
old_review=Path('/tmp/checkpoint24-documentation-helper-independent-applied-review-v1.json')
out={'status':'independent_documentation_helper_code_and_isolated_fixture_review_passed','errors':[],
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','helper_sha256':PIN,
 'helper':{'file':HELPER,'sha256':PIN},'original_unexecuted_helper':{'file':'book/coverage/checks/root_prepare_checkpoint24_documentation_v1.py','sha256':sha(ROOT/'book/coverage/checks/root_prepare_checkpoint24_documentation_v1.py')},
 'original_requires_changes_review':{'file':str(old_review),'sha256':sha(old_review)},'entire_original_requires_changes_review_body_and_time':json.loads(old_review.read_text()),
 'fixture_cases':cases,'fixture_count':len(cases),
 'preflight_scope':'All new factual native audit/Lean/axiom/selection/manifest/static/browser/manual/wrapper prerequisites are checked before metadata backups or writes. README wording AST is exactly the original unexecuted v1. Real existing bounded manual/static/browser records were also read; their bytes were not changed.',
 'preservation_scope':'Isolated accepted fixture preserves exact original progress/README bytes and every unrelated progress field, retains original23 content/live evidence, derives actual-schema partial counts and leaves24 delivery pending. Nine reject fixtures stop before any backups/progress/README writes.',
 'execution_scope':'Actual independent Python checker and synthetic schema subprocess tests in temporary directories only. Synthetic audit data is explicitly fixture_only and supplies no actual Lean verification, frozen audit24, metadata production execution, PUBcopy/stage/Pages/live result. Root must run the unchanged helper only after every actual prerequisite has passed.',
 'held_root_metadata_sha256_before_and_after':before,'coverage_complete':False}
OUT.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'review':str(OUT),'sha256':sha(OUT),'fixture_count':len(cases),'status':out['status']}))
