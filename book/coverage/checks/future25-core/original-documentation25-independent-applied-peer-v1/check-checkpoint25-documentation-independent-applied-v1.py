from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, json, subprocess, tempfile

ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/checks/root_prepare_checkpoint25_documentation_v1.py'
PIN='a9d6db82c57fb3a31c994fe9afba891f47c0f940ab44d999b47124c27d586fcd'
OUT=Path('/tmp/checkpoint25-documentation-helper-independent-applied-review-v1.json')
assert not OUT.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=(ROOT/HELPER).read_text();assert H(ROOT/HELPER)==PIN
ast.parse(source)
assert source.index("manifest['successful_verification']")<source.index("with safe(backup).open('xb')")
assert source.index("for r in integration['exact_replacements']")<source.index("with safe(backup).open('xb')")
original_progress=json.loads((ROOT/'book/coverage/progress.json').read_text())
original_readme=(ROOT/'reports/full-coverage/README.md').read_bytes()
inventory_bytes=(ROOT/'book/coverage/inventory.json').read_bytes()
assert H(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
real_browser=json.loads((ROOT/'reports/full-coverage/browser-checkpoint-24.json').read_text())
assert real_browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
assets=real_browser['source_sha256'];assert len(assets)==31
for n,h in {**assets,**real_browser['qa_source_sha256']}.items():assert H(ROOT/n)==h,n

def fixture(name,mutate=None,counts=(514,19,23,4500,8274)):
 with tempfile.TemporaryDirectory(prefix='documentation25-independent-'+name+'-') as tmp:
  base=Path(tmp)
  def bytes_(n,b):
   p=base/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return H(p)
  def write(n,d):return bytes_(n,(json.dumps(d,indent=2)+'\n').encode())
  def read(n):return json.loads((base/n).read_text())
  bytes_(HELPER,source.encode())
  ih=bytes_('book/coverage/inventory.json',inventory_bytes)
  bytes_('book/coverage/inventory-after-correction52.json',inventory_bytes)
  for n in {**assets,**real_browser['qa_source_sha256']}:bytes_(n,(ROOT/n).read_bytes())
  proofs={f'fixture-source-{i}.lean':{'sha256':hashlib.sha256(str(i).encode()).hexdigest()} for i in range(1156)}
  bn='book/coverage/checks/fixture-content-binding25.json'
  bh=write(bn,{'original_input_count':40485,'new_unique_snapshot_alias_count':123,'fixture_only':True})
  sel={'proof_files':proofs,'previous_frozen_input_content_binding':{'file':bn,'sha256':bh},'fixture_only':True}
  sh=write('reports/full-coverage/checkpoint-25-selection.json',sel)
  checks=[{'exit_code':0,'evidence_mode':'fresh_kernel_replay'} for _ in range(12)]+[
   {'exit_code':0,'evidence_mode':'reused_identical_module_and_transitive_local_imports'} for _ in range(1144)]
  checks.append({'exit_code':0,'command':['lake','env','lean',str(base/'reports/full-coverage/checkpoint-25/verification/lean/AxiomAudit.lean')]})
  audit={'status':'passed','proof_file_count':1156,'theorem_count':9369,'checks':checks,
   'proof_sha256':{n:r['sha256'] for n,r in proofs.items()},'lean_version':'Lean (version 4.34.1, synthetic fixture)',
   'mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','declarations':[str(i) for i in range(9369)],
   'axiom_dependencies':{str(i):['propext','Classical.choice','Quot.sound'] for i in range(9369)},
   'allowed_standard_axioms':['propext','Classical.choice','Quot.sound'],'fixture_only':True}
  ah=write('reports/full-coverage/lean-checkpoint-25/verification-original.json',audit)
  write('reports/full-coverage/checkpoint-25-manifest.json',{'status':'formal_verification_passed_partial_coverage',
   'selection_sha256':sh,'proof_files':proofs,'frozen_inputs_sha256':assets,
   'successful_verification':{'report_sha256':ah},'fixture_only':True})
  write('reports/full-coverage/checkpoint-24-manifest.json',{'frozen_inputs_sha256':assets,'fixture_only':True})
  c,p,n,r,u=counts
  write('reports/full-coverage/lean-checkpoint-25/ledger-audit.json',{'integrity_status':'passed','errors':[],
   'mathematical_coverage_complete':False,'inventory_sha256':ih,'counts':{'exercises':556,'material_source_units':12774,
   'statuses':{'exercise:complete_math':c,'exercise:partial':p,'exercise:pending':n},
   'material_review_statuses':{'reviewed':r,'pending':u}},'fixture_only':True})
  write('reports/full-coverage/integration-25.json',{'status':'PASS','errors':[],
   'counts':{'html_pages':29,'all_current_exercises':556},'fixture_only':True})
  write('reports/full-coverage/browser-checkpoint-24.json',real_browser)
  for stem in ['verify-checkpoint25-execution-v1','export-checkpoint25-execution-v1',
               'frozen-ledger-checkpoint25-execution-v1','static-checkpoint25-execution-v1']:
   log='reports/full-coverage/'+stem+'.log';lh=bytes_(log,b'Synthetic schema fixture; not a genuine Lean or audit run.\n')
   write('reports/full-coverage/'+stem+'.json',{'actual_exit_code':0,'log':log,'log_sha256':lh,'fixture_only':True})
  candidate='book/coverage/checks/fixture-owner25-candidate.json';dh=write(candidate,{'fixture_only':True})
  bytes_('book/coverage/core.json',(base/candidate).read_bytes())
  helper='book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py'
  hh=bytes_(helper,b'# Explicit synthetic schema fixture only.\n')
  write('reports/full-coverage/owner25-reviewed-candidate-integration-v1.json',{'applied':True,
   'status':'four_exact_reviewed_owner25_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate25_audit',
   'all40485_frozen24_inputs_exact':True,'all1144_selected24_root_source_hashes_exact':True,
   'authorized_current_future_code_updates':{helper:{'fixture_only':True}},
   'authorized_current_future_code_update_reference_sha256':{helper:hh},
   'exact_replacements':[{'destination':'book/coverage/core.json','candidate':{'file':candidate,'sha256':dh}}],
   'fixture_only':True})
  progress=copy.deepcopy(original_progress);progress['fixture_preserved_user_metadata']={'sentinel':[1,{'nested':True}]}
  write('book/coverage/progress.json',progress);bytes_('reports/full-coverage/README.md',original_readme)
  original_bytes=(base/'book/coverage/progress.json').read_bytes()
  if mutate:mutate(base,read,write)
  result=subprocess.run(['python3',HELPER],cwd=base,capture_output=True,text=True)
  outputs=['reports/full-coverage/progress-checkpoint25-preparation-update-v1.json',
   'reports/full-coverage/progress-checkpoint25-before-preparation-original-v1.json',
   'reports/full-coverage/README-checkpoint25-before-preparation-original-v1.md']
  if mutate:
   assert result.returncode!=0,(name,result.stdout)
   assert not any((base/x).exists() for x in outputs),(name,result.stderr)
   assert (base/'book/coverage/progress.json').read_bytes()==original_bytes
   assert (base/'reports/full-coverage/README.md').read_bytes()==original_readme
  else:
   assert result.returncode==0,result.stderr
   assert (base/outputs[1]).read_bytes()==original_bytes
   assert (base/outputs[2]).read_bytes()==original_readme
   updated=read('book/coverage/progress.json')
   allowed={'inventory_sha256','inventory_counts','verified_checkpoint','current_frozen_audit','publication_status',
    'live_delivery_status','live_delivery_evidence','current_documented_material_corrections','working_coverage_report',
    'current_published_ledger_candidate','previous_checkpoint24_delivery','working_next_checkpoint_preparation'}
   assert {k for k in updated if updated[k]!=progress.get(k)}<=allowed
   for k,v in progress.items():
    if k not in allowed:assert updated[k]==v,k
   assert updated['previous_checkpoint24_delivery']['live_evidence']==progress['live_delivery_evidence']
   assert updated['previous_checkpoint24_delivery']['content_commit']==progress['last_published_content_commit']
   assert updated['live_delivery_evidence'] is None and 'awaiting' in updated['live_delivery_status']
   text=(base/'reports/full-coverage/README.md').read_text()
   for required in [f'{c} of 556',f'{p} partial and {n} pending',f'{r:,} are reviewed',f'{u:,} remain pending',
    'not a new browser run or a new Pages deployment','whole answer(c) and neural-network exercise remain unfinished',
    'awaits an actual GitHub Pages build','12 additions received fresh kernel replays']:
    assert required in text,required
  return {'case':name,'synthetic_schema_only':True,'process_exit_code':result.returncode,'passed':True,
   'expected':'reject_before_backups_or_metadata_writes' if mutate else 'prepare_partial_coverage_and_pending_delivery_preserving_exact_originals'}

def mutate(name,key,value):
 def change(b,r,w):d=r(name);d[key]=value;w(name,d)
 return change
audit='reports/full-coverage/lean-checkpoint-25/verification-original.json'
cases=[fixture('accepted_dynamic_actual_schema_counts'),fixture('accepted_alternative_dynamic_counts',counts=(500,20,36,4300,8474))]
for name,file,key,value in [
 ('failed_audit',audit,'status','failed'),('wrong_Lean',audit,'lean_version','Lean (version 0.0.0, fixture)'),
 ('wrong_mathlib',audit,'mathlib_revision','bad'),('unapproved_axiom',audit,'allowed_standard_axioms',['propext','unsafe']),
 ('failed_static','reports/full-coverage/integration-25.json','status','FAIL'),
 ('coverage_complete_not_partial','reports/full-coverage/lean-checkpoint-25/ledger-audit.json','mathematical_coverage_complete',True),
 ('failed_wrapper','reports/full-coverage/verify-checkpoint25-execution-v1.json','actual_exit_code',1),
 ('boolean_wrapper','reports/full-coverage/export-checkpoint25-execution-v1.json','actual_exit_code',False),
 ('conflicting_wrapper','reports/full-coverage/frozen-ledger-checkpoint25-execution-v1.json','exit_code',1),
 ('browser_count_drift','reports/full-coverage/browser-checkpoint-24.json','verified_viewport_count',144),
 ('wrong_previous_count','book/coverage/checks/fixture-content-binding25.json','original_input_count',40484),
 ('integration_not_applied','reports/full-coverage/owner25-reviewed-candidate-integration-v1.json','applied',False)]:
 cases.append(fixture(name,mutate(file,key,value)))
cases.append(fixture('site_asset_drift',lambda b,r,w:(b/'SafeLearning/lyapunov-mpc.html').write_bytes(b'fixture drift')))
cases.append(fixture('actual_raw_log_drift',lambda b,r,w:(b/'reports/full-coverage/static-checkpoint25-execution-v1.log').write_bytes(b'fixture drift')))
cases.append(fixture('candidate_copy_drift',lambda b,r,w:(b/'book/coverage/core.json').write_bytes(b'fixture drift')))
cases.append(fixture('audit_boolean_exit',lambda b,r,w:(lambda d:(d['checks'][0].update(exit_code=False),w(audit,d)))(r(audit))))
assert H(ROOT/HELPER)==PIN
for n,h in {**assets,**real_browser['qa_source_sha256']}.items():assert H(ROOT/n)==h,n
report={'status':'passed_independent_documentation25_code_and_isolated_fixtures','errors':[],
 'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helper':{'file':HELPER,'sha256':PIN},'helper_sha256':PIN,'fixture_count':len(cases),'fixture_cases':cases,
 'read_scope':'Complete code and dynamic README/progress updates; actual unchanged31 Source52 assets and retained browser24 report/QA hashes; native audit/manifest/frozen-ledger/integration/strict-zero prerequisites before backups and metadata writes.',
 'preservation_scope':'Both positive isolated fixtures preserve exact previous progress and README backups, all unrelated fields, original24 delivery evidence and content commit. Counts come from the supplied future native frozen-ledger schema; delivery25 remains explicitly pending.',
 'execution_scope':'Genuine independent Python reader and isolated explicitly synthetic schema subprocesses only. Production documentation helper remains unexecuted here; no actual25 audit, PUB copy, Git stage, Pages or live delivery result is asserted.',
 'retained_browser_scope':'145 existing checks including5 prior fresh+140 prior retained;48 screenshots/10 skipped. Site and QA bytes match; this is not a fresh browser25 run.',
 'actual_checker':{'file':str(Path(__file__)),'sha256':H(Path(__file__))}}
OUT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':str(OUT),'sha256':H(OUT),'fixture_count':len(cases),'status':report['status']}))
