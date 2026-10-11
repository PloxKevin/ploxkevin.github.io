from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,sys,difflib
ROOT=Path('/home/oxrexkevin/SafetyBased')
RUNNER=Path('/tmp/root_tmp_lean28_source60_runner_v1.py')
OLD=Path('/tmp/root_tmp_lean28_runner_v4.py')
OUT=Path('/tmp/root-tmp-source60-runner-independent-modules28-v1.json')
SOURCE=Path('/tmp/CompleteModulesSensorCommissioning28-draft-v4.lean')
NEVER=Path('/tmp/root-tmp-source60-preflight-never-written28-v1.json')
assert not OUT.exists() and not NEVER.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(RUNNER)=='f373a291a1f60cb15857935bf0b390adac8614f0d4226f5fc62ea6576a4fd18a'
assert sha(OLD)=='8fe26e9954800b4e104db5a079eb2e9295e3680064fe7ebaaa74b496e60ec49b'
code=RUNNER.read_text(); old=OLD.read_text()
cut='guard();before=sha(source)\n'
assert code.count(cut)==old.count(cut)==1
prefix=code.split(cut)[0]
# The executed prefix defines and tests only real readonly preflight provenance.
assert 'subprocess.run(' not in prefix and 'snapshot.open(' not in prefix and 'log.open(' not in prefix
prefix=compile(prefix,str(RUNNER),'exec')
args=sys.argv[:]
def run_prefix(overrides=None,argv=None):
 ns={'__file__':str(RUNNER),'__name__':'independent_readonly_guard_review'}
 if overrides:
  # Insert a local read wrapper immediately after the actual helper definition.
  text=code.split(cut)[0]
  anchor="def ref(n):return {'file':n,'sha256':sha(ROOT/n)}\n"
  assert text.count(anchor)==1
  injected="original_read=read\ndef read(n):\n    d=original_read(n)\n    if n in READ_OVERRIDES:return copy.deepcopy(READ_OVERRIDES[n])\n    return d\n"
  text=text.replace(anchor,anchor+injected)
  ns.update({'READ_OVERRIDES':overrides,'copy':copy})
  program=compile(text,str(RUNNER),'exec')
 else:program=prefix
 sys.argv=argv or [str(RUNNER),str(SOURCE),str(NEVER)]
 try:exec(program,ns)
 finally:sys.argv=args
 return ns
ns=run_prefix();ns['guard']()
assert len(ns['selection']['proof_files'])==1175 and len(ns['assets'])==31 and len(ns['owners'])==5
assert ns['application']['coverage_complete'] is False
failures=[]
def rejects(label,fn):
 try:fn()
 except (AssertionError,KeyError,TypeError,ValueError):failures.append({'fixture':label,'rejected':True});return
 raise AssertionError('Accepted negative fixture: '+label)
def replace_read(label,path,mutate):
 d=json.loads((ROOT/path).read_bytes());mutate(d)
 rejects(label,lambda:run_prefix({path:d}))
replace_read('historical_source55_audit_cannot_claim_current60_inventory','reports/full-coverage/root-source55-final-owner-integration27-v1.json',lambda d:d.__setitem__('inventory_sha256','6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'))
replace_read('current60_page_set_must_have_all29_exact_keys','book/coverage/inventory.json',lambda d:d['source_sha256'].pop('SafeLearning/lipsdp.html'))
replace_read('application_status_must_be_actual_source60_pending_rebase','reports/full-coverage/source56-60-corrections-application-v1.json',lambda d:d.__setitem__('status','passed'))
replace_read('application_correction_order_is_exact56_to60','reports/full-coverage/source56-60-corrections-application-v1.json',lambda d:d['applications'].reverse())
replace_read('application_last_page_hash_must_equal_realcurrent60','reports/full-coverage/source56-60-corrections-application-v1.json',lambda d:d['applications'][-1]['source_after'].__setitem__('sha256','0'*64))
replace_read('application_selected_sources_count1175','reports/full-coverage/source56-60-corrections-application-v1.json',lambda d:d.__setitem__('selected27_proof_sources_unchanged',1174))
replace_read('application_five_owner_preservation_must_be_true','reports/full-coverage/source56-60-corrections-application-v1.json',lambda d:d.__setitem__('five_installed27_owner_ledgers_unchanged',False))
replace_read('application_never_claims_whole_coverage','reports/full-coverage/source56-60-corrections-application-v1.json',lambda d:d.__setitem__('coverage_complete',True))
replace_read('native_application_bool_true_is_not_exit0','reports/full-coverage/source56-60-corrections-application28-execution-v1.json',lambda d:d.__setitem__('actual_exit_code',True))
replace_read('native_application_wrong_helper_command','reports/full-coverage/source56-60-corrections-application28-execution-v1.json',lambda d:d.__setitem__('actual_command',['python3','wrong.py']))
replace_read('native_application_wrong_workdir','reports/full-coverage/source56-60-corrections-application28-execution-v1.json',lambda d:d.__setitem__('actual_workdir','/tmp'))
replace_read('native_application_changed_log_hash','reports/full-coverage/source56-60-corrections-application28-execution-v1.json',lambda d:d.__setitem__('log_sha256','0'*64))
replace_read('selected27_count_must_stay1175','reports/full-coverage/checkpoint-27-selection.json',lambda d:d.__setitem__('proof_file_count',1174))
replace_read('frozen_audit_retains9644_kernel_declarations','reports/full-coverage/checkpoint-27/reports/lean-verification/verification.json',lambda d:d.__setitem__('theorem_count',9645))
rejects('canonical_source_not_allowed_as_TMP_argument',lambda:run_prefix(argv=[str(RUNNER),str(ROOT/'verification/lean/SafeLearning/Modules.lean'),str(NEVER)]))
rejects('absolute_canonical_path_rejected_by_safe',lambda:ns['safe']('/etc/passwd'))
rejects('parent_traversal_rejected_by_safe',lambda:ns['safe']('book/../coverage/inventory.json'))
for label,key in [('current_inventory_byte_guard','book/coverage/inventory.json'),('current_asset_byte_guard','SafeLearning/lipsdp.html'),('old55_historical_inventory_byte_guard','book/coverage/inventory-after-correction55.json'),('owner27_byte_guard','book/coverage/modules.json'),('selected_proof_byte_guard',next(iter(ns['selection']['proof_files'])))]:
 original=ns['PINNED'].get(key);originalh=ns['held'].get(key)
 if key in ns['held']:ns['held'][key]='0'*64
 else:ns['PINNED'][key]='0'*64
 rejects(label,ns['guard'])
 if original is None:ns['PINNED'].pop(key,None)
 else:ns['PINNED'][key]=original
 if originalh is None:ns['held'].pop(key,None)
 else:ns['held'][key]=originalh
old_runner_before=ns['runner_before'];ns['runner_before']='0'*64
rejects('runner_byte_guard',ns['guard']);ns['runner_before']=old_runner_before
for value in [True,'0',1,None]:rejects('zero_type_rejects_'+repr(value),lambda value=value:ns['zero']({'actual_exit_code':value}))
ns['guard']()
assert all(not x.exists() for x in [NEVER,NEVER.with_suffix('.log'),NEVER.with_name(NEVER.stem+'-source.lean')])
assert sha(RUNNER)=='f373a291a1f60cb15857935bf0b390adac8614f0d4226f5fc62ea6576a4fd18a'
new_runtime=code.split(cut)[1].split("out={")[0]
old_runtime=old.split(cut)[1].split("out={")[0]
assert new_runtime==old_runtime
out={'status':'passed_independent_source60_tmp_runner_full_code_delta_readonly_guards_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_finish28','runner':ref(RUNNER),'original_runner':ref(OLD),'full_code_and_complete_delta_read':True,'readonly_actual_prefix_executed':True,'real_guard_before_after_passed':True,'compiler_launch_or_log_or_snapshot_or_native_lean_record_executed':False,'guard_boundary':cut,'native_prefix_provenance':{'selected27':ref(ROOT/'reports/full-coverage/checkpoint-27-selection.json'),'historical_source55_inventory':ref(ROOT/'book/coverage/inventory-after-correction55.json'),'current60_inventory':ref(ROOT/'book/coverage/inventory.json'),'actual_source56_60_application':ref(ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json'),'actual_source56_60_native':ref(ROOT/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json')},'protected_counts':{'selected27_sources':1175,'current60_assets':31,'unchanged_owner27_ledgers':5,'historical_theorems':9644},'negative_fixtures':failures,'negative_fixture_count':len(failures),'compiler_execution_and_snapshot_logic_identical_to_old_v4':True,'semantic_decisions':['Historical source55 global audit is bound to immutable inventory55 and labeled prior integrity; it does not certify current60 owner identities.','Actual application native command/helper/log/zero exit and correction order56–60 are independently pinned; exactly the four expected pages change, and all29 current HTML plus two other assets are held.','Current60 source application remains explicitly non-whole, and owner27 literal rebase is explicitly pending.','All1175 selected sources, original eight canonical standalone/named native histories, five owner27 ledgers, project/toolchain hashes, fresh8/reused1167 frozen audit provenance and standard axiom whitelist remain held.','Fresh TMP source snapshot/log/native record creation, true compiler return handling and post-compile byte checks are unchanged from previously reviewed v4.'],'closed_evidence_sha256':{r['file']:r['sha256'] for r in [ref(RUNNER),ref(OLD),ref(ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json'),ref(ROOT/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json')]},'canonical_source_owner_selection_PUB_or_publication_mutated':False}
OUT.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(ref(OUT)))
