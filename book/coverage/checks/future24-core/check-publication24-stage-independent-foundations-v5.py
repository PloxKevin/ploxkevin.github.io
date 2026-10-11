"""Read-only staging-helper code fixtures; never execute its top-level module."""
from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/checks/root_stage_publication24_v3.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
src=HELPER.read_text();tree=ast.parse(src)
# Execute only the pure/read-only safe and actual record-validation functions.
ns={'ROOT':ROOT,'Path':Path,'sha':H,'hashlib':hashlib,'json':json}
functions=[n for n in tree.body if isinstance(n,ast.FunctionDef)]
exec(compile(ast.Module(body=functions,type_ignores=[]),str(HELPER),'exec'),ns)
cases=[]
def case(name,body,reject=False):
 try:body()
 except (AssertionError,KeyError,ValueError,TypeError):assert reject,name;cases.append({'fixture':name,'observed':'rejected'})
 else:assert not reject,name;cases.append({'fixture':name,'observed':'accepted'})
case('canonical_allowed_source_path',lambda:ns['safe']('SafeLearning/primer-basics.html'))
for name in ['/tmp/file','../outside','book/coverage/../../../../etc/passwd','bad\0path','bad\npath','bad\rpath']:
 case('reject_unsafe_path_'+repr(name),lambda name=name:ns['safe'](name),True)
records={};ns['read']=lambda n:records[n]
real_log=ROOT/'book/coverage/checks/future24-core/pages24-config-helper-independent-foundations-actual-v1.log';record={'actual_exit_code':0,'exit_code':0,'log':str(real_log.relative_to(ROOT)),'log_sha256':H(real_log)}
def actual_fixture(edit,exit_code=0):
 r=dict(record);edit(r);records['fixture']=r;return ns['actual']('fixture',exit_code)
case('matching_real_hash_native_zero_aliases',lambda:actual_fixture(lambda r:None))
case('historical_failure_accepted_only_as_failure',lambda:actual_fixture(lambda r:r.update(actual_exit_code=1,exit_code=1),1))
case('failed_record_rejected_from_success_stems',lambda:actual_fixture(lambda r:r.update(actual_exit_code=1,exit_code=1)),True)
case('conflicting_exit_alias_rejected',lambda:actual_fixture(lambda r:r.update(exit_code=1)),True)
case('boolean_exit_rejected',lambda:actual_fixture(lambda r:r.update(actual_exit_code=False)),True)
case('wrong_log_hash_rejected',lambda:actual_fixture(lambda r:r.update(log_sha256='0'*64)),True)
case('missing_exit_codes_rejected',lambda:actual_fixture(lambda r:(r.pop('actual_exit_code'),r.pop('exit_code'))),True)
# Exercise the exact staged path status rules and NUL argument construction.
def parse(entries,allowed):
 changed=set()
 for entry in entries:
  assert entry[:2]not in {'R ',' R','C ',' C'}and 'D'not in entry[:2]
  changed.add(entry[3:])
 assert changed<=allowed
 return changed
allowed={'SafeLearning/primer-basics.html','reports/full-coverage/some report.json'}
case('strict_whitelisted_tracked_and_untracked_status',lambda:parse([' M SafeLearning/primer-basics.html','?? reports/full-coverage/some report.json'],allowed))
case('out_of_whitelist_dirty_path_rejected',lambda:parse(['?? outside'],allowed),True)
case('deleted_path_rejected',lambda:parse([' D SafeLearning/primer-basics.html'],allowed),True)
case('renamed_path_rejected',lambda:parse(['R  SafeLearning/primer-basics.html'],allowed),True)
payload=''.join(n+'\0'for n in sorted(allowed)).encode();assert payload.split(b'\0')[:-1]==[n.encode()for n in sorted(allowed)]
assert "['git','add','--pathspec-from-file=-','--pathspec-file-nul']"in src
assert "input=payload"in src and "check=True"in src
assert "assert {n for n in staged if n}<=paths"in src
first_copy=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.For)and ast.unparse(n.target)=='n'and 'shutil.copyfile'in ast.unparse(n))
assert all('1144'in src and n in src for n in ['9279','38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'])
for text in ["audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}","manifest['successful_verification']['report_sha256']","selection['coverage_complete'] is False","config['excluded_count']==88","config['prospective_included_website_bytes']<850_000_000","assert len(assets)==31","sha(safe(n))==sha(PUB/n)==d","'awaits an actual GitHub Pages build'","'checkpoint24_awaiting_actual_pages_and_live_checks'","set(manifest['frozen_inputs_sha256'])<=paths"]:assert text in src,text
for text in ['source52-dry-execution-v1','source52-corrected-paragraphs24-capture-execution-v1','actual(record,1)','source52-dry-execution-v2','source52-apply-execution-v1','verify-checkpoint24-execution-v1','export-checkpoint24-execution-v1','export-checkpoint24-output-integrity-execution-v1','pages24-config-execution-v2','pages24-config-execution-v1','browser-checkpoint24-binding-execution-v1','stage_peer[\'helper_sha256\']==sha(Path(__file__))','config_peer[\'config_sha256\']==config[\'config_sha256\']','closed_evidence_sha256']:assert text in src,text
assert not any(isinstance(n,ast.Call)and ast.unparse(n.func)=='subprocess.run'and any(x in ast.unparse(n)for x in ['commit','push'])for n in ast.walk(tree))
for i,n in enumerate(tree.body[:first_copy]):
 assert not ('shutil.copyfile'in ast.unparse(n)or '.open(\'x\')'in ast.unparse(n))
assert not (ROOT/'reports/full-coverage/publication24-prestage-v2.json').exists()
old_path=ROOT/'book/coverage/checks/root_stage_publication24_v2.py';old=old_path.read_text()
assert H(HELPER)=='92b4428e569fc6acbd4a1388d1f9d821e7309f056f76ff245d8c1ef0714b7e29'
start=src.index('# Preserve the original unexecuted stage helper')
end=src.index('# Exact old/root source bytes are copied only through the frozen whitelist above.')
delta=src[start:end]
reverse=src
reverse=reverse.replace("config['prospective_included_website_bytes']<850_000_000","config['prospective_included_website_bytes']<900_000_000")
reverse=reverse.replace("config['excluded_count']==88","config['excluded_count']==70")
reverse=reverse.replace("config_code_peer=read('book/coverage/checks/pages24-config-helper-independent-modules-review-v2.json')","config_code_peer=read('book/coverage/checks/pages24-config-helper-independent-foundations-review-v1.json')")
reverse=reverse.replace("assert config_code_peer['helper_sha256']==sha(safe('book/coverage/checks/root_prepare_pages24_config_v2.py'))=='7859f7c25e71a830d9782225d99cdf16bb0472cd4e950f89d7f257a3faf14999'","assert config_code_peer['helper_sha256']==sha(safe('book/coverage/checks/root_prepare_pages24_config_v1.py'))")
reverse=reverse.replace("'publication24-ledger-check-execution-v1','pages24-config-execution-v2'","'publication24-ledger-check-execution-v1','pages24-config-execution-v1'")
for line in ["    'book/coverage/checks/root_stage_publication24_v2.py',\n","    'book/coverage/checks/root_prepare_pages24_config_v2.py',\n","    'book/coverage/checks/pages24-config-helper-independent-modules-review-v2.json',\n"]:reverse=reverse.replace(line,'')
reverse=reverse.replace("'source52-corrected-paragraphs24-capture-execution-v1','pages24-config-execution-v1']","'source52-corrected-paragraphs24-capture-execution-v1']")
reverse=reverse.replace("for n in ['book/coverage/checks/future24-core/publication24-stage-independent-review-v3.json',\n          'book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json',","for n in ['book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json',")
reverse=reverse.replace("stage_peer=read('book/coverage/checks/future24-core/publication24-stage-independent-review-v3.json')","stage_peer=read('book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json')")
for line in ["assert sha(safe('book/coverage/checks/root_stage_publication24_v2.py'))=='ec1f45917e044fa67545f24fcf057f042d62bfa04fd59127ba75ffb683eb7383'\n","assert sha(safe('book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json'))=='6ab0c8e8eec3cabb3232f53673b63a3fe16266923921c94bfaf3b6716e8ae8d2'\n","second_stage_peer=read('book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json')\n","assert second_stage_peer['helper_sha256']==sha(safe('book/coverage/checks/root_stage_publication24_v2.py'))\n"]:reverse=reverse.replace(line,'')
assert reverse==old,'Unrequested original gate changes'
original_peer_path=ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-review-v2.json'
original_peer=json.loads(original_peer_path.read_text());assert H(original_peer_path)=='6ab0c8e8eec3cabb3232f53673b63a3fe16266923921c94bfaf3b6716e8ae8d2'
for p,h in original_peer['closed_evidence_sha256'].items():assert H(ROOT/p)==h
# Execute only the newly added read-only assertion block against actual closed inputs.
def delta_fixture(edit=None):
 def reader(n):
  d=json.loads((ROOT/n).read_text())
  return edit(n,d)if edit else d
 local={'ROOT':ROOT,'Path':Path,'sha':H,'safe':ns['safe'],'read':reader,'extra':set()}
 exec(compile(delta,str(HELPER),'exec'),local)
 return local
case('real_new_closed_selection_peer_and_eight_reader_histories',lambda:delta_fixture())
def altered(path,change):
 return lambda n,d:change(d)if n.endswith(path)else d
case('reject_Root_selection_count_change',lambda:delta_fixture(altered('root-checkpoint24-production-output-independent-confirmation-v1.json',lambda d:{**d,'new_sources':14})),True)
case('reject_Root_peer_nonempty_errors',lambda:delta_fixture(altered('root-checkpoint24-production-output-independent-confirmation-v1.json',lambda d:{**d,'errors':['actual problem']})),True)
case('reject_Root_selected_hash_mismatch',lambda:delta_fixture(altered('root-checkpoint24-production-output-independent-confirmation-v1.json',lambda d:{**d,'selection':{'sha256':'0'*64}})),True)
case('reject_Module_export_count_change',lambda:delta_fixture(altered('modules-checkpoint24-production-output-independent-confirmation-v1.json',lambda d:{**d,'public_theorem_or_lemma_exports':0})),True)
case('reject_Module_plan_closure_hash_change',lambda:delta_fixture(altered('modules-checkpoint24-production-output-independent-confirmation-v1.json',lambda d:{**d,'actual_plan_closure_execution':{'sha256':'0'*64}})),True)
case('reject_archival_catalog_duplicate_path',lambda:delta_fixture(altered('modules-checkpoint24-production-output-original-byte-aliases-v1.json',lambda d:{**d,'original_absolute_path_byte_aliases':[d['original_absolute_path_byte_aliases'][0]]*8})),True)
case('reject_original_reader_failure_relabelled_success',lambda:delta_fixture(altered('modules-checkpoint24-production-output-independent-actual-v1.json',lambda d:{**d,'actual_exit_code':0})),True)
case('reject_corrected_reader_boolean_exit',lambda:delta_fixture(altered('modules-checkpoint24-production-output-independent-actual-v2.json',lambda d:{**d,'actual_exit_code':False})),True)
case('reject_corrected_reader_raw_log_hash_change',lambda:delta_fixture(altered('modules-checkpoint24-production-output-independent-actual-v2.json',lambda d:{**d,'raw_log_sha256':'0'*64})),True)
# The replacement config code approval is real; prospective config objects below
# are explicitly synthetic and exercise only the new config preflight assertions.
config_name='book/coverage/checks/pages24-config-helper-independent-modules-review-v2.json'
code_peer_path=ROOT/config_name
code_peer_present=code_peer_path.exists()
code=json.loads(code_peer_path.read_text()) if code_peer_present else {'status':'explicit_synthetic_fixture_passed','errors':[],'helper_sha256':'7859f7c25e71a830d9782225d99cdf16bb0472cd4e950f89d7f257a3faf14999','fixture_only':True}
assert 'passed' in code['status'] and code.get('errors',[])==[]
assert code['helper_sha256']==H(ROOT/'book/coverage/checks/root_prepare_pages24_config_v2.py')=='7859f7c25e71a830d9782225d99cdf16bb0472cd4e950f89d7f257a3faf14999'
config_block=src[src.index("config=read('reports/full-coverage/pages24-config-preparation-v1.json')"):src.index("ledger_name='reports/full-coverage/publication-checks/ledger-checkpoint-24.json'")]
base_config={'config_sha256':'a'*64,'prospective_included_website_bytes':849999999,'excluded_count':88}
def config_fixture(config_edit=None,code_edit=None):
 cfg=dict(base_config);peer=dict(code)
 if config_edit:config_edit(cfg)
 if code_edit:code_edit(peer)
 def reader(n):return cfg if n.endswith('pages24-config-preparation-v1.json')else peer
 def digest(p):return 'a'*64 if str(p).endswith('/_config.yml')else H(p)
 local={'ROOT':ROOT,'PUB':ROOT/'reports/book/publication-repo','sha':digest,'safe':ns['safe'],'read':reader}
 exec(compile(config_block,str(HELPER),'exec'),local)
case('synthetic_replacement88_config_below850M',lambda:config_fixture())
case('reject_budget_at850M',lambda:config_fixture(lambda d:d.update(prospective_included_website_bytes=850000000)),True)
case('reject_old70_exclusions',lambda:config_fixture(lambda d:d.update(excluded_count=70)),True)
case('reject_replacement_config_byte_hash_mismatch',lambda:config_fixture(lambda d:d.update(config_sha256='b'*64)),True)
case('reject_replacement_code_peer_error',lambda:config_fixture(code_edit=lambda d:d.update(errors=['guard issue'])),True)
case('reject_wrong_replacement_helper_digest',lambda:config_fixture(code_edit=lambda d:d.update(helper_sha256='0'*64)),True)
# Check exact success/failure phase membership and the genuinely closed original
# failed config wrapper. The replacement production wrapper must still pass at run.
stems_node=next(n for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='stems'for t in n.targets))
assert 'pages24-config-execution-v2' in ast.literal_eval(stems_node.value) and 'pages24-config-execution-v1' not in ast.literal_eval(stems_node.value)
failure_loop=next(n for n in tree.body if isinstance(n,ast.For)and isinstance(n.iter,ast.List)and 'pages24-config-execution-v1' in ast.literal_eval(n.iter))
assert 'actual(record, 1)' in ast.unparse(failure_loop)
failed_config_path=ROOT/'reports/full-coverage/pages24-config-execution-v1.json'
failed_config=json.loads(failed_config_path.read_text())
assert type(failed_config['actual_exit_code'])is int and failed_config['actual_exit_code']==1
assert H(ROOT/failed_config['log'])==failed_config['log_sha256']
assert "REPORT='reports/full-coverage/publication24-prestage-v2.json'" in src
assert "reports/full-coverage/pages24-config-preparation-v1.json" in src and "reports/full-coverage/pages24-config-previous-original-v1.yml" in src
obs={'status':'independent_publication24_stage_helper_code_and_focused_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','helper':ref(HELPER),'helper_sha256':H(HELPER),'checker':ref(Path(__file__)),'original_stage_v2_code_peer':ref(original_peer_path),'entire_original_stage_v2_peer_body_and_time':original_peer,'original_helper_v2':ref(old_path),'replacement_config_code_peer':ref(code_peer_path) if code_peer_present else {'file':config_name,'scope':'Future production requirement; explicitly synthetic code-peer object was used for isolated assertion fixtures only.'},'replacement_config_code_peer_present_at_review':code_peer_present,'genuine_original_config_v1_failure':ref(failed_config_path),'entire_original_config_v1_failure_body_and_time':failed_config,'new_delta_preserves_all_previous_gates_exact':True,'fixture_count':len(cases),'fixtures':cases,'full_read_scope':['future actual1144-source9279-export kernel/standard-axiom report byte bindings','exact frozen/prepared whitelist and snapshot bytes with only explicit mutable progress','actual31current source52 HTML assets and frozen publication owner validation','truthful awaiting-Pages progress/README guard','success and genuine failure execution stems retain native exits and rawlogs','explicit closed peer/evidence catalogs with exact code/config identity','no broad stage; strict dirty subset and NUL Git add; no commit/push','exclusive new report, original immutable inputs and future25 active-proof exclusion'],'scope':'Code-only author-independent approval. Only isolated read-only functions and explicitly synthetic dictionary/status fixtures were executed. No future audit/config/preparation/output was assumed present or approved; production assertions remain required at actual staging. No preparer/main, PUB copy, Git add/commit/push, live source, owner, inventory or selected-proof mutation occurred.'}
obs['preserved_prior_reader_failure']={'reason':'The first independent reader required the future canonical replacement-config Module code peer before it was published. No Root helper defect or execution; new reader labels isolated synthetic peer/config dictionaries explicitly, while production still requires the real approval.','actual_record':ref(ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-foundations-actual-v4.json'),'entire_original_actual_record_and_time':json.loads((ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-foundations-actual-v4.json').read_text()),'raw_log':ref(ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-foundations-actual-v4.log'),'checker':ref(ROOT/'book/coverage/checks/future24-core/check-publication24-stage-independent-foundations-v4.py'),'runner':ref(ROOT/'book/coverage/checks/future24-core/run-publication24-stage-independent-foundations-v4.py')}
out=ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-observations-v5.json' 
with out.open('x')as f:f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':obs['status'],'observations':ref(out),'fixture_count':len(cases)}))
