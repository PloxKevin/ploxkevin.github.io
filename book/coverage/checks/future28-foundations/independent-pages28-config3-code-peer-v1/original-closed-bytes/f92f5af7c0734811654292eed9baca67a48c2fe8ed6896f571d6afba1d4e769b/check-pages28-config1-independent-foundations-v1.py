from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');S=R/'book/coverage/checks/root_prepare_pages28_config_v1.py';OUT=Path('/tmp/pages28-config1-independent-foundations-findings-v1.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':h(p)}
assert h(S)=='2a9223c9cfe3a1b070eca81810501e32a945e8e00b7d41c8f32bfe00b94ebbed'and not OUT.exists()
start=datetime.now(timezone.utc).isoformat();spec=importlib.util.spec_from_file_location('pages28_unexecuted1_guard_review',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);tree=ast.parse(S.read_text());obs=[]
def test(needle):
 rows=[x.test for x in ast.walk(tree)if isinstance(x,ast.Assert)and needle in ast.unparse(x.test)];assert len(rows)==1,(needle,len(rows));return compile(ast.Expression(rows[0]),'<exact-pages28-v1-local-assert>','eval')
audit=j(R/'reports/full-coverage/lean-checkpoint-27/verification-original.json');bad=copy.deepcopy(audit);bad['checks'][0]['actual_exit_code']=1
assert eval(test("type(c['exit_code'])"),{'audit':bad})is True
obs.append({'fixture':'actual1178_baseline_native_checks_conflicting_present_actual_exit_code','v1_local_guard_accepted':True,'required_result':'reject'})
bad=copy.deepcopy(audit);bad['checks'][0]['exit_code']=False;assert eval(test("type(c['exit_code'])"),{'audit':bad})is False;obs.append({'fixture':'boolean_false_direct_exit_code','rejected':True})
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
base=j(R/'reports/full-coverage/checkpoint-27-selection.json');r1=j(R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json');r2=j(R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json')
paths=list(base['proof_files'])+[x['canonical_source']for x in r1['sources']+r2['sources']];names=[d['name']for n in paths for d in declarations((R/n).read_text())if d['kind']in ('theorem','lemma')];assert len(names)==len(set(names))==9896
fake={'status':'passed','theorem_count':9896,'declarations':names,'axiom_dependencies':{n:[]for n in names}}
fake['axiom_dependencies'].pop(names[0]);fake['axiom_dependencies']['Unrelated.FixtureDeclaration']=[]
assert eval(test("len(audit['declarations'])"),{'audit':fake})is True
obs.append({'fixture':'exact9896_actual_source_name_fixture_with_same_count_wrong_axiom_key','v1_local_guard_accepted':True,'required_result':'reject','scope':'Isolated table-count assertion; no fabricated production audit claimed.'})
browser=j(R/'reports/full-coverage/browser-checkpoint-28.json');bad=dict(browser,status='failed')
assert eval(test("browser['verified_viewport_count']"),{'browser':bad})is True
obs.append({'fixture':'actual_browser28_failed_status_same145_20_125_48_counts','v1_local_guard_accepted':True,'required_result':'reject'})
scroll=j(R/'reports/full-coverage/source60-four-page-math-scroll28-v3.json');bad=copy.deepcopy(scroll);bad['source_sha256']={n:'0'*64 for n in bad['source_sha256']}
assert eval(test("scroll['status']"),{'scroll':bad})is True
obs.append({'fixture':'actual_scroll28_wrong_four_source_hashes_same_passed_empty_errors_eight_containers','v1_local_guard_accepted':True,'required_result':'reject'})
ledger=j(R/'reports/full-coverage/lean-checkpoint-27/ledger-audit.json');bad=dict(ledger,errors=['fixture contradiction'],inventory_sha256='0'*64)
assert eval(test("ledger-audit.json"),{'read':lambda root,name:bad,'PUB':Path('/tmp/isolated-pages-ledger')})is True
obs.append({'fixture':'actual_ledger_passed_status_with_errors_wrong_inventory','v1_local_guard_accepted':True,'required_result':'reject'})
included=next(x.value for x in ast.walk(tree)if isinstance(x,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='included'for t in x.targets));code=compile(ast.Expression(included),'<exact-pages28-v1-tree-budget-comprehension>','eval')
with tempfile.TemporaryDirectory(prefix='pages28-native-guard-fixtures-')as td:
 ctx=Path(td);pub=ctx/'pub';pub.mkdir();outside=ctx/'outside';outside.write_bytes(b'0123456789');(pub/'plain').write_bytes(b'abcde');(pub/'included-file-link').symlink_to(outside)
 count=eval(code,{'PUB':pub,'kept':m.kept,'exclusions':set()});assert count==15
 obs.append({'fixture':'included_file_symlink_budget_follows_outside_bytes','v1_local_guard_accepted':True,'required_result':'reject','counted_bytes':count})
 (pub/'included-file-link').unlink();(pub/'included-dir-link').symlink_to(ctx,target_is_directory=True)
 count=eval(code,{'PUB':pub,'kept':m.kept,'exclusions':set()});assert count==5
 obs.append({'fixture':'included_directory_symlink_budget_silently_ignored','v1_local_guard_accepted':True,'required_result':'reject'})
 # Exact native reader function is called only with isolated synthetic JSON.
 oldroot=m.ROOT;m.ROOT=ctx;log=ctx/'log';log.write_bytes(b'exact fixture log');cmd=['python3','fixture-helper.py'];native={'status':'passed','actual_exit_code':0,'actual_command':cmd,'actual_workdir':str(ctx),'log':'log','log_sha256':h(log),'helper_sha256_before':{'fixture-helper.py':'0'*64},'helper_sha256_after':{'fixture-helper.py':'1'*64}}
 record=ctx/'actual.json';record.write_text(json.dumps(native));assert m.actual('actual.json',cmd)==native
 obs.append({'fixture':'actual_function_changed_helper_before_after_maps','v1_local_guard_accepted':True,'required_result':'reject'})
 native['raw_log']='conflicting-log';native['raw_log_sha256']='2'*64;record.write_text(json.dumps(native));assert m.actual('actual.json',cmd)==native
 obs.append({'fixture':'actual_function_conflicting_present_raw_log_aliases','v1_local_guard_accepted':True,'required_result':'reject'})
 m.ROOT=oldroot
assert len(m.ADDITIONS)==20 and len({n for n in m.ADDITIONS if n.startswith('book/coverage/inventory-')})==10
assert m.kept('archive-sibling/file',{'archive'})and not m.kept('archive/file',{'archive'})and not m.kept('archive',{'archive'})
obs.append({'fixture':'literal_exclusion_exact_path_and_descendant_only','passed':True})
for n in ['/tmp/absolute','../escape','folder*','folder?','folder[0]','folder\nname']:
 try:m.safe(R,n)
 except (AssertionError,ValueError):obs.append({'fixture':'unsafe_literal_path_'+repr(n),'rejected':True})
 else:raise AssertionError(n)
assert 'successful_verification'not in S.read_text()
findings=[{'id':'all_present_native_audit_exit_aliases','repair':'Require all present exit_code/actual_exit_code/actual_runner_exit_code exact native integer0 in audit checks; command/directory/status aliases consistent where present.'},{'id':'included_symlink_budget_tree','repair':'Iterate every tree entry, skipping .git and literal excluded paths first; reject included symlink files/directories before is_file.'},{'id':'native_audit_manifest_table_binding','repair':'Bind manifest.successful_verification exact audit path/SHA/counts/all_check_exit_codes int0; require unique declarations and exact axiom-dependency key equality.'},{'id':'execution_helpers_and_log_aliases','repair':'Require command helper before/after exact unchanged current hash map; all present log/raw_log and digest aliases agree before validating the bytes.'},{'id':'frozen_ledger_actual_integrity','repair':'Check passed plus errors[], current inventory60 and mathematical_coverage_complete false on the hosted frozen ledger audit.'},{'id':'browser_native_and_screenshot_binding','repair':'Check browser status/page29/request145; bind binput actual execution to real current node command0/source31 beforeafter/QA2/report+rawlog hashes and all48 unique screenshot alias path/hash bindings.'},{'id':'scroll_source_binding','repair':'Bind actual scroll source_sha256 to the exact four current60 HTML hashes as well as passed/errors[]/eight containers.'}]
out={'status':'completed_full_pages28_config1_code_review_rejected_pending_concrete_native_guard_repairs','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(S),'full_source_lines_read':len(S.read_text().splitlines()),'fixture_count':len(obs),'fixture_observations':obs,'findings':findings,'actual_current28_manifest_frozen_audit_publication_prerequisites_available':False,'production_prepare_or_writer_executed':False,'actual_complete_production_budget_preflight_executed':False,'production_approval':False,'scope':'Full code/native schema review and independent isolated exact assert/function/tree fixtures. Actual browser28/current scroll/native27 fixture schemas read; synthetic tables/records are fixture-only. Complete real current28 freeze/audit/publication preflight remains unavailable and is not fabricated.'}
with OUT.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'fixture_count':len(obs),'production_approval':False}))
