from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');S=R/'book/coverage/checks/root_prepare_pages28_config_v3.py';OUT=Path('/tmp/pages28-config3-independent-foundations-findings-v1.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':h(p)}
assert h(S)=='600aeed827ce65754500fd4b8905979083e6216bd611fb69be6dabea36e0c1b5'and not OUT.exists()
start=datetime.now(timezone.utc).isoformat();spec=importlib.util.spec_from_file_location('pages28_unexecuted2_guard_review',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);tree=ast.parse(S.read_text());obs=[]
def rejected(label,fn):
 try:fn()
 except (AssertionError,KeyError,ValueError):obs.append({'fixture':label,'rejected':True})
 else:raise AssertionError('Guard accepted '+label)
def passed(label,fn):fn();obs.append({'fixture':label,'passed':True})
def test(needle):
 rows=[x.test for x in ast.walk(tree)if isinstance(x,ast.Assert)and needle in ast.unparse(x.test)];assert len(rows)==1,(needle,len(rows));return compile(ast.Expression(rows[0]),'<exact-pages28-v2-local-assert>','eval')
def guarded(label,code,env):rejected(label,lambda:exec('assert eval(code,env)',{'code':code,'env':env}))
audit=j(R/'reports/full-coverage/lean-checkpoint-27/verification-original.json')
passed('all1178_genuine_baseline_native_code_and_alias_checks_preserve_historical_cwds',lambda:[m.audit_native(c)for c in audit['checks']])
for key in ['exit_code','actual_exit_code','actual_runner_exit_code']:
 for value in [1,False,'0',None]:
  c={'exit_code':0};c[key]=value;rejected('native_audit_'+key+'_'+repr(value),lambda c=c:m.zero(c))
rejected('missing_native_exit_codes',lambda:m.zero({}))
fresh_original=next(c for c in audit['checks']if c.get('evidence_mode')=='fresh_kernel_replay')
for key,value in [('actual_command',['false']),('working_directory','/tmp/conflicting-fixture-cwd'),('cwd','/tmp/conflicting-fixture-cwd'),('workdir','/tmp/conflicting-fixture-cwd'),('status','failed'),('command','not-a-native-command-list')]:
 c=copy.deepcopy(fresh_original);c[key]=value;rejected('actual_baseline_present_'+key+'_conflict',lambda c=c:m.audit_native(c))
c={'exit_code':0};rejected('native_audit_missing_required_command',lambda:m.audit_native(c))
for key in ['actual_workdir','working_directory','workdir','cwd']:
 c=copy.deepcopy(fresh_original);c[key]=False;rejected('native_audit_nonstring_'+key,lambda c=c:m.audit_native(c))
c=copy.deepcopy(fresh_original);c['actual_command']=c['command'];c['cwd']=c['actual_workdir'];m.audit_native(c);obs.append({'fixture':'native_audit_consistent_present_aliases_preserve_exact_historical_cwd','passed':True})
# Verify the complete delta is exactly SELF, the new audit alias function and its caller.
old=(R/'book/coverage/checks/root_prepare_pages28_config_v2.py').read_text()
new=S.read_text();oldtree=ast.parse(old);newtree=ast.parse(new)
oldnodes=[n for n in oldtree.body if not(isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='SELF'for t in n.targets))]
newnodes=[n for n in newtree.body if not(isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='SELF'for t in n.targets))and not(isinstance(n,ast.FunctionDef)and n.name=='audit_native')]
assert ast.dump(ast.parse(ast.unparse(ast.Module(oldnodes,type_ignores=[]))))==ast.dump(ast.parse(ast.unparse(ast.Module(newnodes,type_ignores=[])).replace('audit_native(c)','zero(c)')))
obs.append({'fixture':'exact_full_v3_delta_only_self_audit_alias_function_and_call','passed':True})
# Native unique-name/keyset assertion, with actual baseline tables and independent source-index fixtures.
names=[d['name']for d in audit['declarations']];guard=test('set(names)');assert eval(guard,{'names':names,'audit':audit})
passed('genuine9644_native_names_unique_and_axiom_keys_equal',lambda:None)
bad=copy.deepcopy(audit);bad['axiom_dependencies'].pop(names[0]);bad['axiom_dependencies']['Fixture.Unrelated']=[]
guarded('same_count_wrong_native_axiom_key',guard,{'names':names,'audit':bad})
guarded('duplicate_native_declaration_name',guard,{'names':names+[names[0]],'audit':audit})
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
base=j(R/'reports/full-coverage/checkpoint-27-selection.json');r1=j(R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json');r2=j(R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json')
paths=list(base['proof_files'])+[x['canonical_source']for x in r1['sources']+r2['sources']];source_names=[d['name']for n in paths for d in declarations((R/n).read_text())if d['kind']in ('theorem','lemma')];assert len(source_names)==len(set(source_names))==9896
fake={'status':'passed','theorem_count':9896,'declarations':[{'name':n}for n in source_names],'axiom_dependencies':{n:[]for n in source_names}}
assert eval(guard,{'names':source_names,'audit':fake});fake['axiom_dependencies'].pop(source_names[0]);fake['axiom_dependencies']['Fixture.Unrelated']=[]
guarded('9896_source_index_fixture_wrong_axiom_key',guard,{'names':source_names,'audit':fake})
# Manifest native success code assertion is tested explicitly with synthetic local count fixtures.
success_code=test("type(success['all_check_exit_codes'])")
for key,value in [('all_check_exit_codes',False),('all_check_exit_codes',1),('all_check_exit_codes','0'),('proof_file_count',1185),('theorem_count',9895)]:
 fake={'proof_file_count':1186,'theorem_count':9896,'all_check_exit_codes':0};fake[key]=value;guarded('isolated_manifest_success_'+key+'_'+repr(value),success_code,{'success':fake})
ledger=j(R/'reports/full-coverage/lean-checkpoint-27/ledger-audit.json');manifest=j(R/'reports/full-coverage/checkpoint-27-manifest.json');ledger_code=test("ledger['integrity_status']")
assert eval(ledger_code,{'ledger':ledger})
for key,value in [('errors',['fixture error']),('integrity_status','failed'),('mathematical_coverage_complete',True)]:
 bad=dict(ledger);bad[key]=value;guarded('native_ledger_'+key,ledger_code,{'ledger':bad})
inv_code=test("ledger['inventory_sha256']");required=manifest['frozen_inputs_sha256'];assert eval(inv_code,{'ledger':ledger,'required':required})
bad=dict(ledger,inventory_sha256='0'*64);guarded('native_ledger_wrong_inventory_hash',inv_code,{'ledger':bad,'required':required})
domain_code=test("d['ledger_sha256']")
for d in ledger['domains']:assert eval(domain_code,{'d':d,'required':required})
d=dict(ledger['domains'][0],ledger_sha256='0'*64);guarded('native_ledger_wrong_frozen_domain_hash',domain_code,{'d':d,'required':required})
browser=j(R/'reports/full-coverage/browser-checkpoint-28.json');binput=j(R/'reports/full-coverage/browser-corrections-28-inputs.json');assets=browser['source_sha256']
assert len(assets)==31
browser_code=test("browser['status']");assert eval(browser_code,{'browser':browser})
for key,value in [('status','failed'),('page_count',28),('requested_viewport_count',144)]:
 bad=dict(browser);bad[key]=value;guarded('actual_browser28_'+key,browser_code,{'browser':bad})
page_code=test("len(browser['pages'])");assert eval(page_code,{'browser':browser})
bad=copy.deepcopy(browser);bad['pages'][0]['status']='failed';guarded('actual_browser28_page_failed',page_code,{'browser':bad})
bad=copy.deepcopy(browser);bad['pages'][0]['errors']=['fixture'];guarded('actual_browser28_page_errors',page_code,{'browser':bad})
image_code=test("len(screenshots)");assert eval(image_code,{'screenshots':binput['screenshot_aliases']})
bad=copy.deepcopy(binput['screenshot_aliases']);bad[1]['file']=bad[0]['file'];guarded('actual_browser28_duplicate_image_alias',image_code,{'screenshots':bad})
for row in binput['screenshot_aliases']:assert m.sha(R,row['original'])==row['sha256']
obs.append({'fixture':'all48_actual_original_screenshot_byte_aliases','passed':True})
fresh=j(R/browser['actual_execution']);m.native(fresh,fresh['actual_command']);assert fresh['source_sha256_before']==fresh['source_sha256_after']==assets
for n,digest in fresh['qa_source_sha256'].items():assert h(R/n)==digest
assert h(R/fresh['report'])==fresh['report_sha256']
obs.append({'fixture':'genuine_browser28_native_command0_log_source31_qa2_report_bindings','passed':True})
scroll=j(R/'reports/full-coverage/source60-four-page-math-scroll28-v3.json');scroll_code=test("scroll['status']");assert eval(scroll_code,{'scroll':scroll,'assets':assets})
bad=copy.deepcopy(scroll);bad['source_sha256'][next(iter(assets))]='0'*64;guarded('actual_scroll28_wrong_source_hash',scroll_code,{'scroll':bad,'assets':assets})
scroll_page_code=test("overflow_containers");assert eval(scroll_page_code,{'scroll':scroll})
bad=copy.deepcopy(scroll);bad['pages'][0]['overflow_containers'][0]['status']='failed';guarded('actual_scroll28_failed_overflow_container',scroll_page_code,{'scroll':bad})
real_execution=m.actual('reports/full-coverage/source60-math-scroll28-execution-v3.json',['node','book/coverage/checks/root_check_math_scroll28_v3.mjs']);obs.append({'fixture':'genuine_current_scroll_v3_native_execution0_current_helper_maps_log','passed':True})
# Full native reader function rejection tests use isolated synthetic JSON files only.
with tempfile.TemporaryDirectory(prefix='pages28-v2-isolated-native-')as td:
 ctx=Path(td);oldroot=m.ROOT;m.ROOT=ctx;log=ctx/'log';log.write_bytes(b'exact fixture log');helper=ctx/'fixture-helper.py';helper.write_bytes(b'fixture bytes');cmd=['python3','fixture-helper.py'];native={'status':'passed','actual_exit_code':0,'actual_command':cmd,'actual_workdir':str(ctx),'log':'log','log_sha256':h(log),'helper_sha256_before':{'fixture-helper.py':h(helper)},'helper_sha256_after':{'fixture-helper.py':h(helper)}}
 record=ctx/'actual.json'
 def call(d):record.write_text(json.dumps(d));return m.actual('actual.json',cmd)
 assert call(native)==native;obs.append({'fixture':'isolated_native_function_valid_exact_aliases_helpers_log','passed':True})
 variants=[('status','failed'),('actual_exit_code',False),('exit_code',1),('actual_runner_exit_code',1),('command',['false']),('working_directory','/tmp/wrong'),('cwd','/tmp/wrong'),('workdir','/tmp/wrong'),('raw_log','wrong-log'),('raw_log_sha256','0'*64),('helper_sha256_before',{'fixture-helper.py':'0'*64}),('helper_sha256_after',{'fixture-helper.py':'0'*64})]
 for key,value in variants:
  bad=copy.deepcopy(native);bad[key]=value;rejected('isolated_native_'+key,lambda bad=bad:call(bad))
 helper.write_bytes(b'changed bytes');rejected('isolated_native_helper_changed_current_bytes',lambda:call(native));m.ROOT=oldroot
 # Execute the producer's exact loop, not the writer or complete prepare().
 prep=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='prepare');assign=next(n for n in prep.body if isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='included'for x in n.targets));idx=prep.body.index(assign);loop=prep.body[idx+1];assert isinstance(loop,ast.For)
 budget_code=compile(ast.Module(body=[assign,loop],type_ignores=[]),'<exact-pages28-v2-included-tree-loop>','exec')
 pub=ctx/'pub';pub.mkdir();(pub/'plain').write_bytes(b'abcde');outside=ctx/'outside';outside.write_bytes(b'0123456789')
 def budget(exclusions=set()):
  env={'PUB':pub,'kept':m.kept,'exclusions':exclusions};exec(budget_code,env);return env['included']
 assert budget()==5;obs.append({'fixture':'actual_budget_loop_plain_tree','passed':True})
 (pub/'included-link').symlink_to(outside);rejected('included_file_symlink_budget',budget);(pub/'included-link').unlink()
 (pub/'included-link').symlink_to(ctx,target_is_directory=True);rejected('included_directory_symlink_budget',budget);(pub/'included-link').unlink()
 (pub/'excluded-link').symlink_to(ctx,target_is_directory=True);assert budget({'excluded-link'})==5;obs.append({'fixture':'excluded_directory_symlink_skipped_before_rejection','passed':True});(pub/'excluded-link').unlink()
 (pub/'.git').symlink_to(ctx,target_is_directory=True);assert budget()==5;obs.append({'fixture':'git_directory_symlink_skipped_before_rejection','passed':True})
assert len(m.ADDITIONS)==20 and len({n for n in m.ADDITIONS if n.startswith('book/coverage/inventory-')})==10
assert m.kept('archive-sibling/file',{'archive'})and not m.kept('archive/file',{'archive'})and not m.kept('archive',{'archive'});obs.append({'fixture':'literal20_exclusions_and_exact_prefix_membership','passed':True})
for n in ['/tmp/absolute','../escape','folder*','folder?','folder[0]','folder\nname']:rejected('unsafe_literal_path_'+repr(n),lambda n=n:m.safe(R,n))
findings=[]
out={'status':'passed_full_independent_pages28_config3_code_native_schema_and_guard_fixture_review','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(S),'full_source_lines_read':len(S.read_text().splitlines()),'fixture_count':len(obs),'fixture_observations':obs,'findings':findings,'actual_current28_manifest_frozen_audit_publication_prerequisites_available':False,'production_prepare_or_writer_executed':False,'actual_complete_production_budget_preflight_executed':False,'code_approval_for_root_owned_genuine_runtime_preflight':True,'production_approval':False,'scope':'Full v1/v2 source and exact v3 delta and native declaration, baseline ledger, browser28/scroll28 source31, QA2, native command0/log, 48 actual byte aliases. Exact producer function/assert/tree fixtures are isolated and do not fabricate production audit/manifest/ledger or website-budget success.'}
with OUT.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'fixture_count':len(obs),'code_approval_for_root_owned_genuine_runtime_preflight':True,'production_approval':False}))
