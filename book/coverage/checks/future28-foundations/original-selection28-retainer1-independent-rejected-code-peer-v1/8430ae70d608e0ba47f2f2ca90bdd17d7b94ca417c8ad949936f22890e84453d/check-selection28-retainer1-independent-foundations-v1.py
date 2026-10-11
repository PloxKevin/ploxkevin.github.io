from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/selection28-retainer1-independent-foundations-findings-v1.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':h(p)}
S=R/'book/coverage/prepare_checkpoint28_selection_v1.py';T=R/'book/coverage/retain_baseline_inputs28_v1.py';N=R/'book/coverage/lean_names.py'
assert h(S)=='ed0e8849a2fdca79911363e4249c709dd698003e13b1d3915ff824135a9ed061' and h(T)=='a53495772823cf7ab3124089e99b3facd4284d6184a2954010a39bb322da13db'and not OUT.exists()
pins=json.loads((R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json').read_bytes())['protected_inputs_sha256']
def guard():
 for n,s in pins.items():assert h(R/n)==s,n
guard();started=datetime.now(timezone.utc).isoformat();sys.path.insert(0,str(R/'book/coverage'))
spec=importlib.util.spec_from_file_location('selection28_review1',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
trees={str(p):ast.parse(p.read_text())for p in [S,T]};obs=[]
def expression(p,needle):
 found=[x.test for x in ast.walk(trees[str(p)])if isinstance(x,ast.Assert)and needle in ast.unparse(x.test)];assert len(found)==1,(needle,len(found));return found[0]
def evaluate(node,scope):return eval(compile(ast.Expression(node),'<exact-unmodified-helper-assert>','eval'),scope)
def reject(fn):
 try:fn()
 except (AssertionError,KeyError,ValueError):return True
 return False
audit=json.loads((R/'reports/full-coverage/lean-checkpoint-27/verification-original.json').read_bytes());assert audit['status']=='passed'and len(audit['checks'])==1178
for p in [S,T]:
 exp=expression(p,"all((type(r['exit_code']) is int")
 native=copy.deepcopy(audit);native['checks'][0]['actual_exit_code']=1
 accepted=evaluate(exp,{'audit':native});assert accepted is True
 obs.append({'fixture':'native_baseline_audit_present_conflicting_actual_exit_code','helper':ref(p),'accepted_by_v1_guard':accepted,'required_result':'reject','finding':'Existing inline native audit guard checks only exit_code; conflicting present actual_exit_code is ignored.'})
 native=copy.deepcopy(audit);native['checks'][0]['exit_code']=False
 assert evaluate(exp,{'audit':native})is False
 obs.append({'fixture':'native_baseline_audit_boolean_false_is_not_integer_zero','helper':ref(p),'rejected':True})
native=json.loads((R/'book/coverage/checks/CompleteFoundationsResidualWeightingIdentification27-standalone.json').read_bytes())
paircmd=expression(S,"native['command'] == command");expected=native['command'];native['actual_command']=['false-conflicting-command'];native['cwd']='/tmp/conflicting-cwd'
accepted=evaluate(paircmd,{'native':native,'command':expected,'ROOT':R});assert accepted is True
obs.append({'fixture':'native_pair_present_conflicting_command_and_cwd_aliases','accepted_by_v1_guard':True,'required_result':'reject','finding':'Direct command/actual_workdir fields leave present actual_command/cwd aliases unchecked.'})
for bad in [{'exit_code':False},{'exit_code':0,'actual_exit_code':1},{'actual_exit_code':False},{}]:
 assert reject(lambda:m.zero(bad));obs.append({'fixture':'allpresent_zero_helper_rejects','native_value':bad,'rejected':True})
target={'a':'0'*64};assert reject(lambda:m.merge(target,{'a':'1'*64}));assert target=={'a':'0'*64};obs.append({'fixture':'merge_conflicting_existing_reference','rejected':True})
for name in ['/tmp/absolute-not-root-relative','../escape']:
 assert reject(lambda:m.safe(name));obs.append({'fixture':'unsafe_path_rejected','path':name,'rejected':True})
tmp=Path(tempfile.mkdtemp(prefix='selection28-helper1-guards-'));oldroot=m.ROOT;m.ROOT=tmp
f=tmp/'typed.json';f.write_text('{}');assert reject(lambda:m.checked({'file':'typed.json','sha256':'0'*64}));m.ROOT=oldroot
obs.append({'fixture':'typed_existing_native_file_wrong_sha','rejected':True})
empty={};m.merge(empty,{});assert empty=={};obs.append({'fixture':'empty_helpers_map_allowed_by_only_merge_validation','accepted_by_v1_guard':True,'required_result':'reject_exact_required_selector_retainer_parser_dependency_set','scope':'This observes the dependency-map primitive, not a complete positive production plan.'})
prepare=next(x for x in trees[str(S)].body if isinstance(x,ast.FunctionDef)and x.name=='prepare')
nofile=next(x for x in ast.walk(prepare)if isinstance(x,ast.If)and ast.unparse(x.test)=='not apply')
assert isinstance(nofile.body[0],ast.Return)
newsha_asserts=[ast.unparse(x.test)for x in ast.walk(prepare)if isinstance(x,ast.Assert)and 'sha(n)'in ast.unparse(x.test)]
assert not any("expected[n]"in x or "selected[n]"in x for x in newsha_asserts)
guard()
out={'status':'full_code_review_completed_v1_rejected_pending_four_concrete_repairs','errors':[],'reviewer':'/root/foundations_recovery28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reader_started_at_utc':started,'helper':ref(S),'retainer':ref(T),'parser_dependency':ref(N),'full_source_lines_read':{'selector':len(S.read_text().splitlines()),'retainer':len(T.read_text().splitlines())},'fixture_count':len(obs),'fixture_observations':obs,'actual_production_prepare_or_retain_executed':False,'complete_genuine_plan_preflight_executed':False,'production_approval':False,'findings':[{'id':'strict_allpresent_native_aliases','scope':'Both baseline audit loops and all command/cwd/status native records','required_repair':'All present native exit aliases exact int0; present command/cwd aliases equal expected; present status passed.'},{'id':'preflight_current_selected_source_sha','scope':'Before apply=False can return success','required_repair':'Explicitly verify every selected1186 source SHA, including all eleven new canonical files.'},{'id':'reviewed_exact_helper_dependency_set','scope':'Selector, retainer and lean_names parser','required_repair':'Require exact three pinned helper paths/SHA and peer reviewed dependency refs, rejecting omissions and arbitrary map substitutions.'},{'id':'all_outputs_prevalidated_before_any_write','scope':'Retainer contentmap and selection payload transaction','required_repair':'Prepare payloads without writer side effects; verify both output paths/collisions/sizes before first canonical file write.'}],'old_original_baseline_schema':{'proof_sources':1175,'public_theorems':9644,'native_checks':1178,'frozen_inputs':48662},'scope':'Actual execution of isolated native-schema assert expressions and pure guard functions from exact v1 code. No adapted positive production result or whole preparation/retention execution claimed. Original unexecuted writers require repairs.'}
with OUT.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'fixture_count':len(obs),'production_approval':False}))
