from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,runpy,tempfile,copy,sys,contextlib,io,subprocess,ast
R=Path('/home/oxrexkevin/SafetyBased');HELP=R/'book/coverage/checks/run_root28_current60_canonical_pairs_v1.py';PLAN=Path('/tmp/root28-current60-canonical-pair-plan-v1.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_bytes())
assert H(PLAN)=='64fe57b1296bf5d016eaf3da375a382454ea8c310c23c3421220000f0565533b'
started=datetime.now(timezone.utc).isoformat();d=runpy.run_path(str(HELP));cases=[]
def case(name,f,should_reject=False):
 try:f();rejected=False
 except (AssertionError,TypeError,ValueError,FileNotFoundError):rejected=True
 assert rejected==should_reject,(name,rejected,should_reject);cases.append({'name':name,'expected_reject':should_reject,'observed_reject':rejected})
case('strict exit integer zero accepted',lambda:d['zero']({'actual_exit_code':0,'exit_code':0,'actual_runner_exit_code':0}))
for v in [False,True,1,-1,None,'0',0.0]:case('strict exit rejects '+repr(v),lambda v=v:d['zero']({'actual_exit_code':v}),True)
case('missing exit rejects',lambda:d['zero']({}),True)
case('conflicting exit aliases reject',lambda:d['zero']({'exit_code':0,'actual_exit_code':1}),True)
case('all original10 peers source refs equal actual plan',lambda:all_refs()) if False else None
plan=J(PLAN);actual_refs=[]
for row in plan['sources']:
 src=J(row['independent_whole_scope_peer']['file']);ptr=src.get('proof_source',src.get('source'));assert {k:ptr[k]for k in ('file','sha256')}==row['original_tmp_source'];actual_refs.append({'canonical_source':row['canonical_source'],'peer_sha256':row['independent_whole_scope_peer']['sha256'],'peer_source':ptr})
pre=subprocess.run([sys.executable,str(HELP),'--plan',str(PLAN),'--plan-sha256',H(PLAN)],cwd=R,capture_output=True,text=True)
assert pre.returncode==0,(pre.stdout,pre.stderr)
with tempfile.TemporaryDirectory(prefix='root28-executor-review-fixtures-') as td:
 T=Path(td);TROOT=T/'root';TROOT.mkdir();NS=runpy.run_path(str(HELP));NS['main'].__globals__['ROOT']=TROOT;NS['main'].__globals__['BASE']=TROOT/'closure';NS['main'].__globals__['RESULT']=TROOT/'closure/result.json';NS['main'].__globals__['protection']=lambda source:{}
 plan_fixture=copy.deepcopy(plan)
 for row in plan_fixture['sources']:
  native=J(row['original_actual_tmp_trial']['file']);native['actual_workdir']=str(TROOT/'verification/lean');p=T/(Path(row['canonical_source']).stem+'-synthetic-original-trial.json');p.write_text(json.dumps(native));row['original_actual_tmp_trial']={'file':str(p),'sha256':H(p)}
 for n,h in NS['HELPERS'].values():
  target=TROOT/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((R/n).read_bytes());assert H(target)==h
 def prepare(pp,return_guard=False):
  file=T/(str(len(list(T.glob('plan*.json'))))+'plan.json');file.write_text(json.dumps(pp));argv=sys.argv[:];sys.argv=[str(HELP),'--plan',str(file),'--plan-sha256',H(file)]
  try:
   if not return_guard:
    with contextlib.redirect_stdout(io.StringIO()):NS['main']()
   else:
    tree=ast.parse(HELP.read_text());main=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='main')
    gate=next(n for n in main.body if isinstance(n,ast.If)and isinstance(n.test,ast.UnaryOp))
    gate.body=ast.parse('return guard, originals, protected').body
    t=ast.Module(body=[main],type_ignores=[]);ast.fix_missing_locations(t);env=dict(NS['main'].__globals__);exec(compile(t,str(HELP),'exec'),env);return env['main']()
  finally:sys.argv=argv
 case('synthetic workspace same actual10 native inputs dry acceptance',lambda:prepare(plan_fixture))
 wrong=copy.deepcopy(plan_fixture);peer=J(wrong['sources'][0]['independent_whole_scope_peer']['file']);peer['proof_source']=copy.deepcopy(wrong['sources'][1]['original_tmp_source']);badpeer=T/'wrong-source-peer.json';badpeer.write_text(json.dumps(peer));wrong['sources'][0]['independent_whole_scope_peer']={'file':str(badpeer),'sha256':H(badpeer)}
 case('v1 actual main permits semantic peer for wrong source (requires changes)',lambda:prepare(wrong))
 guard,originals,protected=prepare(wrong,True);assert str(badpeer)in originals;badpeer.write_text('changed original peer after validation\n');case('v1 actual nested guard omits original peer digest (requires changes)',guard)
 for name,delta in [('wrong canonical parent',lambda p:p['sources'][0].update(canonical_source='other/CompleteInvalid.lean')),('wrong theorem count',lambda p:p['sources'][0].update(public_theorem_count=999)),('duplicate declaration mapping',lambda p:p['sources'][1].update(public_declarations=p['sources'][0]['public_declarations'])),('wrong peer status',lambda p:p['sources'][0].update(expected_peer_status='invented_status'))]:
  pp=copy.deepcopy(plan_fixture);delta(pp);case(name,lambda pp=pp:prepare(pp),True)
 findings={'status':'requires_changes_independent_canonical_pair_executor_code_review','errors':['Original source/peer/trial/log/snapshot digests are not protected throughout/copy is not postchecked.','Semantic peer source pointer is not required to match approved source.','All10 newly installed canonical sources are not rehashed after final named command.'],'helper':{'file':str(HELP.relative_to(R)),'sha256':H(HELP)},'plan':{'file':str(PLAN),'sha256':H(PLAN)},'started_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_readonly_preflight':{'exit_code':pre.returncode,'stdout':pre.stdout,'stderr':pre.stderr,'producer_apply':False},'fixture_count':len(cases),'fixtures':cases,'all10_actual_native_peer_source_refs_verified':actual_refs,'scope':'Actual helper functions plus isolated synthetic ROOT fixture. No producer --apply, Lean command, canonical copy, owner, PUB or Git mutation. V1 acceptance observations show guard gaps; they are not compiler/production failures.'}
 out=Path('/tmp/root28-canonical-pairs-independent-applied-findings-v2.json');assert not out.exists();out.write_text(json.dumps(findings,indent=2)+'\n');print(json.dumps({'findings':str(out),'sha256':H(out),'fixture_count':len(cases),'actual_readonly_preflight':pre.returncode,'status':findings['status']}))
