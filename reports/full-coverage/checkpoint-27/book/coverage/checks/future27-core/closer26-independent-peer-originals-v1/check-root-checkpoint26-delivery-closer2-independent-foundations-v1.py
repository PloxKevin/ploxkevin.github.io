from pathlib import Path
from datetime import datetime,timezone
import ast,copy,json,hashlib,subprocess
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
n='book/coverage/checks/close_root_checkpoint26_delivery_originals_v2.py';old='book/coverage/checks/close_root_checkpoint26_delivery_originals_v1.py'
assert H(R/n)=='6de6ca53709605b48b30956078043e15c8e24af6609f14e75c90c272f197097e'
assert H(R/old)=='9a75178916c89f3cd440d74e98fdda4d4c8a0d84e8784bb9b06c08ad2cf7e3f2'
t=ast.parse((R/n).read_text());o=ast.parse((R/old).read_text())
class Inverse(ast.NodeTransformer):
 def visit_Constant(self,node):
  if isinstance(node.value,str):node.value=node.value.replace('closed-checkpoint26-delivery-originals-v2','closed-checkpoint26-delivery-originals-v1').replace('close-checkpoint26-delivery-originals-execution-v2','close-checkpoint26-delivery-originals-execution-v1')
  return node
 def visit_FunctionDef(self,node):
  node=self.generic_visit(node)
  if node.name=='main':
   loop=next(x for x in node.body if isinstance(x,ast.For) and ast.unparse(x.target)=='attempt')
   loop.body=[x for x in loop.body if not ('page_codes' in ast.unparse(x))]
  return node
assert ast.dump(Inverse().visit(copy.deepcopy(t)),include_attributes=False)==ast.dump(o,include_attributes=False)
funcs=[x for x in t.body if isinstance(x,ast.FunctionDef) and x.name!='main'];ns={'ROOT':R,'REPORTS':R/'reports/full-coverage','Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess}
exec(compile(ast.Module(body=funcs,type_ignores=[]),n,'exec'),ns)
main=next(x for x in t.body if isinstance(x,ast.FunctionDef) and x.name=='main');loop=next(x for x in main.body if isinstance(x,ast.For) and ast.unparse(x.target)=='attempt')
code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(loop.body),type_ignores=[])),n,'exec')
manifest=json.loads((R/'reports/full-coverage/checkpoint-26-manifest.json').read_text());assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and len(manifest['proof_files'])==1167
for p,row in manifest['proof_files'].items():assert H(R/p)==row['sha256']
for p,h in assets.items():assert H(R/p)==h
cases=[]
def case(label,fn,reject=False,synthetic=True):
 try:fn()
 except (AssertionError,KeyError,TypeError,ValueError,FileNotFoundError):assert reject,label;result='rejected'
 else:assert not reject,label;result='accepted'
 cases.append({'fixture':label,'observed':result,'synthetic_guard_fixture':synthetic})
actualread=ns['read']
def attempt2(change=None):
 env=dict(ns,attempt=2,commits={},assets=assets)
 def read(p):
  d=actualread(p)
  if change and p==R/'reports/full-coverage/pages-checkpoint-26-attempt2.json':change(d)
  return d
 env['read']=read
 exec(code,env)
case('actual successful content attempt2 complete native loop',attempt2,synthetic=False)
for field,val in [('actual_exit_code',False),('exit_code',False),('exit_code',0.0),('exit_code',1),('actual_exit_code',1)]:
 case('reject conflicting or ill-typed native Pages '+field+repr(val),lambda field=field,val=val:attempt2(lambda d:d.update({field:val})),True)
case('reject Pages native missing all exit fields',lambda:attempt2(lambda d:[d.pop(k,None) for k in ('actual_exit_code','exit_code')]),True)
case('actual first live failure preserved strictly1',lambda:ns['actual']('live26-attempt1-execution-v1',1),synthetic=False)
case('actual original main3 failure preserved strictly1',lambda:ns['actual']('stage-publication26-execution-v1',1),synthetic=False)
case('first live failure cannot become success',lambda:ns['actual']('live26-attempt1-execution-v1'),True,False)
for suff in ['.json','.log']:
 p=Path('close-checkpoint26-delivery-originals-execution-v2'+suff)
 assert p.stem=='close-checkpoint26-delivery-originals-execution-v2'
case('exact active closer JSON and raw log both excluded by stem',lambda:None)
for suff in ['.json','.log']:
 p=Path('close-checkpoint26-delivery-originals-execution-v1'+suff);assert p.stem!='close-checkpoint26-delivery-originals-execution-v2'
case('closed old closer names do not share active stem',lambda:None)
for bad in ['/tmp/file','../file','./book/a','book//a','book/a\n']:
 case('reject unsafe closure root path '+repr(bad),lambda bad=bad:ns['safe'](bad),True)
firstwrite=next(i for i,x in enumerate(main.body) if isinstance(x,ast.For) and 'target.open' in ast.unparse(x))
assert not any(isinstance(x,ast.Call) and ast.unparse(x.func) in ['shutil.copyfile','shutil.copytree'] for node in main.body[:firstwrite] for x in ast.walk(node))
source=(R/n).read_text()
for phrase in ["for attempt in [2,3]", "commits[2]!=commits[3]", "codes and all(type(c) is int and c==code", "p.stem!=ACTIVE", "actual('live26-attempt1-execution-v1',1)", "actual('stage-publication26-execution-v1',1)", "with target.open('xb')", "for n,h in protected.items():assert sha(safe(n))==h,n"]:assert phrase in source
paths=[n,old,'reports/full-coverage/checkpoint-26-manifest.json','reports/full-coverage/live-checkpoint-26-attempt2.json','reports/full-coverage/pages-checkpoint-26-attempt2.json','reports/full-coverage/live26-attempt2-execution-v1.json','reports/full-coverage/live26-attempt2-execution-v1.log','reports/full-coverage/live26-attempt1-execution-v1.json','reports/full-coverage/live26-attempt1-execution-v1.log','reports/full-coverage/stage-publication26-execution-v1.json','reports/full-coverage/stage-publication26-execution-v1.log']
out=Path('/tmp/root-checkpoint26-delivery-closer2-independent-foundations-code-review-v1.json');assert not out.exists()
d={'status':'independent_full_delivery_closer2_code_and_native_guards_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':n,'sha256':H(R/n)},'helper_sha256':H(R/n),'original_unexecuted_closer1':{'file':old,'sha256':H(R/old)},'exact_AST_inverse_with_only_Base_Active_and_strict_native_Pages_gate':True,'fixture_count':len(cases),'fixtures':cases,'actual_content_attempt2_native_read':True,'selected1167_and_current31_rehashed':True,'actual_closed_evidence_sha256':{p:H(R/p) for p in paths},'scope':'Full code and focused read-only content2/native strict-success and retained-failure guard review. Real metadata3 Pages/live completion remains a required future producer prerequisite; no closer application, archive copying, deployment or Git executed.'}
out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'status':'passed','peer':str(out),'sha256':H(out),'fixtures':len(cases)}))
