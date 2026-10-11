from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
C='book/coverage/checks/root_close_checkpoint26_selection_plan_v1.py';R='book/coverage/checks/root_check_checkpoint26_selection_output_v2.py';cs=(ROOT/C).read_text();rs=(ROOT/R).read_text();ct=ast.parse(cs);rt=ast.parse(rs)
assert H(ROOT/C)=='65d4e1ecfad944cb019734c8def8729d2b267395533eb7a480716fad92977a6a';assert H(ROOT/R)=='9c1959903a4f7a92808478c85a92fafe2e0381250e7b1fb83479e77bc1de86b4'
# Exact original closer25 text after only checkpoint25->26, previous config26
# history references intentionally stay25 and do not approve any new output.
old=(ROOT/'book/coverage/checks/root_close_checkpoint25_selection_plan_v2.py').read_text();expected=old.replace('checkpoint25','checkpoint26').replace('owner25','owner26').replace('future25','future26').replace('checkpoint-25','checkpoint-26');expected=expected.replace('pages26-config','pages25-config');assert cs==expected
fixtures=[]
def check(label,nodes,scope,want):
 okay=True
 try:exec(compile(ast.Module(body=nodes,type_ignores=[]),label,'exec'),scope,scope)
 except (AssertionError,KeyError,ValueError,FileNotFoundError):okay=False
 assert okay==want,label;fixtures.append({'fixture':label,'accepted':okay,'expected_acceptance':want,'synthetic_only':True})
loop=next(n for n in ct.body if isinstance(n,ast.For)and isinstance(n.target,ast.Name)and n.target.id=='stem')
base={'actual_exit_code':0,'exit_code':0,'log':'fixture.log','log_sha256':'a'*64}
for label,mutate,want in [('closed int-zero success',lambda d:None,True),('boolean false',lambda d:d.update(actual_exit_code=False),False),('conflicting exit',lambda d:d.update(exit_code=1),False),('no exit aliases',lambda d:[d.pop(k)for k in ('actual_exit_code','exit_code')],False),('wrong log digest',lambda d:d.update(log_sha256='b'*64),False)]:
 d=copy.deepcopy(base);mutate(d);check('closer '+label,[loop],{'read':lambda n:copy.deepcopy(d),'sha':lambda n:'a'*64,'records':[]},want)
# Independently execute the actual closer's body-preserving inverse, without any
# archive creation or production plan writes.
start=next(i for i,n in enumerate(ct.body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='out'for t in n.targets));end=next(i for i in range(start,len(ct.body))if isinstance(ct.body[i],ast.With));nodes=ct.body[start:end]
prior={'status':'independently_reviewed_installed_owner26_selection_plan','additional_frozen_inputs':{},'helpers_sha256':{},'original_semantic_row':{'reason':'Preserve exact reason','hypotheses':['hyp'],'time':'synthetic immutable historical time'}}
scope={'copy':copy,'old':copy.deepcopy(prior),'extra':{'book/coverage/synthetic-reviewed.json':{'sha256':'a'*64,'scope':'immutable_audit_or_local_source_evidence'}},'Path':Path,'__file__':str(ROOT/C),'ROOT':ROOT,'sha':lambda n:'a'*64,'ref':lambda n:{'file':n,'sha256':'a'*64},'OLD':'book/coverage/checks/future26-core/synthetic-old-plan.json','catalog':'book/coverage/checks/future26-core/synthetic-catalog.json','datetime':datetime,'timezone':timezone}
exec(compile(ast.Module(body=nodes,type_ignores=[]),'closer-exact-inverse','exec'),scope,scope);assert scope['old']==prior and scope['inverse']==prior and scope['out']['entire_original_installed_owner_selection_plan_v1_body_and_time']==prior
# Root output reader canonical path and strict native-exit assertions run against
# isolated in-memory records, never production outputs or approved plan files.
functions=[n for n in rt.body if isinstance(n,ast.FunctionDef)and n.name=='safe'];g={'Path':Path,'ROOT':ROOT};exec(compile(ast.Module(body=functions,type_ignores=[]),'reader-safe','exec'),g,g)
for name,want in [('book/coverage/core.json',True),('../outside',False),('/tmp/outside',False),('book//coverage/core.json',False)]:check('Root reader path '+name,[ast.parse('safe(name)').body[0]],dict(g,name=name),want)
zero_nodes=[n for n in rt.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='codes'for t in n.targets)]+[n for n in rt.body if isinstance(n,ast.Assert)and 'codes and all' in ast.unparse(n)]
for d,want in [({'actual_exit_code':0},True),({'actual_exit_code':False},False),({'actual_exit_code':0,'exit_code':1},False),({},False)]:check('Root reader strict exit '+repr(d),zero_nodes,{'actual':d},want)
assert "len(public) == len(set(public)) == 9503" in rs
assert "current['checkpoint26_original_baseline_owner_evidence']" in rs and "original['original_row_body'] == old" in rs
assert "'kind'] in {'theorem', 'lemma'}" in rs and "1167" in rs and "44111" in rs
assert 'passed_independent_root_actual_selection26_output_review' in rs
basepath=ROOT/'book/coverage/checks/future26-core';reports=[]
for n,helper,scope_note in [('checkpoint26-plan-closer-independent-applied-code-review-v1.json',C,'Actual closed interface/plan records remain future requirements. Isolated native-exit and exact inverse fixtures only; no Root plan/archive write.'),('root-checkpoint26-output-reader-independent-applied-code-review-v1.json',R,'Code/actual isolated canonical-path and strict native-exit fixtures only. Actual produced selector bytes/Root checker execution remain required; no production output peer or Lean result inferred.')]:
 p=basepath/n;assert not p.exists();report={'status':'passed_independent_full_code_and_isolated_native_guard_fixtures','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_applied','helper':ref(helper),'helper_sha256':H(ROOT/helper),'full_code_read':True,'fixtures':fixtures,'fixture_count':len(fixtures),'scope':scope_note};p.write_text(json.dumps(report,indent=2)+'\n');reports.append(ref(str(p.relative_to(ROOT))))
print(json.dumps({'status':'passed','reports':reports,'fixtures':len(fixtures)}))
