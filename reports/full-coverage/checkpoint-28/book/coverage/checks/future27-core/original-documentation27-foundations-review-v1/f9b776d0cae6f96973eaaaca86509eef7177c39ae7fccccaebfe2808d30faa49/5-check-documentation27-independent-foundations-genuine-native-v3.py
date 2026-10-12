"""Read-only exact helper pre-write AST using genuine checkpoint27 native evidence."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,sys,time,traceback
ROOT=Path('/home/oxrexkevin/SafetyBased')
p=Path(sys.argv[1]);version=sys.argv[2]
helper_bytes=p.read_bytes();tree=ast.parse(helper_bytes)
def assignment(name):return next(i for i,n in enumerate(tree.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets))
start=assignment('selectionn')
stop=next(i for i,n in enumerate(tree.body) if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and any(isinstance(t,ast.Name) and t.id=='body' for t in n.target.elts))
def compile_slice(a,b):return compile(ast.Module(body=tree.body[a:b],type_ignores=[]),str(p),'exec')
ns={'__file__':str(ROOT/'book/coverage/checks'/p.name)}
exec(compile_slice(0,start),ns)
protected={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in ['book/coverage/progress.json','reports/full-coverage/README.md','book/coverage/checks/root_prepare_checkpoint27_documentation_v1.py']}
began=time.monotonic();exec(compile_slice(start,stop),ns)
assert ns['progress']['live_delivery_evidence'] is None
assert ns['progress']['previous_checkpoint26_delivery']['live_evidence']=='reports/full-coverage/live-checkpoint-26-attempt2.json'
assert ns['progress']['verified_checkpoint']['proof_files']==1175
assert ns['progress']['verified_checkpoint']['theorems']==9644
results=[{'fixture':'entire genuine27 native pre-write positive control','accepted':True,'expected_acceptance':True,'elapsed_seconds':time.monotonic()-began,'current_live_delivery_evidence':None,'prior26_live_delivery_evidence':ns['progress']['previous_checkpoint26_delivery']['live_evidence']}]
real_read=ns['read']
def section(label,a,b,filename,mutate,expect=False):
 state=dict(ns)
 exec(compile_slice(0,start),state)
 altered=copy.deepcopy(real_read(filename));mutate(altered)
 state['read']=lambda n:altered if n==filename else real_read(n)
 began=time.monotonic()
 try:exec(compile_slice(a,b),state);accepted=True;error=None
 except Exception as e:accepted=False;error=type(e).__name__+': '+str(e)
 row={'fixture':label,'accepted':accepted,'expected_acceptance':expect,'expectation_met':accepted==expect,'error':error,'elapsed_seconds':time.monotonic()-began,'scope':'Exact guard AST segment with one copied genuine native object changed; unchanged file reads/hashes remain actual.'}
 results.append(row);print(json.dumps(row));assert accepted==expect
A='reports/full-coverage/lean-checkpoint-27/verification-original.json'
B='reports/full-coverage/browser-checkpoint-27.json'
E='reports/full-coverage/verify-checkpoint27-execution-v1.json'
auditstart=assignment('auditn');auditstop=assignment('execution_specs')
browserstart=assignment('browsern');browserstop=assignment('progressn')
execstart=assignment('execution_specs');execstop=assignment('ledger')
section('mismatched axiom/declaration name',auditstart,auditstop,A,lambda d:d['declarations'][0].update(name='SafeLearning.UnindexedWrongDeclaration'))
section('duplicate declaration preserving length',auditstart,auditstop,A,lambda d:d['declarations'].__setitem__(0,dict(d['declarations'][1])))
section('wrong Lean version',auditstart,auditstop,A,lambda d:d.update(lean_version='Lean (version 4.0.0, wrong environment)'))
section('wrong mathlib revision',auditstart,auditstop,A,lambda d:d.update(mathlib_revision='0'*40))
section('changed selected proof digest',auditstart,auditstop,A,lambda d:d['proof_sha256'].__setitem__(next(iter(d['proof_sha256'])),'0'*64))
section('wrong native axiom audit command',auditstart,auditstop,A,lambda d:d['checks'][-1].update(command=['lake','build']))
section('unsafe axiom',auditstart,auditstop,A,lambda d:d['axiom_dependencies'].__setitem__(next(iter(d['axiom_dependencies'])),['sorryAx']))
section('bool false check exit',auditstart,auditstop,A,lambda d:d['checks'][0].update(exit_code=False))
section('browser failed status',browserstart,browserstop,B,lambda d:d.update(status='failed'))
section('browser manual inspection pending',browserstart,browserstop,B,lambda d:d['manual_visual_inspection'].update(status='pending',fresh_actual_captures=0,retained_exact_capture_count=0))
section('browser four-manual-review hash corrupted',browserstart,browserstop,B,lambda d:d['manual_visual_inspection']['new_original_four_review'].update(sha256='0'*64))
section('browser QA fingerprint corrupted',browserstart,browserstop,B,lambda d:d['qa_source_sha256'].__setitem__(next(iter(d['qa_source_sha256'])),'0'*64))
section('browser viewport total inconsistent',browserstart,browserstop,B,lambda d:d.update(verified_viewport_count=0))
section('browser skipped target count inconsistent',browserstart,browserstop,B,lambda d:d.update(skipped_capture_target_count=99))
section('browser region inspection wrongly approves whole pages',browserstart,browserstop,B,lambda d:d['manual_visual_inspection'].update(whole_page_visual_approval=True))
section('browser old48 closure reference changed',browserstart,browserstop,B,lambda d:d['manual_visual_inspection']['entire_original48_checkpoint26_review'].update(sha256='0'*64))
section('empty execution helper fingerprints',execstart,execstop,E,lambda d:d.update(helper_sha256_before={},helper_sha256_after={}))
section('bool false actual execution exit',execstart,execstop,E,lambda d:d.update(actual_exit_code=False))
section('wrong native actual execution command',execstart,execstop,E,lambda d:d.update(actual_command=['python3','unexecuted.py']))
section('wrong execution log hash',execstart,execstop,E,lambda d:d.update(log_sha256='0'*64))
section('contradictory actual exit alias',execstart,execstop,E,lambda d:d.update(exit_code=1))
section('contradictory audit actual-exit alias',auditstart,auditstop,A,lambda d:d['checks'][0].update(actual_exit_code=1))
section('bool audit actual-exit alias',auditstart,auditstop,A,lambda d:d['checks'][0].update(actual_exit_code=False))
section('contradictory native command alias',execstart,execstop,E,lambda d:d.update(command=['python3','unexecuted.py']))
section('contradictory native working-directory alias',execstart,execstop,E,lambda d:d.update(working_directory='/tmp/wrong-workdir'))
section('contradictory native cwd alias',execstart,execstop,E,lambda d:d.update(cwd='/tmp/wrong-workdir'))
for n,h in protected.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h
report={'status':'passed_author_full_code_and_genuine27_native_prewrite_guard_fixtures','helper':{'file':str(p),'sha256':hashlib.sha256(helper_bytes).hexdigest()},'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Foundations recovery28 author','fixture_count':len(results),'fixtures':results,'errors':[],'production_writer_executed':False,'genuine27_native_positive':True,'independent_peer_approval':False,'protected_original_bytes_unchanged_sha256':protected,'scope':'Entire actual pre-write code plus exact guard segment mutations on genuine27 native schema/evidence. Author verification only; independent review remains required. No production writer/Lean/source/owner/Git mutations.'}
out=Path('/tmp/documentation27-independent-foundations-genuine-native-'+version+'.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'review':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'fixture_count':len(results)}))
