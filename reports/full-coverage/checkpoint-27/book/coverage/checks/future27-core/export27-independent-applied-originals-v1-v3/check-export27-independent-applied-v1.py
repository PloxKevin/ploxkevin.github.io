from pathlib import Path
import ast, copy, hashlib, json, tempfile, types
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/export_audit27_v1.py'
OUT=Path('/tmp/export27-independent-applied-check-result-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
tree=ast.parse(HELPER.read_text());body=tree.body
start=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='snapshot' for t in n.targets))
stop=next(i for i,n in enumerate(body[start:],start) if isinstance(n,ast.Expr) and ast.unparse(n)=='output.mkdir()')
guards=copy.deepcopy(body[start:stop])
with tempfile.TemporaryDirectory(prefix='independent-export27-guard-fixtures-') as tmp:
    fixture=Path(tmp);snapshot=fixture/'reports/full-coverage/checkpoint-27';original=snapshot/'reports/lean-verification';original.mkdir(parents=True)
    source=snapshot/'verification/lean/SafeLearning/Fixture.lean';source.parent.mkdir(parents=True);source.write_text('-- synthetic guard fixture; no compiled proof claim\n')
    manifestpath=snapshot.parent/'checkpoint-27-manifest.json';reportpath=original/'verification.json'
    source_name='verification/lean/SafeLearning/Fixture.lean';oldh=sha(source)
    native={'status':'passed','checks':[{'exit_code':0,'command':['synthetic-fixture-only']}],'proof_sha256':{source_name:oldh},'source_sha256':{},'project_sha256':{},'proof_file_count':1,'theorem_count':1}
    manifest={'proof_files':{source_name:{'sha256':oldh,'historical_body':{'warning':'original actual warning','exit_code':1}}},'status':'frozen_partial_fixture_only'}
    def guard(report=None,m=None):
        reportpath.write_text(json.dumps(native if report is None else report));manifestpath.write_text(json.dumps(manifest if m is None else m))
        env={'ROOT':fixture,'args':types.SimpleNamespace(snapshot=Path('reports/full-coverage/checkpoint-27'),output=Path('reports/full-coverage/lean-checkpoint-27')),'Path':Path,'json':json,'sha':sha}
        exec(compile(ast.Module(body=copy.deepcopy(guards),type_ignores=[]),str(HELPER)+'::<prewrite-guards>','exec'),env)
        assert not (fixture/'reports/full-coverage/lean-checkpoint-27').exists()
    guard()
    empty=copy.deepcopy(native);empty['checks']=[];guard(empty)
    source.write_text('-- changed frozen proof; synthetic fixture only\n');changedh=sha(source)
    changed=copy.deepcopy(native);changed['proof_sha256'][source_name]=changedh;guard(changed)
    findings=['Passed-status synthetic report with an empty check list is accepted before output creation.','Changed frozen proof plus a matching audited proof SHA is accepted while the frozen manifest still pins its original SHA; only key sets are compared.']
result={'status':'passed_read_only_export27_guard_counterexample_checker','errors':[],'helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':sha(HELPER)},'requires_changes':findings,'actual_snapshot_or_export_touched':False,'synthetic_guard_blocks_only':True,'full_helper_executed':False,'scope':'Full source/delta read and two isolated exact prewrite-guard counterexamples. No actual27 aggregate/audit/export assertion or Root/PUB write.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'requires_changes':findings,'result':str(OUT),'sha256':sha(OUT)}))
