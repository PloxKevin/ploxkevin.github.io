from pathlib import Path
import ast, copy, hashlib, json, tempfile, types
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/export_audit27_v3.py'
OUT=Path('/tmp/export27-independent-applied-check-result-v3.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
tree=ast.parse(HELPER.read_text());body=tree.body
start=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='snapshot' for t in n.targets))
stop=next(i for i,n in enumerate(body[start:],start) if isinstance(n,ast.Expr) and ast.unparse(n)=='output.mkdir()')
guards=copy.deepcopy(body[start:stop]);fixtures=[]
def reject(name,f):
    try:f()
    except (AssertionError,KeyError,TypeError,ValueError,FileNotFoundError):fixtures.append({'fixture':name,'result':'rejected'});return
    raise AssertionError('unexpected acceptance '+name)
with tempfile.TemporaryDirectory(prefix='independent-export27-strict-fixtures-') as tmp:
    fixture=Path(tmp);snapshot=fixture/'reports/full-coverage/checkpoint-27';original=snapshot/'reports/lean-verification';original.mkdir(parents=True)
    source_dir=snapshot/'verification/lean/SafeLearning';source_dir.mkdir(parents=True)
    proof_map={}
    for i in range(1175):
        p=source_dir/('SyntheticGuardFixture'+str(i)+'.lean');p.write_bytes(b'-- guard fixture only; no proof/compilation claim\n')
        proof_map[str(p.relative_to(snapshot))]=sha(p)
    manifestpath=snapshot.parent/'checkpoint-27-manifest.json';reportpath=original/'verification.json'
    native={'status':'passed','checks':[{'exit_code':0,'command':['synthetic-fixture-only'],'original_check':{'output_file':'reports/lean-verification/old-check.log','started_at_utc':'historical-time'}}],'proof_sha256':proof_map,'source_sha256':{},'project_sha256':{},'proof_file_count':1175,'theorem_count':9644}
    manifest={'proof_files':{n:{'sha256':h,'history':{'warning':'original actual warning','exit_code':1,'literal':'μ ≤ α'}} for n,h in proof_map.items()},'status':'frozen_partial_fixture_only'}
    def guard(report=None,m=None,snapshotarg='reports/full-coverage/checkpoint-27',outputarg='reports/full-coverage/lean-checkpoint-27'):
        reportpath.write_text(json.dumps(native if report is None else report));manifestpath.write_text(json.dumps(manifest if m is None else m))
        env={'ROOT':fixture,'args':types.SimpleNamespace(snapshot=Path(snapshotarg),output=Path(outputarg)),'Path':Path,'json':json,'sha':sha}
        exec(compile(ast.Module(body=copy.deepcopy(guards),type_ignores=[]),str(HELPER)+'::<prewrite-guards>','exec'),env)
        assert not (fixture/'reports/full-coverage/lean-checkpoint-27').exists()
    guard();fixtures.append({'fixture':'1175 exact proof hashes and nonempty strict-zero native checks','result':'accepted'})
    for name,value in [('empty-checks',[]),('wrong-checks-type',{}),('bool-false-exit',[{'exit_code':False}]),('float-zero-exit',[{'exit_code':0.0}]),('native-failure',[{'exit_code':1}]),('missing-exit',[{}])]:
        changed=copy.deepcopy(native);changed['checks']=value;reject(name,lambda d=changed:guard(d))
    for name,field,value in [('wrong-status','status','partial'),('wrong-proof-count','proof_file_count',1174),('wrong-theorem-count','theorem_count',9643)]:
        changed=copy.deepcopy(native);changed[field]=value;reject(name,lambda d=changed:guard(d))
    first=next(iter(proof_map));changed=copy.deepcopy(native);changed['proof_sha256'][first]='0'*64
    reject('audited hash disagrees with frozen manifest',lambda:guard(changed))
    small=copy.deepcopy(native);small['proof_sha256']={first:proof_map[first]};smallmanifest=copy.deepcopy(manifest);smallmanifest['proof_files']={first:manifest['proof_files'][first]}
    reject('fabricated1175 header on one-entry proof maps',lambda:guard(small,smallmanifest))
    source=snapshot/first;source.write_bytes(b'-- changed input after audit\n')
    changed=copy.deepcopy(native);changed['proof_sha256'][first]=sha(source)
    reject('changed proof plus report hash cannot replace frozen manifest hash',lambda:guard(changed))
    reject('changed input with original audit hash',lambda:guard())
    source.write_bytes(b'-- guard fixture only; no proof/compilation claim\n')
    reject('wrong snapshot path',lambda:guard(snapshotarg='reports/full-coverage/checkpoint-26'))
    reject('wrong output path',lambda:guard(outputarg='reports/full-coverage/lean-checkpoint-26'))
    output=fixture/'reports/full-coverage/lean-checkpoint-27';output.mkdir()
    reject('existing output cannot be overwritten',guard);output.rmdir()

    # Execute only the path-relocation function, preserving historical originals.
    fn=next(n for n in body if isinstance(n,ast.FunctionDef) and n.name=='relocate_check')
    env={'old_prefix':'reports/lean-verification/','new_prefix':'reports/full-coverage/lean-checkpoint-27/'}
    exec(compile(ast.Module(body=[copy.deepcopy(fn)],type_ignores=[]),'<exact-relocation-function>','exec'),env)
    historical={'actual_command':['lake','env','lean','SafeLearning/Historical.lean'],'started_at_utc':'historical-time','exit_code':1,'output_file':'reports/lean-verification/historical-original.log'}
    row={'output_file':'reports/lean-verification/current.log','original_check':copy.deepcopy(historical),'reused_from':{'report':'reports/lean-verification/verification.json','original_check':copy.deepcopy(historical)}}
    env['relocate_check'](row)
    assert row['output_file']=='reports/full-coverage/lean-checkpoint-27/current.log'
    assert row['reused_from']['report']=='reports/full-coverage/lean-checkpoint-27/verification.json'
    assert row['original_check']==row['reused_from']['original_check']==historical
    fixtures.append({'fixture':'current output/report paths relocate while all historical body/time/exit1 fields remain exact','result':'accepted'})
    # Execute only compact serialization and its size assertion, never its write.
    i=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='manifest_payload' for t in n.targets))
    serialization=copy.deepcopy(body[i:i+2]);assert isinstance(serialization[1],ast.Assert)
    env={'json':json,'manifest':manifest}
    exec(compile(ast.Module(body=serialization,type_ignores=[]),'<exact-compact-manifest-gate>','exec'),env)
    assert json.loads(env['manifest_payload'])==manifest and 'μ'.encode() in env['manifest_payload']
    fixtures.append({'fixture':'compact Unicode serialization preserves complete original manifest object/history','result':'accepted'})
    def oversized():
        class D:
            @staticmethod
            def dumps(*args,**kwargs):return 'x'*100_000_000
        exec(compile(ast.Module(body=serialization,type_ignores=[]),'<exact-size-limit>','exec'),{'json':D,'manifest':{}})
    reject('100MB compact payload is rejected before manifest write',oversized)
assert not (ROOT/'reports/full-coverage/lean-checkpoint-27').exists()
result={'status':'passed_independent_export27_v3_full_code_and_exact_guard_fixture_checker','errors':[],'helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':sha(HELPER)},'fixtures':fixtures,'fixture_count':len(fixtures),'expected_proof_count':1175,'expected_theorem_lemma_count':9644,'original_historical_execution_fields_preserved':True,'compact_manifest_object_equivalence':True,'actual_snapshot_or_export_touched':False,'full_helper_executed':False,'scope':'Full independent source/delta read plus exact prewrite guards, relocation and serialization functions in an isolated synthetic workspace. No actual aggregate, export producer, Root/PUB write or mathematical coverage inference.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixtures':len(fixtures),'result':str(OUT),'sha256':sha(OUT)}))
