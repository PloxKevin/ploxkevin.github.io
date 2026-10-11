from pathlib import Path
import ast,copy,hashlib,json,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/checks/root_prepare_checkpoint27_cache_v1.py';OUT=Path('/tmp/cache27-independent-applied-check-result-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
tree=ast.parse(HELPER.read_text());body=tree.body
start=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='selection_path' for t in n.targets))
stop=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='started' for t in n.targets))
header=copy.deepcopy(body[start:stop]);fixtures=[]
def reject(name,f):
    try:f()
    except (AssertionError,KeyError,TypeError,ValueError,FileNotFoundError):fixtures.append({'fixture':name,'result':'rejected'});return
    raise AssertionError('unexpected acceptance '+name)
with tempfile.TemporaryDirectory(prefix='cache27-readonly-guard-fixtures-') as td:
    fixture=Path(td);reports=fixture/'reports/full-coverage';reports.mkdir(parents=True)
    old={'proof_files':{'verification/lean/SafeLearning/Old'+str(i)+'.lean':{'sha256':'a'*64} for i in range(1167)}}
    selection={'proof_file_count':1175,'new_file_count':8,'proof_files':{**old['proof_files'],**{'verification/lean/SafeLearning/New'+str(i)+'.lean':{'sha256':'b'*64} for i in range(8)}}}
    (reports/'checkpoint-26-selection.json').write_text(json.dumps(old))
    def guard(sel=None,man=None):
        data=selection if sel is None else sel;(reports/'checkpoint-27-selection.json').write_text(json.dumps(data))
        manifest={'selection_sha256':sha(reports/'checkpoint-27-selection.json'),'proof_files':data['proof_files'],'snapshot':'reports/full-coverage/checkpoint-27'} if man is None else man
        (reports/'checkpoint-27-manifest.json').write_text(json.dumps(manifest))
        exec(compile(ast.Module(body=copy.deepcopy(header),type_ignores=[]),'<exact-cache27-prewrite-header>','exec'),{'ROOT':fixture,'Path':Path,'json':json,'sha':sha})
        assert not (reports/'checkpoint27-cache-preparation.json').exists()
    guard();fixtures.append({'fixture':'1175 selected/8 new with all1167 baseline hashes exact','result':'accepted'})
    for label,k,v in [('wrong selected count','proof_file_count',1174),('wrong additions','new_file_count',9)]:
        bad=copy.deepcopy(selection);bad[k]=v;reject(label,lambda d=bad:guard(d))
    bad=copy.deepcopy(selection);bad['proof_files'].pop(next(iter(old['proof_files'])));reject('missing baseline source',lambda:guard(bad))
    bad=copy.deepcopy(selection);bad['proof_files'][next(iter(old['proof_files']))]['sha256']='c'*64;reject('changed inherited source hash',lambda:guard(bad))
    for label,change in [('wrong frozen snapshot',{'snapshot':'reports/full-coverage/checkpoint-26'}),('wrong selection hash',{'selection_sha256':'0'*64}),('manifest proof map mismatch',{'proof_files':old['proof_files']})]:
        (reports/'checkpoint-27-selection.json').write_text(json.dumps(selection));man={'selection_sha256':sha(reports/'checkpoint-27-selection.json'),'proof_files':selection['proof_files'],'snapshot':'reports/full-coverage/checkpoint-27'};man.update(change)
        reject(label,lambda m=man:guard(man=m))
    # Actual per-source routing/hash guard only, without cache copy loops.
    loop=next(n for n in body if isinstance(n,ast.For) and 'selection' in ast.unparse(n.iter))
    source_guard=copy.deepcopy(loop.body[:3]);assert len(source_guard)==3 and isinstance(source_guard[-1],ast.Assert)
    source='verification/lean/SafeLearning/Fixture.lean';baseline=reports/'checkpoint-26';snapshot=reports/'checkpoint-27'
    live=fixture/source;live.parent.mkdir(parents=True);live.write_bytes(b'-- fixture\n')
    frozen=snapshot/source;frozen.parent.mkdir(parents=True);frozen.write_bytes(live.read_bytes());record={'sha256':sha(live)}
    def route():
        env={'source':source,'record':record,'baseline':baseline,'snapshot':snapshot,'ROOT':fixture,'Path':Path,'sha':sha}
        exec(compile(ast.Module(body=copy.deepcopy(source_guard),type_ignores=[]),'<exact-source-cache-routing>','exec'),env);return env['origin']
    assert route()==fixture/'verification/lean';fixtures.append({'fixture':'new source artifact origin is working project after exact frozen/source hash guard','result':'accepted'})
    inherited=baseline/source;inherited.parent.mkdir(parents=True);inherited.write_bytes(live.read_bytes())
    assert route()==baseline/'verification/lean';fixtures.append({'fixture':'inherited source artifact origin is exact baseline snapshot','result':'accepted'})
    inherited.write_bytes(b'-- changed inherited source\n');reject('changed artifact-origin source',route);inherited.write_bytes(live.read_bytes())
    frozen.write_bytes(b'-- changed frozen source\n');reject('changed frozen source',route)
    base=fixture/'artifact-glob';base.mkdir();(base/'Fixture.olean').write_bytes(b'fixture only');(base/'AllProofs.olean').write_bytes(b'aggregate fixture only')
    assert [p.name for p in base.glob('Fixture.*')]==['Fixture.olean'];fixtures.append({'fixture':'per-module artifact glob excludes aggregate artifact','result':'accepted'})
result={'status':'passed_independent_cache27_full_code_delta_and_prewrite_guard_fixture_checker','errors':[],'helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':sha(HELPER)},'fixture_count':len(fixtures),'fixtures':fixtures,'expected_selected_sources':1175,'baseline_sources':1167,'new_sources':8,'cache_copy_executed':False,'actual_root_snapshot_modified':False,'scope':'Full source/delta and isolated exact selection/source-routing guards only. Actual cache-copy execution remains Root-only after freeze0; fresh normal build,8 fresh kernel checks,1167 exact reuse and all9644 axiom checks remain required.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixtures':len(fixtures),'result':str(OUT),'sha256':sha(OUT)}))
