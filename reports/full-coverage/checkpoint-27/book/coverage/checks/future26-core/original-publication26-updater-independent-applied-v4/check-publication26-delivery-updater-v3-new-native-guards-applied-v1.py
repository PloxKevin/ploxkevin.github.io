from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');P=R/'book/coverage/checks/root_update_publication26_delivery_progress_v3.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();s=P.read_text();assert H(P)=='e2c94e169d4b5ffc105b725c488f30c5dcb10ec50397636994a711f0cad57784';nodes=ast.parse(s).body
start=next(i for i,n in enumerate(nodes)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='failed_name'for t in n.targets))
end=next(i for i,n in enumerate(nodes)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='progress_path'for t in n.targets))
code=compile(ast.Module(body=nodes[start:end],type_ignores=[]),'isolated-v3-failed-live-native-gates','exec')
reports=R/'reports/full-coverage';failed=json.loads((reports/'live26-attempt1-execution-v1.json').read_text());live=json.loads((reports/'live-checkpoint-26-attempt1.json').read_text());rows=[]
def run(label,mutate,want):
 f=copy.deepcopy(failed);l=copy.deepcopy(live);mutate(f,l)
 scope={'REPORTS':reports,'commit':live['commit'],'read':lambda p:copy.deepcopy(f if p.name=='live26-attempt1-execution-v1.json' else l),'safe':lambda p:R/p,'sha':H}
 ok=True
 try:exec(code,scope,scope)
 except (AssertionError,KeyError,ValueError):ok=False
 assert ok==want,(label,ok,want)
 rows.append({'fixture':label,'accepted':ok,'synthetic_isolated_copy':True})
run('actual first native24 matched plus7DNS accepted',lambda f,l:None,True)
run('boolean actual failure rejected',lambda f,l:f.update(actual_exit_code=True),False)
run('wrong raw log hash rejected',lambda f,l:f.update(log_sha256='b'*64),False)
run('wrong first commit rejected',lambda f,l:l.update(commit='other'),False)
run('wrong match count rejected',lambda f,l:l['assets'][0].update(matches=False,error='Temporary failure in name resolution'),False)
run('conflicting extra exit alias currently accepted',lambda f,l:f.update(exit_code=0),True)
run('changed expected hash currently accepted',lambda f,l:l['assets'][0].update(expected_sha256='b'*64),True)
run('changed actual matched hash currently accepted',lambda f,l:l['assets'][0].update(actual_sha256='b'*64),True)
run('duplicate first source currently accepted',lambda f,l:l['assets'][-1].update(source=l['assets'][0]['source']),True)
run('matched HTTP404 currently accepted',lambda f,l:l['assets'][0].update(http_status=404),True)
assert s.index("failed_name='live26-attempt1-execution-v1.json'")<s.index('shutil.copyfile(source,target)')<s.index('progress_path.write_text')
p=Path('/tmp/publication26-delivery-updater-v3-independent-applied-requires-changes-observation-v1.json');assert not p.exists()
p.write_text(json.dumps({'status':'requires_changes_independent_code_native_guard_observation','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(P.relative_to(R)),'sha256':H(P)},'helper_sha256':H(P),'entire_helper_body':s,'full_code_read':True,'whole_prior_v1_peer':json.loads((R/'book/coverage/checks/future26-core/publication26-delivery-updater-independent-applied-review-v1.json').read_text()),'fixtures':rows,'findings':['The actual first native bytes are good, but the failed wrapper gate ignores conflicting present exit aliases.','The first native31 row gate accepts altered expected/actual hashes, duplicate source or HTTP404 under a truthy matched row. New version should bind the first source/hash map to frozen assets and24 genuinely matched HTTP200 rows/7strict False DNS failures before writes.','Successful retry wrapper should bind exact attempt2 command.'],'actual_scope':'Read-only helper code and isolated synthetic copies only. No producer execution, progress/README/backup/PUB/Git/owner write. Existing v3 held unchanged; fixture pass is diagnostic completion, not helper approval.'},indent=2)+'\n')
print(json.dumps({'observation':str(p),'sha256':H(p),'fixture_count':len(rows)}))
