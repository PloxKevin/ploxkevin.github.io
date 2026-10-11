from pathlib import Path
from datetime import datetime,timezone
import ast,copy,json,hashlib,subprocess
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
n='book/coverage/checks/close_root_checkpoint26_delivery_originals_v2.py';assert H(R/n)=='6de6ca53709605b48b30956078043e15c8e24af6609f14e75c90c272f197097e'
t=ast.parse((R/n).read_text());main=next(x for x in t.body if isinstance(x,ast.FunctionDef) and x.name=='main')
stop=next(i for i,x in enumerate(main.body) if isinstance(x,ast.For) and 'target.open' in ast.unparse(x));body=copy.deepcopy(main.body[:stop])
ns={'ROOT':R,'REPORTS':R/'reports/full-coverage','BASE':R/'book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2','ACTIVE':'close-checkpoint26-delivery-originals-execution-v2','Path':Path,'datetime':datetime,'timezone':timezone,'hashlib':hashlib,'json':json,'subprocess':subprocess}
funcs=[x for x in t.body if isinstance(x,ast.FunctionDef) and x.name!='main'];exec(compile(ast.Module(body=funcs,type_ignores=[]),n,'exec'),ns)
assert not any(isinstance(x,ast.Call) and ast.unparse(x.func) in ('shutil.copyfile','shutil.copytree') for node in body for x in ast.walk(node))
exec(compile(ast.fix_missing_locations(ast.Module(body=body,type_ignores=[])),n,'exec'),ns)
assert ns['commits']=={2:'68fa8a62c5085c3dbc92ec6c80e5dfd9f3e2e381',3:'585972c26d42542f2c47f71940f33721c7230c26'}
priorpath=Path('/tmp/root-checkpoint26-delivery-closer2-independent-foundations-code-review-v1.json');prior=json.loads(priorpath.read_text());assert 'passed' in prior['status'] and prior['errors']==[]
originals=ns['originals'];assert len(originals)>100
assert not any(Path(p).stem==ns['ACTIVE'] for p in originals)
for p,h in originals.items():assert H(R/p)==h
for p,h in ns['protected'].items():assert H(R/p)==h
p=Path('/tmp/root-checkpoint26-delivery-closer2-actual-two-deliveries-independent-foundations-review-v2.json');assert not p.exists()
d={'status':'independent_full_closer2_code_fixtures_and_actual_both_delivery_prewrite_guards_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':n,'sha256':H(R/n)},'helper_sha256':H(R/n),'original_full_code_review':{'file':str(priorpath),'sha256':H(priorpath)},'entire_original_code_review_body_and_time':prior,'actual_read_only_prewrite_guards_executed_to_before_first_copy':True,'content_commit':ns['commits'][2],'metadata_commit':ns['commits'][3],'both_actual_Pages_runs_and_all31_live_hashes_passed':True,'original_closed_root_file_count':len(originals),'all_original_file_hashes_checked_read_only':originals,'protected_selected1167_current31_owners5_count':len(ns['protected']),'scope':'Read-only actual both-deliveries/native eligibility check plus preserved earlier full-code/focused guards. Producer copying/archive construction, closer execution, current source/owner changes and Git are not executed.'}
p.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'status':'passed','peer':str(p),'sha256':H(p),'closed_root_files':len(originals)}))
