from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');OLD=R/'book/coverage/checks/root_prepare_browser26_v1.py';NEW=R/'book/coverage/checks/root_prepare_browser26_v2.py';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(NEW)=='b71fd49a7d5fe7ede6149a4ed8e1e2d4f2680036f9fb7f6507f42fea90ba19ab'
s=NEW.read_text();old=OLD.read_text();start=s.index("manual_name = ");end=s.index('artifact_dir.mkdir()',start);block=s[start:end];normblock=block.replace("assert sha(ROOT/manual_name) == '44e380bda0d0c0a6945c7980eca2d15da069b027280dd2144a48082d29620719'\n",'').replace("assert len(manual['inspected_captures']) == 6\n",'').replace("assert len({c['path'] for c in manual['inspected_captures']}) == 6\n",'');back=s[:start]+s[end:];back=back.replace('output.write_text(',normblock+'output.write_text(',1);assert ast.dump(ast.parse(back))==ast.dump(ast.parse(old))
tree=ast.parse(s);stop=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and ast.unparse(n.value.func)=='artifact_dir.mkdir');prefix=tree.body[:stop];split=next(i for i,n in enumerate(prefix)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Tuple)for t in n.targets));header=prefix[:split];body=prefix[split:]
# All producer writes lie after the native-read/guard prefix executed below.
assert not any(isinstance(n,ast.Call)and ast.unparse(n.func).endswith(('.mkdir','.write_text','.copyfile'))for n in ast.walk(ast.Module(body=prefix,type_ignores=[])))
paths=['reports/full-coverage/browser-source53-26-v1-execution.json','reports/full-coverage/browser-checkpoint-25.json','reports/full-coverage/browser-source53-26-v1.json','reports/full-coverage/source53-six-paragraph-content-manual-review26-v1.json'];native={p:json.loads((R/p).read_text())for p in paths};original=native[paths[1]]['original_browser_report']['file'];native[original]=json.loads((R/original).read_text())
results=[]
def trial(name,mut=None,accept=False,sha_mut=None):
 inputs=copy.deepcopy(native)
 if mut:mut(inputs)
 ns={'__file__':str(NEW)};exec(compile(ast.Module(body=header,type_ignores=[]),str(NEW),'exec'),ns);native_sha=ns['sha'];ns['read']=lambda n:copy.deepcopy(inputs[n]);ns['sha']=lambda p:sha_mut(p,native_sha)if sha_mut else native_sha(p)
 try:exec(compile(ast.Module(body=body,type_ignores=[]),str(NEW),'exec'),ns);passed=True
 except (AssertionError,KeyError,TypeError):passed=False
 assert passed==accept,(name,passed,accept);results.append({'fixture':name,'expected_accept':accept,'actual_accept':passed,'scope':'Native read-only prefix with isolated in-memory mutation; no output writes.'});return ns
n=trial('entire genuine native contract',accept=True);assert len(n['pages'])==29 and len(n['screenshots'])==48 and n['skipped']==10
fresh=paths[2];ex=paths[0];oldp=paths[1];manual=paths[3]
trial('bool exit rejected',lambda d:d[ex].update(actual_exit_code=False))
trial('nonzero actual rejected',lambda d:d[ex].update(actual_exit_code=1))
trial('wrong execution status',lambda d:d[ex].update(status='pending'))
trial('fresh hash mismatch',lambda d:d[ex].update(report_sha256='0'*64))
trial('changed before-after map',lambda d:d[ex]['source_sha256_after'].update({'SafeLearning/nn-in-the-loop.html':'0'*64}))
trial('old fresh inference rejected',lambda d:d[oldp].update(fresh_verified_viewport_count=145))
trial('old retained count rejected',lambda d:d[oldp].update(retained_verified_viewport_count=140))
trial('qa hash mismatch',lambda d:d[oldp]['qa_source_sha256'].update({'qa/learning_review.mjs':'0'*64}))
trial('wrong changed page',lambda d:d[fresh][0].update(file='verification.html'))
trial('fresh status rejected',lambda d:d[fresh][0].update(status='failed'))
trial('page errors rejected',lambda d:d[fresh][0].update(errors=['clip']))
trial('width missing rejected',lambda d:d[fresh][0]['viewports'].pop())
trial('clipped rejected',lambda d:d[fresh][0]['viewports'][0].update(clipped=True))
trial('document overflow rejected',lambda d:d[fresh][0]['viewports'][0].update(documentWidth=9999))
trial('wrong page source rejected',lambda d:d[fresh][0].update(source_sha256='0'*64))
trial('full-path page qa rejected',lambda d:d[fresh][0].update(qa_source_sha256=d[ex]['qa_source_sha256']))
trial('bad screenshot source rejected',lambda d:d[fresh][0]['screenshots'][0].update(source_sha256='0'*64))
trial('bad screenshot bytes rejected',lambda d:d[fresh][0]['screenshots'][0].update(sha256='0'*64))
trial('manual five rejected',lambda d:d[manual]['inspected_captures'].pop())
trial('duplicate manual capture rejected',lambda d:d[manual]['inspected_captures'].__setitem__(1,d[manual]['inspected_captures'][0]))
trial('manual whole status rejected',lambda d:d[manual].update(status='passed_all_48'))
trial('wrong manual source rejected',lambda d:d[manual].update(source_sha256='0'*64))
trial('manual bytes rejected',lambda d:d[manual]['inspected_captures'][0].update(sha256='0'*64))
trial('manual report hash rejected',sha_mut=lambda p,f:'0'*64 if str(p).endswith(manual)else f(p))
assert not (R/'reports/full-coverage/browser-checkpoint-26.json').exists()and not(R/'reports/full-coverage/browser-artifacts-26').exists()
out={'status':'passed_independent_browser26_preparation_full_and_narrow_guard_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(NEW.relative_to(R)),'sha256':H(NEW)},'helper_sha256':H(NEW),'original_unexecuted_v1_helper':{'file':str(OLD.relative_to(R)),'sha256':H(OLD)},'original_v1_code_read_finding':'Manual report guard occurred after copies/input write; v2 moves it entirely before writes and pins the exact existing six-capture report. V1 was never executed by this reviewer.','exact_AST_inverse_recovers_original_v1':True,'native_contract':{'pages':29,'fresh_viewports':5,'retained_viewports':140,'screenshots':48,'skipped':10,'scoped_manual_captures':6,'whole48_manual_review_remains_pending':True},'native_evidence_sha256':{p:H(R/p)for p in native},'fixtures':results,'fixture_count':len(results),'scope':'Read-only full code/delta and actual native guard-prefix validation plus isolated reject fixtures. No producer/browser/PUB execution or mathematical/whole-site manual approval inferred.'}
p=Path('/tmp/browser26-preparation-independent-modules-code-review-v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(p),'sha256':H(p),'fixture_count':len(results)}))
