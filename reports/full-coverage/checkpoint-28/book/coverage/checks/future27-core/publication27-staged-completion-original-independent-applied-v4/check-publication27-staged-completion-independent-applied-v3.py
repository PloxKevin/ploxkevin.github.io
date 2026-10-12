from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,tempfile,types
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/checks/root_finish_staged_publication27_v3.py'
OUT=Path('/tmp/publication27-staged-completion-independent-applied-observations-v3.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HELPER)=='45bc1de38662afd34699feb327eb3177e2f30127e06be44b875d9c6f43905e47'
source=HELPER.read_text();tree=ast.parse(source);old=ROOT/'book/coverage/checks/root_finish_staged_publication27_v2.py';oldsource=old.read_text();oldtree=ast.parse(oldsource)
new_start=source.index("    assert sha(safe(FAILED)) ==")
new_end=source.index("    assert type(failed['actual_exit_code'])")
assert source[:new_start]+source[new_end:]==oldsource.replace('root_finish_staged_publication27_v2.py','root_finish_staged_publication27_v3.py')
for name in ['safe','sha','read','git','staged','index_exact']:
 def f(t):return next(x for x in t.body if isinstance(x,ast.FunctionDef) and x.name==name)
 assert ast.dump(f(tree),include_attributes=False)==ast.dump(f(oldtree),include_attributes=False),name
ns={'__name__':'independent_read_only_review','__file__':str(HELPER)};exec(compile(source,str(HELPER),'exec'),ns)
main=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='main')
fixtures=[]
def accept(label,fn):fn();fixtures.append({'fixture':label,'result':'accepted'})
def reject(label,fn):
 try:fn()
 except (AssertionError,KeyError,FileNotFoundError,ValueError,TypeError):fixtures.append({'fixture':label,'result':'rejected'});return
 raise AssertionError('unexpected acceptance: '+label)
def exact_block(statements,namespace):
 t=ast.Module(body=copy.deepcopy(statements),type_ignores=[]);exec(compile(ast.fix_missing_locations(t),str(HELPER),'exec'),namespace)
prepared_loop=next(x for x in main.body if isinstance(x,ast.For) and ast.unparse(x.target)=='n' and ast.unparse(x.iter)=='prepared')
proof_loop=next(x for x in main.body if isinstance(x,ast.For) and ast.unparse(x.target)=='(n, row)' and "manifest['proof_files']" in ast.unparse(x.iter))
owner_loop=next(x for x in main.body if isinstance(x,ast.For) and ast.unparse(x.target)=='owner')
exit_assert=next(x for x in main.body if isinstance(x,ast.Assert) and "type(failed['actual_exit_code'])" in ast.unparse(x.test))
allowed_assert=next(x for x in main.body if isinstance(x,ast.Assert) and "set(native['staged_paths'])" in ast.unparse(x.test))
with tempfile.TemporaryDirectory(prefix='completion27-pure-guards-') as td:
 root=Path(td)/'root';pub=Path(td)/'pub';root.mkdir();pub.mkdir();ns['ROOT']=root;ns['PUB']=pub
 # safe's default argument intentionally remains actual ROOT; these fixtures supply base explicitly.
 def put(n,b,base=root):p=base/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p
 ns['safe']=lambda n,base=root: original_safe(n,base)
 original_safe=exec_ns_safe=globals().get('_unused')
 # Extracted exact safe function is recreated so its default is the synthetic ROOT.
 exact_block([next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='safe')],ns)
 accept('canonical relative safe path',lambda:ns['safe']('book/coverage/checks/a.json'))
 for n in ['/tmp/absolute','../escape','book/../escape','./dot','a//b','a\nb','a\rb','a\0b','a*.json','a?.json','a[0].json']:
  reject('unsafe path '+repr(n),lambda n=n:ns['safe'](n))
 live='SafeLearning/probe.html';original=b'<p>exact frozen source</p>\n';put(live,original);put(live,original,pub);h=sha(root/live)
 ns.update(prepared=[live],overrides={'book/coverage/progress.json','reports/full-coverage/README.md'},frozen={live:h},native={'additional_closed_paths_sha256':{}})
 accept('already prepared frozen HTML exact bytes',lambda:exact_block([prepared_loop],ns))
 put(live,b'<p>changed live HTML staged identically</p>\n',pub)
 reject('matching changed PUB/index HTML cannot bypass frozen SHA',lambda:exact_block([prepared_loop],ns));put(live,original,pub)
 pruned='book/coverage/applied.json';put(pruned,b'raw unpruned working owner\n');put(pruned,b'frozen pruned published owner\n',pub);ph=sha(pub/pruned)
 ns.update(prepared=[pruned],frozen={pruned:ph})
 accept('published Applied verified against exact frozen pruned SHA',lambda:exact_block([prepared_loop],ns))
 put(pruned,(root/pruned).read_bytes(),pub);reject('raw unpruned Applied cannot overwrite published frozen owner',lambda:exact_block([prepared_loop],ns));put(pruned,b'frozen pruned published owner\n',pub)
 doc='book/coverage/progress.json';put(doc,b'new truthful delivery-pending progress\n');put(doc,(root/doc).read_bytes(),pub);dh=sha(root/doc)
 ns.update(prepared=[doc],frozen={doc:'0'*64},native={'additional_closed_paths_sha256':{doc:dh}})
 accept('only designated document override uses exact supplemental SHA',lambda:exact_block([prepared_loop],ns))
 put(doc,b'stale document\n',pub);reject('document override wrong bytes',lambda:exact_block([prepared_loop],ns));put(doc,(root/doc).read_bytes(),pub)
 extra='reports/full-coverage/exact-external.json';put(extra,b'exact actual external\n');put(extra,(root/extra).read_bytes(),pub);ns.update(prepared=[extra],frozen={})
 accept('derived external prepared path matches exact Root bytes',lambda:exact_block([prepared_loop],ns))
 put(extra,b'altered external\n',pub);reject('derived external PUB drift',lambda:exact_block([prepared_loop],ns));put(extra,(root/extra).read_bytes(),pub)
 proof='verification/lean/SafeLearning/Probe.lean';put(proof,b'theorem fixture : True := by trivial\n');put(proof,(root/proof).read_bytes(),pub);proofh=sha(root/proof);ns['manifest']={'proof_files':{proof:{'sha256':proofh}}}
 accept('selected proof exact Root and PUB source bytes',lambda:exact_block([proof_loop],ns));put(proof,b'changed selected proof\n',pub);reject('selected proof PUB hash drift',lambda:exact_block([proof_loop],ns));put(proof,(root/proof).read_bytes(),pub);put(proof,b'changed Root selected proof\n');reject('selected proof Root hash drift',lambda:exact_block([proof_loop],ns));put(proof,b'theorem fixture : True := by trivial\n')
 owners={}
 for owner in ('core','foundations','applied','modules','applied-promotions'):
  n='book/coverage/'+owner+'.json';put(n,('exact '+owner+'\n').encode());owners[n]=sha(root/n)
 ns['manifest']={'working_inputs_sha256':owners};accept('all five working owners bound to manifest exact SHA',lambda:exact_block([owner_loop],ns));put('book/coverage/applied.json',b'changed owner\n');reject('working Applied drift rejected separately from published prune',lambda:exact_block([owner_loop],ns))
 for code in [1,False,True,0,2,'1',None]:
  ns['failed']={'actual_exit_code':code};fn=lambda:exact_block([exit_assert],ns)
  (accept if type(code)is int and code==1 else reject)('original failed actual strict exit '+repr(code),fn)
 ns.update(prepared=['prepared/a'],NATIVE='native.json',native={'staged_paths':['prepared/a','supplement/b','_config.yml','native.json'],'additional_closed_paths_sha256':{'supplement/b':'0'*64}})
 accept('allowed whitelist is exact prepared+supplement+config+native union',lambda:exact_block([allowed_assert],ns));ns['native']['staged_paths'].append('rogue/file');reject('extra native allowed path',lambda:exact_block([allowed_assert],ns));ns['native']['staged_paths'].remove('rogue/file');ns['native']['staged_paths'].remove('prepared/a');reject('missing required prepared allowed path',lambda:exact_block([allowed_assert],ns))
 # Exact index verifier, purely synthetic Git-output fixtures. Never calls Git mutation.
 n='fixtures/staged.txt';put(n,b'exact staged bytes\n',pub);oid=hashlib.sha1(b'blob '+str((pub/n).stat().st_size).encode()+b'\0'+(pub/n).read_bytes()).hexdigest();mode=b'100644';stage=b'0';returned_oid=oid
 def fakegit(args,data=None,check=True):
  if args==['ls-files','--stage','-z']:return types.SimpleNamespace(stdout=mode+b' '+returned_oid.encode()+b' '+stage+b'\t'+n.encode()+b'\0')
  if args==['hash-object','--stdin-paths','--no-filters']:
   assert data==(str(pub/n)+'\n').encode();return types.SimpleNamespace(stdout=(oid+'\n').encode())
  raise AssertionError(args)
 ns['git']=fakegit;accept('staged index uses literal unfiltered Git blob bytes',lambda:ns['index_exact']({n}));returned_oid='0'*40;reject('staged index stale blob',lambda:ns['index_exact']({n}));returned_oid=oid;mode=b'120000';reject('staged symlink index mode',lambda:ns['index_exact']({n}));mode=b'100644';stage=b'2';reject('unmerged index stage',lambda:ns['index_exact']({n}));stage=b'0';(pub/n).unlink();(pub/n).symlink_to(pub/live);reject('staged filesystem symlink',lambda:ns['index_exact']({n}))
# Load exact original module again so all default arguments/read-only Git cwd return to real ROOT/PUB.
real={'__name__':'independent_read_only_prefix','__file__':str(HELPER)};exec(compile(source,str(HELPER),'exec'),real)
# Run ONLY original main statements before review/body/copy/staging. Exact read-only native/prepared/index/99-archive checks.
first_assert=next(i for i,x in enumerate(main.body) if isinstance(x,ast.Assert))
review_i=next(i for i,x in enumerate(main.body) if isinstance(x,ast.Assign) and ast.unparse(x.targets[0])=='review')
prefix=ast.Module(body=copy.deepcopy(main.body[first_assert:review_i]),type_ignores=[])
exec(compile(ast.fix_missing_locations(prefix),str(HELPER),'exec'),real)
assert len(real['violations'])==99 and sum(map(len,real['violations'].values()))==389
assert not (ROOT/real['REPORT']).exists() and not (real['PUB']/real['REPORT']).exists()
result={'status':'passed_independent_full_checkpoint27_staged_completion_code_and_read_only_prefix_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'fixture_count':len(fixtures),'fixtures':fixtures,'exact_v3_to_v2_reverse':True,'prior_v2_finding':{'file':'/tmp/publication27-completion-v2-index-frozen-guard-observation-v1.json','sha256':sha(Path('/tmp/publication27-completion-v2-index-frozen-guard-observation-v1.json'))},'original_v1_helper':{'file':str(ROOT/'book/coverage/checks/root_finish_staged_publication27_v1.py'),'sha256':sha(ROOT/'book/coverage/checks/root_finish_staged_publication27_v1.py')},'original_v2_helper':{'file':str(old),'sha256':sha(old)},'actual_read_only_main_prefix':{'staged_index_blobs':len(real['names']),'allowed_paths':len(real['allowed']),'frozen_inputs':len(real['frozen']),'selected_sources':len(real['manifest']['proof_files']),'all_already_prepared_paths':len(real['prepared']),'exact_archival_files':len(real['violations']),'exact_original_diagnostics':sum(map(len,real['violations'].values())),'actual_scoped_lint_exit_code':0,'original_failed_stage_exit_code':real['failed']['actual_exit_code'],'original_failed_stage':{'file':real['FAILED'],'sha256':sha(ROOT/real['FAILED'])},'native_pre_stage':{'file':real['NATIVE'],'sha256':sha(ROOT/real['NATIVE'])}},'scope':'Full source/delta and exact-function TMP fixtures plus exact main pre-review/pre-copy read-only native/frozen/prepared/current/index/lint prefix. All 99 immutable archival SHA/389 original diagnostics bound. Final added failed-stage log is the sole 100th literal lint exception. No production main, copies, staging, commit, push, Pages or delivery claim.'}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixture_count':len(fixtures),'observations':str(OUT),'sha256':sha(OUT),'actual_prefix_staged_index_blobs':len(real['names']),'actual_archival_files':len(real['violations'])}))
