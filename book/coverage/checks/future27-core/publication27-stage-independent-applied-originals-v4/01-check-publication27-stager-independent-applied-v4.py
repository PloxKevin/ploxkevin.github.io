from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,tempfile,copy,ast
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_stage_publication27_v4.py');OUT=Path('/tmp/publication27-stager-independent-applied-observations-v4.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HELPER)=='5d676ab3d78cfe7486ee5bc0acef87fa8a7c4ac7caa20a79ccd6a4320af9f562'
old=Path('/tmp/root_stage_publication27_v3.py').read_text();new=HELPER.read_text()
t3=ast.parse(old);t4=ast.parse(new)
def function(tree,name):return next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name==name)
for n in ['safe','actual','zero','dirty','staged','main']:assert ast.dump(function(t3,n),include_attributes=False)==ast.dump(function(t4,n),include_attributes=False),n
p3=copy.deepcopy(function(t3,'prepare'));p4=function(t4,'prepare')
class ExtendArgs(ast.NodeTransformer):
 def visit_Call(self,node):
  self.generic_visit(node)
  if isinstance(node.func,ast.Name) and node.func.id=='closed_peer':
   node.args.extend([ast.Name(id='paths',ctx=ast.Load()),ast.Subscript(value=ast.Name(id='manifest',ctx=ast.Load()),slice=ast.Constant(value='working_inputs_sha256'),ctx=ast.Load())])
  return node
p3=ExtendArgs().visit(p3);assert ast.dump(p3,include_attributes=False)==ast.dump(p4,include_attributes=False)
ns={'__name__':'isolated_peer_guard_fixture','__file__':str(HELPER)};exec(compile(new,str(HELPER),'exec'),ns);fixtures=[]
def reject(label,fn):
 try:fn()
 except (AssertionError,KeyError,FileNotFoundError,ValueError,TypeError):fixtures.append({'fixture':label,'result':'rejected'});return
 raise AssertionError('unexpected acceptance: '+label)
def accept(label,fn):fn();fixtures.append({'fixture':label,'result':'accepted'})
with tempfile.TemporaryDirectory(prefix='publication27-raw-owner-closure-fixtures-') as td:
 r=Path(td)/'root';p=Path(td)/'pub';r.mkdir();p.mkdir();ns['ROOT']=r;ns['PUB']=p
 def put(n,data,base=r):
  f=base/n;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data if isinstance(data,bytes) else json.dumps(data).encode());return f
 peer_n='peer.json';raw_n='book/coverage/applied.json';canon='book/coverage/checks/exact-unpruned-owner-copy.json'
 put(raw_n,b'{"raw_unpruned":"kept three original proof metadata entries"}\n');h=sha(r/raw_n)
 put(raw_n,b'{"published_pruned":"three documented unreferenced entries absent"}\n',p)
 put(canon,(r/raw_n).read_bytes());put(canon,(r/raw_n).read_bytes(),p)
 d={'status':'passed','errors':[],'closed_evidence_sha256':{raw_n:h}};put(peer_n,d)
 aliases={raw_n+'::'+h:{'file':canon,'sha256':h}};working={raw_n:h};expected={};prepared={raw_n,canon}
 fn=lambda a=aliases,e=expected,pr=prepared,w=working:ns['closed_peer'](peer_n,'passed',a,e,pr,w)
 accept('unpruned Applied closure retained at exact prepared canonical body; pruned PUB original untouched',fn)
 assert sha(p/raw_n)!=h and sha(p/canon)==h
 accept('unpruned Applied closure retained through explicit supplemental canonical copy',lambda:fn(e={canon:h},pr={raw_n}))
 reject('missing raw Applied explicit alias',lambda:fn(a={}))
 reject('wrong current working hash',lambda:fn(w={raw_n:'0'*64}))
 reject('raw alias retained equals forbidden raw owner path',lambda:fn(a={raw_n+'::'+h:{'file':raw_n,'sha256':h}}))
 reject('raw alias digest differs from native closure',lambda:fn(a={raw_n+'::'+h:{'file':canon,'sha256':'0'*64}}))
 reject('retained canonical body absent from both prepared and explicit extra',lambda:fn(pr={raw_n}))
 reject('retained alias parent traversal',lambda:fn(a={raw_n+'::'+h:{'file':'../escape.json','sha256':h}}))
 reject('retained alias absolute path',lambda:fn(a={raw_n+'::'+h:{'file':'/tmp/escape.json','sha256':h}}))
 # Current Root evidence drift and stale published copy both reject.
 put(raw_n,b'changed raw owner');reject('raw Root source stale against literal closed hash',fn);put(raw_n,(r/canon).read_bytes())
 put(canon,b'changed retained Root body');reject('canonical retained Root stale',fn);put(canon,(r/raw_n).read_bytes())
 put(canon,b'changed retained PUB body',p);reject('canonical retained PUB stale under prepared-only route',fn);put(canon,(r/raw_n).read_bytes(),p)
 symlink='book/coverage/checks/alias-link.json';(r/symlink).symlink_to(r/canon)
 reject('retained raw alias final symlink',lambda:fn(a={raw_n+'::'+h:{'file':symlink,'sha256':h}},e={symlink:h}));(r/symlink).unlink()
 for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/modules.json','book/coverage/inventory.json','book/coverage/material-corrections.json','other-working.json']:
  put(n,b'unrelated current working bytes');hn=sha(r/n);put(peer_n,{'status':'passed','errors':[],'closed_evidence_sha256':{n:hn}})
  reject('arbitrary current-working bypass rejected '+n,lambda n=n,hn=hn:ns['closed_peer'](peer_n,'passed',{n+'::'+hn:{'file':canon,'sha256':hn}},{},set(),{n:hn}))
  put(n,(r/n).read_bytes(),p);accept('same exact prepared Root/PUB closure accepted '+n,lambda n=n,hn=hn:ns['closed_peer'](peer_n,'passed',{}, {},{n},{}))
 put(peer_n,d)
 reject('passed status alone cannot omit errors',lambda:ns['closed_peer']('missing.json','passed',aliases,{},prepared,working))
 # Absolute originals still require typed path/hash alias and current retained body.
 absolute='/tmp/synthetic-original.json';put(peer_n,{'status':'passed','errors':[],'closed_evidence_sha256':{absolute:h}})
 accept('absolute original through explicit prepared exact canonical copy',lambda:ns['closed_peer'](peer_n,'passed',{absolute+'::'+h:{'file':canon,'sha256':h}}, {},{canon},{}))
 reject('absolute original without typed alias',lambda:ns['closed_peer'](peer_n,'passed',{}, {},{canon},{}))
# Actual native current owner/config/production closure read, using only exact typed catalog aliases and hash-identical prepared candidate. No production prepare/main call.
ns['ROOT']=ROOT;ns['PUB']=ROOT/'reports/book/publication-repo';manifest=ns['read'](ns['MANIFEST']);prepared=set(ns['read']('reports/full-coverage/publication-prepared-27-files.json'))
working=manifest['working_inputs_sha256'];h=working['book/coverage/applied.json'];frozen=manifest['frozen_inputs_sha256'];retained=[n for n,v in frozen.items() if v==h and n!='book/coverage/applied.json'];assert retained
retained=[n for n in retained if n in prepared and ns['safe'](ROOT,n).is_file() and ns['safe'](ns['PUB'],n).is_file() and sha(ns['safe'](ROOT,n))==sha(ns['safe'](ns['PUB'],n))==h];assert retained
raw_alias={'book/coverage/applied.json::'+h:{'file':retained[0],'sha256':h}}
native=[]
for n,status,catalog_name in [
 ('book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json','passed_independent_actual_checkpoint27_pages_configuration',None),
 ('book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json','passed','book/coverage/checks/future27-core/original-independent-module-production-output-peer-v1/original-closed-byte-aliases-v1.json')]:
 d=ns['read'](n);a=d.get('original_closed_byte_aliases')
 if a is None:a=ns['read'](catalog_name)['original_closed_byte_aliases']
 alias=dict(raw_alias);expected={}
 for orig,h1 in d['closed_evidence_sha256'].items():
  if Path(orig).is_absolute():
   row=a[orig];assert row['sha256']==h1;alias[orig+'::'+h1]=row;name=row['file'];expected[name]=h1
  else:
   name=orig
   # Prepared exact references do not need supplement; raw Applied is routed exclusively through retained candidate, never original owner.
   if name not in prepared:expected[name]=h1
 ns['closed_peer'](n,status,alias,expected,prepared,working)
 assert 'book/coverage/applied.json' not in expected
 native.append({'peer':{'file':n,'sha256':sha(ROOT/n)},'closed_references':len(d['closed_evidence_sha256']),'raw_applied_retained_without_copying_published_owner':raw_alias})
for n,c in ns['REQUIRED_EXECUTIONS'].items():ns['actual'](n,c)
prior=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v3.json'
result={'status':'passed_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review','errors':[],'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'fixture_count':len(fixtures),'fixtures':fixtures,'native_peer_closure_reads':native,'native_exact_execution_families':17,'whole_prior_v3_review_body_and_time':json.loads(prior.read_bytes()),'prior_v3_review':{'file':str(prior),'sha256':sha(prior)},'new_semantic_gap_history':'Root pre-production plan construction identified that raw owner closure cannot be staged over its pruned published ledger. Previous v3 guard fixtures and full review remain unchanged; this v4 adds separate retained-byte routing and prepared exact evidence.','producer_execution':False,'production_pub_or_git_mutation':False,'scope':'Whole v4 code/delta read and exact guarded closed_peer() branch fixtures, real output5/production27 evidence and prepared immutable unpruned candidate body checks. Unchanged actual()/safe()/main()/prepare() AST retained apart from two typed closure arguments; entire v3 full prepare synthetic61+33 observations preserved. No real production prepare/main, Git, copy or stager execution.'}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixture_count':len(fixtures),'observations':str(OUT),'sha256':sha(OUT)}))
