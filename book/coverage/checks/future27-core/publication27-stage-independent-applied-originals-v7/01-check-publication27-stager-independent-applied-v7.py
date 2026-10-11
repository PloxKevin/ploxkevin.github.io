from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/checks/root_stage_publication27_v7.py'
OUT=Path('/tmp/publication27-stager-independent-applied-observations-v7.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HELPER)=='67cc3e1f859993a06fda63d7774e2e6f981f6743ca90afe2a8552235b3c657de'
source=HELPER.read_text();prior_helper=Path('/tmp/root_stage_publication27_v6.py');old=prior_helper.read_text();tree=ast.parse(source);oldtree=ast.parse(old)
def function(t,n):return next(x for x in t.body if isinstance(x,ast.FunctionDef) and x.name==n)
for n in ['safe','read','zero','actual','dirty','staged','prepare','main']:
 assert ast.dump(function(tree,n),include_attributes=False)==ast.dump(function(oldtree,n),include_attributes=False),n
new_block='''  # Closed originals may retain their exact bytes through an explicit typed
  # alias. Current raw Applied bytes remain separate from published pruning.
  assert original==n,n
  if n=='book/coverage/applied.json':assert working[n]==h,n
'''
old_block='''  # The current raw Applied owner is retained separately from its reviewed
  # published metadata pruning. It must never overwrite the publication owner.
  assert original==n=='book/coverage/applied.json' and working[n]==h,n
'''
assert source.count(new_block)==1
assert source.replace('root_stage_publication27_v7.py','root_stage_publication27_v6.py').replace(new_block,old_block)==old
ns={'__name__':'independent_read_only_review','__file__':str(HELPER)};exec(compile(source,str(HELPER),'exec'),ns)
fixtures=[]
def accept(label,fn):fn();fixtures.append({'fixture':label,'result':'accepted'})
def reject(label,fn):
 try:fn()
 except (AssertionError,KeyError,FileNotFoundError,ValueError,TypeError):fixtures.append({'fixture':label,'result':'rejected'});return
 raise AssertionError('unexpected acceptance '+label)
with tempfile.TemporaryDirectory(prefix='publication27-general-alias-review-') as td:
 root=Path(td)/'root';pub=Path(td)/'pub';root.mkdir();pub.mkdir();ns['ROOT']=root;ns['PUB']=pub
 def put(n,b,base=root):
  p=base/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else (json.dumps(b,separators=(',',':'))+'\n').encode());return p
 original='sources/text/hertneck.txt.log';content=b'original exact closed source retrieval log\n';put(original,content);h=sha(root/original)
 retained='book/coverage/checks/future27-core/original-documentation27-foundations-review-v1/additional-exact-closed-reference-bytes27-v1/'+h+'/hertneck.txt.log';put(retained,content)
 peername='fixtures/independent-peer.json';status='passed_native_fixture_only';peer={'status':status,'errors':[],'closed_evidence_sha256':{original:h}};put(peername,peer)
 aliases={original+'::'+h:{'file':retained,'sha256':h}};expected={retained:h};prepared=set();working={}
 run=lambda:ns['closed_peer'](peername,status,aliases,expected,prepared,working)
 accept('relative original exactRoot plus explicit retained supplemental copy',run)
 expected.clear();prepared.add(retained);put(retained,content,pub);accept('relative original exactRoot plus explicit retained alreadyprepared exactPub',run)
 def bad_alias(label,row):
  original_row=copy.deepcopy(aliases[original+'::'+h]);aliases[original+'::'+h]=row;reject(label,run);aliases[original+'::'+h]=original_row
 bad_alias('alias wrong digest',{'file':retained,'sha256':'0'*64})
 bad_alias('alias self reference cannot authorize retrieval',{'file':original,'sha256':h})
 bad_alias('alias path traversal',{'file':'../escape','sha256':h})
 bad_alias('alias absolute destination',{'file':'/tmp/escape','sha256':h})
 bad_alias('alias glob destination',{'file':'unsafe/*.log','sha256':h})
 saved=aliases.pop(original+'::'+h);reject('relative original without explicit exactSHA alias',run);aliases[original+'::'+h]=saved
 aliases[original+'::'+'0'*64]=aliases.pop(original+'::'+h);reject('alias key wrong originalSHA',run);aliases[original+'::'+h]=aliases.pop(original+'::'+'0'*64)
 put(original,b'stale Root original');reject('stale Root original always rejected before retrieval',run);put(original,content)
 put(retained,b'stale retained Root');reject('stale retained Root copy',run);put(retained,content)
 put(retained,b'stale retained Pub',pub);reject('stale alreadyprepared Pub retained copy',run);put(retained,content,pub)
 prepared.clear();reject('exact alias copy unbound by supplemental or prepared set',run)
 expected[retained]='0'*64;reject('supplemental alias bound to wrong digest',run);expected[retained]=h
 (root/retained).unlink();(root/retained).symlink_to(root/original);reject('retained final symlink rejected',run);(root/retained).unlink();put(retained,content)
 (root/original).unlink();(root/original).symlink_to(root/retained);reject('Root original final symlink rejected',run);(root/original).unlink();put(original,content)
 expected.clear();expected[original]=h;accept('direct exact supplemental original remains valid',run)
 expected.clear();prepared.add(original);put(original,content,pub);accept('direct exact prepared original remains valid',run);prepared.clear()
 # A relative current owner may be retained as evidence, never copied onto its published owner here.
 owner='book/coverage/core.json';put(owner,b'raw current Core evidence\n');ownerh=sha(root/owner);ownerretained='retained/core-original.json';put(ownerretained,(root/owner).read_bytes())
 put(peername,dict(peer,closed_evidence_sha256={owner:ownerh}));owner_alias={owner+'::'+ownerh:{'file':ownerretained,'sha256':ownerh}}
 accept('other raw owner exact evidence retrieval only through typed retained copy',lambda:ns['closed_peer'](peername,status,owner_alias,{ownerretained:ownerh},set(),{}))
 reject('other raw owner with no retained evidence binding',lambda:ns['closed_peer'](peername,status,owner_alias,{},set(),{}))
 applied='book/coverage/applied.json';raw=b'raw unpruned Applied exact evidence\n';put(applied,raw);appliedh=sha(root/applied);appliedretained='retained/applied-original.json';put(appliedretained,raw);put(applied,b'published three-metadata-pruned Applied\n',pub)
 put(peername,dict(peer,closed_evidence_sha256={applied:appliedh}));appliedalias={applied+'::'+appliedh:{'file':appliedretained,'sha256':appliedh}}
 applied_run=lambda w:ns['closed_peer'](peername,status,appliedalias,{appliedretained:appliedh},set(),w)
 accept('raw Applied evidence retrieval preserves different pruned Pub owner',lambda:applied_run({applied:appliedh}))
 reject('raw Applied missing working manifest exacthash',lambda:applied_run({}))
 reject('raw Applied wrong working manifest exacthash',lambda:applied_run({applied:'0'*64}))
 assert (pub/applied).read_bytes()==b'published three-metadata-pruned Applied\n'
 absolute='/tmp/original-native-checker.py';absolute_retained='retained/original-native-checker.py';put(absolute_retained,b'absolute closed original\n');absoluteh=sha(root/absolute_retained)
 absolute_second='retained/second-copy.py';put(absolute_second,(root/absolute_retained).read_bytes())
 put(peername,dict(peer,closed_evidence_sha256={absolute:absoluteh}));absolutealiases={absolute+'::'+absoluteh:{'file':absolute_retained,'sha256':absoluteh}}
 absolute_run=lambda e,p:ns['closed_peer'](peername,status,absolutealiases,e,p,{})
 accept('absolute TMP closure requires direct exactexplicit retained copy',lambda:absolute_run({absolute_retained:absoluteh},set()))
 reject('absolute TMP closure does not gain relative fallback',lambda:absolute_run({absolute_second:absoluteh},set()))
 put(absolute_retained,(root/absolute_retained).read_bytes(),pub);accept('absolute TMP closure alreadyprepared direct retained copy',lambda:absolute_run({}, {absolute_retained}))
 reject('absolute TMP closure wrong required digest',lambda:absolute_run({absolute_retained:'0'*64},set()))
 put(peername,dict(peer,closed_evidence_sha256={original:h}));expected={retained:h}
 for label,mutation in [('failed peer status',lambda d:d.update(status='failed')),('nonempty peer errors',lambda d:d.update(errors=['bad'])),('missing peer errors',lambda d:d.pop('errors')),('empty closed map',lambda d:d.update(closed_evidence_sha256={})),('non-dictionary closed map',lambda d:d.update(closed_evidence_sha256=[])),('unsafe original relative path',lambda d:d.update(closed_evidence_sha256={'../escape':h}))]:
  bad=copy.deepcopy(peer);mutation(bad);put(peername,bad);reject(label,run);put(peername,peer)
 assert not (root/ns['REPORT']).exists() and not (pub/ns['REPORT']).exists()
ns['ROOT']=ROOT;ns['PUB']=ROOT/'reports/book/publication-repo'
native=[]
for name,command in ns['REQUIRED_EXECUTIONS'].items():
 d=ns['actual'](name,command);native.append({'file':name,'sha256':sha(ROOT/name),'helper':command[1],'status':d['status'],'actual_exit_code':d.get('actual_exit_code'),'raw_log_sha256':d['log_sha256']})
assert len(native)==18
catalog_n='book/coverage/checks/future27-core/publication27-additional-closed-reference-byte-aliases-v1.json';catalog=ns['read'](catalog_n)
assert sha(ROOT/catalog_n)=='edd3de1ef8cafc26f7376073914b927168b83683c985e6c9efea7739cda9a33a'
rows=catalog['original_byte_aliases'];assert len(rows)==122
for key,row in rows.items():
 original,h=key.rsplit('::',1);assert type(row) is dict and set(row)=={'file','sha256'} and row['sha256']==h
 assert sha(ns['safe'](ROOT,original))==sha(ns['safe'](ROOT,row['file']))==h
 assert row['file']!=original
# Real failed stage was before copies/Git. Its original record remains strict1 and raw bytes are bound.
failed_n='reports/full-coverage/stage-publication27-execution-v1.json';failed=ns['read'](failed_n)
assert type(failed['actual_exit_code']) is int and failed['actual_exit_code']==1
assert sha(ns['safe'](ROOT,failed['log']))==failed['log_sha256']
prior_n=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v6.json';prior=json.loads(prior_n.read_bytes())
result={'status':'passed_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'fixture_count':len(fixtures),'fixtures':fixtures,'native_read_only_families':native,'prior_v6_full_body_and_time':prior,'prior_v6_ref':{'file':str(prior_n),'sha256':sha(prior_n)},'whole_v7_to_v6_reverse_exact':True,'unchanged_prepare_and_main_ast':True,'additional_exact_reference_alias_catalog':{'file':catalog_n,'sha256':sha(ROOT/catalog_n),'rows':122},'original_failed_stage':{'file':failed_n,'sha256':sha(ROOT/failed_n),'actual_exit_code':1},'production_helper_execution':False,'production_pub_or_git_mutation':False,'scope':'Full helper7 source and exact6 reverse; focused tests invoke the exact closed_peer on synthetic TMP Root/PUB with relative exactRoot typed retained alias, prepared/supplemental bindings, stale/missing/unsafe aliases, absolute original fallback rejection and raw Applied working-hash/pruned-owner preservation. All18 genuine native families and all122 real original::SHA catalog retained bytes rehashed read-only. Original61+33+28+62 fixture observations/body/times retained rather than rerun or counted new. No production prepare/main, copies, PUB/Git or publication claim.'}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixture_count':len(fixtures),'observations':str(OUT),'sha256':sha(OUT),'actual_native_families':len(native),'additional_alias_rows':len(rows)}))
