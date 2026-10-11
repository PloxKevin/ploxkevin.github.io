from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT)else str(p),'sha256':H(p)}
helpers={'main':('book/coverage/checks/root_stage_publication25_v3.py','4b1fb3927aa08ff63fcde33ab6b692c5098b06628a274caecff01b5fa475c7af'),'metadata':('book/coverage/checks/root_stage_publication25_delivery_metadata_v3.py','c093da065c42b5b1eb549ff42758caea362a07cb3b20e143096f9deacd474cab')}
observations={};cases=[]
def case(name,f,reject=False):
 try:f()
 except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):assert reject,name;cases.append({'fixture':name,'observed':'rejected','explicitly_synthetic_guard_fixture':True})
 else:assert not reject,name;cases.append({'fixture':name,'observed':'accepted','explicitly_synthetic_guard_fixture':True})
realname='book/coverage/checks/future25-core/checkpoint25-exact-four-suffix-freezer-independent-foundations-actual-v1.log';rh=H(ROOT/realname)
for kind,(name,expected)in helpers.items():
 p=ROOT/name;assert H(p)==expected;src=p.read_text();tree=ast.parse(src);start=len(cases)
 functions=[n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name!='main'];ns={'ROOT':ROOT,'PUB':ROOT/'reports/book/publication-repo','Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess};exec(compile(ast.Module(body=functions,type_ignores=[]),name,'exec'),ns)
 case(kind+' canonical safe',lambda:ns['safe'](realname))
 for bad in ['/tmp/file','../outside','book/coverage/../../../../etc/passwd','./book/coverage/a','book//coverage/a','x\0a','x\na','x\ra']:
  case(kind+' reject unsafe '+repr(bad),lambda bad=bad:ns['safe'](bad),True)
 records={};ns['read']=lambda n:records[n]
 record={'actual_exit_code':0,'exit_code':0,'log':realname,'raw_log':realname,'log_sha256':rh,'raw_log_sha256':rh}
 def test_actual(edits,code=0):
  d=copy.deepcopy(record);edits(d);records['fixture']=d
  return ns['actual']('fixture',code)if kind=='main'else ns['actual']('fixture')
 case(kind+' actual record equal aliases true raw hash',lambda:test_actual(lambda d:None))
 for k,v in [('exit_code',1),('actual_exit_code',False),('exit_code',0.0),('log_sha256','0'*64),('raw_log_sha256','0'*64),('raw_log','reports/full-coverage/else.log')]:
  case(kind+' rejects native alias '+k+repr(v),lambda k=k,v=v:test_actual(lambda d:d.update({k:v})),True)
 case(kind+' rejects missing exits',lambda:test_actual(lambda d:(d.pop('actual_exit_code'),d.pop('exit_code'))),True)
 if kind=='main':
  case('main actual historical failure preserved as1',lambda:test_actual(lambda d:d.update(actual_exit_code=1,exit_code=1),1))
  case('main failure rejected from successful stem',lambda:test_actual(lambda d:d.update(actual_exit_code=1,exit_code=1)),True)
 peerfn=ns['peer_evidence']if kind=='main'else ns['add_peer']
 basepeer={'status':'synthetic_fixture_passed','errors':[],'closed_evidence_sha256':{realname:rh}}
 def testpeer(mod):
  q=copy.deepcopy(basepeer);mod(q);records['peer']=q;names=set();r=peerfn('peer',names);return r,names
 case(kind+' canonical peer closure',lambda:testpeer(lambda q:None))
 orig='/tmp/synthetic-original-checker.log';alias={'file':realname,'sha256':rh}
 def absolute(q):q['closed_evidence_sha256']={orig:rh};q['original_closed_byte_aliases']={orig:alias}
 case(kind+' typed absolute original to canonical exact hash',lambda:testpeer(absolute))
 def wronghash(q):absolute(q);q['original_closed_byte_aliases'][orig]={'file':realname,'sha256':'0'*64}
 case(kind+' rejects mismatched absolute alias hash',lambda:testpeer(wronghash),True)
 case(kind+' rejects absolute closure without alias',lambda:testpeer(lambda q:q.update(closed_evidence_sha256={orig:rh})),True)
 def duplicate(q):absolute(q);q['original_closed_byte_aliases']['/tmp/second']={'file':realname,'sha256':rh}
 case(kind+' rejects duplicate canonical alias',lambda:testpeer(duplicate),True)
 def unsafepath(q):absolute(q);q['original_closed_byte_aliases'][orig]={'file':'/tmp/not-stageable','sha256':rh}
 case(kind+' rejects absolute alias target',lambda:testpeer(unsafepath),True)
 case(kind+' rejects peer errors',lambda:testpeer(lambda q:q.update(errors=['realerror'])),True)
 case(kind+' rejects pending peer',lambda:testpeer(lambda q:q.update(status='pending')),True)
 # Exercise actual producer dirty parser, using only a synthetic subprocess result.
 ns['subprocess']=type('MockSubprocess',(),{})
 def dirty(entries):
  ns['subprocess'].run=lambda *a,**kw:type('Result',(),{'stdout':''.join(x+'\0'for x in entries).encode()})();return ns['dirty']()
 case(kind+' whitelist dirty parser',lambda:dirty([' M book/coverage/progress.json','?? reports/full-coverage/a b.log']))
 for e in ['R  oldpath',' R newpath','C  copied',' D removed','D  removed']:
  case(kind+' rejects rename-copy-delete '+repr(e),lambda e=e:dirty([e]),True)
 case(kind+' dirty subset rejects unrelated',lambda:exec("assert dirty(['?? unrelated']) <= {'book/coverage/progress.json'}",{'dirty':dirty}),True)
 main=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='main');body=main.body
 firstcopy=next(i for i,n in enumerate(body)if isinstance(n,ast.For)and 'shutil.copyfile'in ast.unparse(n))
 assert all(not any(isinstance(x,ast.Call)and ast.unparse(x.func)in ['shutil.copyfile','shutil.copytree']for x in ast.walk(n))for n in body[:firstcopy])
 assert all(not any(isinstance(x,ast.Call)and ast.unparse(x.func)=='subprocess.run'and any(a in ast.unparse(x)for a in ["'commit'","'push'"])for x in ast.walk(n))for n in body)
 assert "['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul']"in src and 'input=payload'in src
 assert "assert staged() and staged()<="in src and "assert dirty()<="in src
 required=['1156','9369','coverage_complete','sha(safe(n))==sha(target(n))','original_closed_byte_aliases','closed_evidence_sha256']
 for text in required:assert text in src,(kind,text)
 if kind=='main':
  for text in ["config['prospective_included_website_bytes_before_new_native_records']","prospective=included_now+replacements+(len(record_bytes) if kept(REPORT) else 0)",'0<=prospective<850_000_000',"set(manifest['frozen_inputs_sha256'])<=paths","audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}","'root-independent-selection25-output-execution-v1'","owner25-integration-dry-execution-v1.json","'fresh_kernel_replay'","'reused_identical_module_and_transitive_local_imports'","config['excluded_count']==len(config['exclusions'])==97"]:assert text in src,text
  # Execute the real read-only prospective budget block on a tiny isolated mock tree.
  lo=next(i for i,n in enumerate(body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='exclusions'for t in n.targets));hi=firstcopy
  code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[lo:hi]),type_ignores=[])),name,'exec')
  with tempfile.TemporaryDirectory(prefix='foundation25-budget-fixture-')as td:
   root=Path(td)/'root';pub=Path(td)/'pub';root.mkdir();pub.mkdir();(root/'new.log').write_bytes(b'new');(pub/'new.log').write_bytes(b'oldold');(pub/'keep.json').write_bytes(b'1'*10);(pub/'excluded').mkdir();(pub/'excluded/x').write_bytes(b'x'*100)
   env={'config':{'exclusions':['excluded']+['absent'+str(i)for i in range(96)]},'PUB':pub,'Path':Path,'json':json,'safe':lambda n:root/n,'target':lambda n:pub/n,'expected':{'new.log':'synthetic_hash_fixture'},'record':{'synthetic':True},'REPORT':'report.json'}
   exec(code,env);assert env['included_now']==16 and env['replacements']==-3;assert env['prospective']==13+len(env['record_bytes']);cases.append({'fixture':'main exact replacement native byte budget','observed':'accepted','explicitly_synthetic_guard_fixture':True})
   bad=dict(env);bad['config']={'exclusions':['excluded']*97};case('main duplicate literal exclusion rejected',lambda:exec(code,bad),True)
   bad=dict(env);bad['config']={'exclusions':['*']+['absent'+str(i)for i in range(96)]};case('main wildcard exclusion rejected',lambda:exec(code,bad),True)
   # Huge additional source is represented by an explicit stat proxy, no huge file created.
   real_safe=env['safe'];Huge=type('Huge',(),{'stat':lambda self:type('Stat',(),{'st_size':850_000_000})()});bad=dict(env);bad['safe']=lambda n:Huge();case('main prospective budget over850M rejected',lambda:exec(code,bad),True)
 else:
  for text in ["set(update['updated_sha256'])=={'book/coverage/progress.json','reports/full-coverage/README.md'}","for n,h in update['evidence_sha256'].items():assert sha(safe(n))==h,n","len({row['source'] for row in live['assets']})==31","row['http_status']==200 and row['matches'] is True","row['actual_sha256']==row['expected_sha256']==sha(safe(row['source']))","d['actual_command']==['python3',PRIMARY_HELPER]","d['helper_sha256_before']==d['helper_sha256_after']"]:assert text in src,text
  # Direct actual live-row producer AST validation with explicit synthetic hashes.
  mlo=next(i for i,n in enumerate(body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='assets'for t in n.targets));mhi=next(i for i,n in enumerate(body[mlo:],mlo)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='progress'for t in n.targets))
  code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[mlo:mhi]),type_ignores=[])),name,'exec');assets={'SafeLearning/'+str(i)+'.html':str(i).zfill(64)for i in range(31)};live={'assets':[{'source':n,'expected_sha256':h,'actual_sha256':h,'http_status':200,'matches':True}for n,h in assets.items()]}
  def livecase(edit):
   l=copy.deepcopy(live);edit(l);exec(code,{'manifest':{'frozen_inputs_sha256':assets},'live':l,'sha':lambda n:assets[n],'safe':lambda n:n,'target':lambda n:n})
  case('metadata exact31 live mappings accepted',lambda:livecase(lambda l:None))
  for k,v in [('expected_sha256','0'*64),('actual_sha256','0'*64),('http_status',404),('matches',False),('source','SafeLearning/changed.html')]:
   case('metadata changed live evidence '+k,lambda k=k,v=v:livecase(lambda l:l['assets'][1].update({k:v})),True)
  case('metadata repeated asset rejected',lambda:livecase(lambda l:l['assets'].__setitem__(1,copy.deepcopy(l['assets'][0]))),True)
 observations[kind]={'status':'independent_publication25_'+kind+'_stager_full_code_and_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Applied authored helper','helper':ref(p),'helper_sha256':expected,'full_code_read':True,'fixture_count':len(cases)-start,'fixtures':cases[start:],'historical_unexecuted_helper_versions':{str((ROOT/'book/coverage/checks'/ (p.stem[:-2]+'v'+str(v)+'.py')).relative_to(ROOT)):H(ROOT/'book/coverage/checks'/ (p.stem[:-2]+'v'+str(v)+'.py'))for v in [1,2]},'scope':'Full code approval and explicitly synthetic read-only guard fixtures only. No main/helper invocation, future audit/preparation/budget/output approval, PUB write or actual publication Git/Pages/deployment action. Real gates remain required.'}
# A genuine separate temporary Git regression proves explicit force/NUL staging handles ignored logs without adding unrelated files.
with tempfile.TemporaryDirectory(prefix='foundation25-ignored-log-regression-')as td:
 t=Path(td);subprocess.run(['git','init','-q'],cwd=t,check=True);(t/'.gitignore').write_text('*.log\n');(t/'actual.log').write_text('genuine isolated regression\n');(t/'unrelated.txt').write_text('do not stage\n');payload=b'.gitignore\0actual.log\0';subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=t,input=payload,check=True);st=set(subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=t,check=True,capture_output=True).stdout.split(b'\0'))-{b''};assert st=={b'.gitignore',b'actual.log'}
for k,v in observations.items():v['real_temporary_git_force_explicit_NUL_ignored_log_regression_passed']=True
OUT=Path('/tmp/publication25-two-stagers-independent-foundations-observations-v2.json');assert not OUT.exists();OUT.write_text(json.dumps(observations,indent=2)+'\n');print(json.dumps({'status':'passed','fixtures':len(cases),'observation':ref(OUT)}))
