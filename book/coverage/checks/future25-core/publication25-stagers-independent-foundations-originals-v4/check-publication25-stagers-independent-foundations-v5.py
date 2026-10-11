from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT)else str(p),'sha256':H(p)}
helpers={'main':('book/coverage/checks/root_stage_publication25_v8.py','06abe1870775f2a3ca88b91b459f184c72c54711d78716cac8b0e7b9cab781e6'),'metadata':('book/coverage/checks/root_stage_publication25_delivery_metadata_v8.py','ae6e7125e76574c388305a8d25310ed74cce8c19d2f0e3b3580be4d9e03a2200')}
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
  return ns['actual']('fixture',code)
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
  for text in ["config['prospective_included_website_bytes_before_new_native_records']","prospective=included_now+replacements+(len(record_bytes) if kept(REPORT) else 0)",'0<=prospective<850_000_000',"set(manifest['frozen_inputs_sha256'])<=paths","audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}","'root-independent-selection25-output-execution-v1'","owner25-integration-dry-execution-v1.json","'fresh_kernel_replay'","'reused_identical_module_and_transitive_local_imports'","config['excluded_count']==len(config['exclusions'])==101"]:assert text in src,text
  # Execute the real read-only prospective budget block on a tiny isolated mock tree.
  lo=next(i for i,n in enumerate(body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='exclusions'for t in n.targets));hi=firstcopy
  code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[lo:hi]),type_ignores=[])),name,'exec')
  with tempfile.TemporaryDirectory(prefix='foundation25-budget-fixture-')as td:
   root=Path(td)/'root';pub=Path(td)/'pub';root.mkdir();pub.mkdir();(root/'new.log').write_bytes(b'new');(pub/'new.log').write_bytes(b'oldold');(pub/'keep.json').write_bytes(b'1'*10);(pub/'excluded').mkdir();(pub/'excluded/x').write_bytes(b'x'*100)
   env={'config':{'exclusions':['excluded']+['absent'+str(i)for i in range(100)]},'PUB':pub,'Path':Path,'json':json,'safe':lambda n:root/n,'target':lambda n:pub/n,'expected':{'new.log':'synthetic_hash_fixture'},'record':{'synthetic':True},'REPORT':'report.json'}
   exec(code,env);assert env['included_now']==16 and env['replacements']==-3;assert env['prospective']==13+len(env['record_bytes']);cases.append({'fixture':'main exact replacement native byte budget','observed':'accepted','explicitly_synthetic_guard_fixture':True})
   bad=dict(env);bad['config']={'exclusions':['excluded']*101};case('main duplicate literal exclusion rejected',lambda:exec(code,bad),True)
   bad=dict(env);bad['config']={'exclusions':['*']+['absent'+str(i)for i in range(100)]};case('main wildcard exclusion rejected',lambda:exec(code,bad),True)
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
 observations[kind]={'status':'independent_publication25_'+kind+'_stager_full_code_and_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Applied authored helper','helper':ref(p),'helper_sha256':expected,'full_code_read':True,'fixture_count':len(cases)-start,'fixtures':cases[start:],'historical_helper_versions':{str((ROOT/'book/coverage/checks'/ (p.stem[:-2]+'v'+str(v)+'.py')).relative_to(ROOT)):H(ROOT/'book/coverage/checks'/ (p.stem[:-2]+'v'+str(v)+'.py'))for v in [1,2,3,4,5,6,7]},'scope':'Full code approval and explicitly synthetic read-only guard fixtures only. No main/helper invocation, future audit/preparation/budget/output approval, PUB write or actual publication Git/Pages/deployment action. Real gates remain required.'}
# A genuine separate temporary Git regression proves explicit force/NUL staging handles ignored logs without adding unrelated files.
with tempfile.TemporaryDirectory(prefix='foundation25-ignored-log-regression-')as td:
 t=Path(td);subprocess.run(['git','init','-q'],cwd=t,check=True);(t/'.gitignore').write_text('*.log\n');(t/'actual.log').write_text('genuine isolated regression\n');(t/'unrelated.txt').write_text('do not stage\n');payload=b'.gitignore\0actual.log\0';subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=t,input=payload,check=True);st=set(subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=t,check=True,capture_output=True).stdout.split(b'\0'))-{b''};assert st=={b'.gitignore',b'actual.log'}
for k,v in observations.items():v['real_temporary_git_force_explicit_NUL_ignored_log_regression_passed']=True
# Fresh read-only native/schema delta; execute only isolated producer guard AST.
main_path=ROOT/helpers['main'][0];main_tree=ast.parse(main_path.read_text())
meta_path=ROOT/helpers['metadata'][0];meta_tree=ast.parse(meta_path.read_text())
for kind, tree in [('main',main_tree),('metadata',meta_tree)]:
 baseline=ast.parse((ROOT/('book/coverage/checks/root_stage_publication25_v3.py'if kind=='main'else'book/coverage/checks/root_stage_publication25_delivery_metadata_v3.py')).read_text())
 old_functions={x.name:ast.dump(x,include_attributes=False)for x in baseline.body if isinstance(x,ast.FunctionDef)and x.name!='main'}
 new_functions={x.name:ast.dump(x,include_attributes=False)for x in tree.body if isinstance(x,ast.FunctionDef)and x.name!='main'}
 assert {k:v for k,v in old_functions.items()if not(kind=='main'and k=='peer_evidence')and not(kind=='metadata'and k=='actual')}=={k:v for k,v in new_functions.items()if not(kind=='main'and k=='peer_evidence')and not(kind=='metadata'and k=='actual')}
 observations[kind]['all_reusable_unchanged_guard_function_ASTs_equal_original_fully_reviewed_v3']=True
body=next(x for x in main_tree.body if isinstance(x,ast.FunctionDef)and x.name=='main').body
consts={}
for x in main_tree.body:
 if isinstance(x,ast.Assign)and len(x.targets)==1 and isinstance(x.targets[0],ast.Name):
  try:consts[x.targets[0].id]=ast.literal_eval(x.value)
  except (ValueError,TypeError):pass
assert consts['CONFIG_HELPER']=='book/coverage/checks/root_prepare_pages25_config_v3.py'
assert consts['CONFIG_HELPER_SHA']=='6a05cb9a1ab25be9b2450778f264a424613dcea4c895452aec2545bbf7cabc70'
assert consts['CONFIG_CODE_PEER']=='book/coverage/checks/pages25-config-helper-independent-modules-review-v3.json'
assert consts['CONFIG_OUTPUT_PEER']=='book/coverage/checks/future25-core/pages25-config-independent-modules-review-v3.json'
lo=next(i for i,x in enumerate(body)if isinstance(x,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='browser_name'for t in x.targets))
hi=next(i for i,x in enumerate(body[lo:],lo)if isinstance(x,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='progress'for t in x.targets))
code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[lo:hi]),type_ignores=[])),str(main_path),'exec')
manifest_name='reports/full-coverage/checkpoint-25-manifest.json';manifest=json.loads((ROOT/manifest_name).read_text())
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
browser_name='reports/full-coverage/browser-checkpoint-25.json';realbrowser=json.loads((ROOT/browser_name).read_text())
def browser_guard(edit):
 browser=copy.deepcopy(realbrowser);edit(browser)
 env={'manifest_name':manifest_name,'assets':assets,'sha':H,'safe':lambda n:ROOT/n,'target':lambda n:ROOT/'reports/book/publication-repo'/n,
      'read':lambda n:browser if n==browser_name else json.loads((ROOT/n).read_text()),**consts}
 exec(code,env)
case('main actual retained24 native browser binding read-only',lambda:browser_guard(lambda d:None))
for field,value in [('status','pending'),('coverage_complete',True),('page_count',28),('fresh_verified_viewport_count',1),('retained_verified_viewport_count',144),('verified_viewport_count',144),('source_sha256',{}),('original_browser_report_body',{})]:
 case('main browser rejects changed '+field,lambda field=field,value=value:browser_guard(lambda d:d.update({field:value})),True)
case('main browser rejects changed QA source hash',lambda:browser_guard(lambda d:d['qa_source_sha256'].update({next(iter(d['qa_source_sha256'])):'0'*64})),True)
functions=[x for x in main_tree.body if isinstance(x,ast.FunctionDef)and x.name!='main']
realns={'ROOT':ROOT,'PUB':ROOT/'reports/book/publication-repo','Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess}
exec(compile(ast.Module(body=functions,type_ignores=[]),str(main_path),'exec'),realns)
stems=next(ast.literal_eval(x.value)for x in body if isinstance(x,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='stems'for t in x.targets))
assert 'export-integrity-checkpoint25-execution-v1'in stems and 'prepare-documentation25-execution-v1'in stems
assert 'retain-browser25-exact24-execution-v1'in stems and 'pages25-config-execution-v3'in stems and 'pages25-config-execution-v4'in stems
assert 'pages25-config-execution-v1'not in stems and 'pages25-config-execution-v2'not in stems
closed_native={};future=[]
for stem in stems:
 n='reports/full-coverage/'+stem+'.json'
 if not(ROOT/n).exists():assert stem=='pages25-config-execution-v4';future.append(n);continue
 d,log=realns['actual'](n);closed_native[n]=H(ROOT/n);closed_native[log]=H(ROOT/log)
for n in ['reports/full-coverage/owner25-integration-dry-execution-v1.json','reports/full-coverage/pages25-config-execution-v1.json','reports/full-coverage/pages25-config-execution-v2.json']:
 d,log=realns['actual'](n,1);closed_native[n]=H(ROOT/n);closed_native[log]=H(ROOT/log)
# Confirm all ten actual existing peer closures, including both immutable native lists.
actual_peers=[consts['CONFIG_CODE_PEER'],consts['CONFIG_OUTPUT_PEER'],consts['ROOT_OUTPUT'],consts['MODULE_OUTPUT'],consts['BROWSER_CODE_PEER'],consts['BROWSER_OUTPUT_PEER'],
 'book/coverage/checks/pages25-config-helper-independent-modules-review-v1.json',
 'book/coverage/checks/future25-core/checkpoint25-documentation-independent-applied-review-v1.json',
 'book/coverage/checks/future25-core/publication25-stage-independent-review-v3.json',
 'book/coverage/checks/future25-core/publication25-stage-independent-review-v6.json',
 'book/coverage/checks/future25-core/publication25-stage-independent-review-v7.json',
 'book/coverage/checks/pages25-config-helper-independent-modules-review-v2.json',
 'book/coverage/checks/future25-core/pages25-config-independent-modules-review-v2.json']
actual_closures={}
for pn in actual_peers:
 names=set();peer=realns['peer_evidence'](pn,names);assert pn in names
 for name in names:actual_closures[name]=H(ROOT/name)
 case('main actual existing native peer '+pn,lambda:None)
# Synthetic mutations keep only the pinned-peer SHA premise mocked, so each deeper list guard is tested separately.
for pn,count in [('book/coverage/checks/pages25-config-helper-independent-modules-review-v2.json',6),('book/coverage/checks/future25-core/pages25-config-independent-modules-review-v2.json',5)]:
 original_peer=json.loads((ROOT/pn).read_text());pinned=H(ROOT/pn)
 assert isinstance(original_peer['original_closed_byte_aliases'],list)and len(original_peer['original_closed_byte_aliases'])==count
 def list_case(edit,wrong_pin=False,other_path=False):
  peer=copy.deepcopy(original_peer);edit(peer);name='book/coverage/checks/unapproved-peer.json'if other_path else pn
  env=dict(realns);env['read']=lambda n:peer;env['sha']=lambda p:'0'*64 if Path(p)==ROOT/pn and wrong_pin else pinned if Path(p)==ROOT/pn else H(p)
  fns=[x for x in main_tree.body if isinstance(x,ast.FunctionDef)and x.name=='peer_evidence'];exec(compile(ast.Module(body=fns,type_ignores=[]),str(main_path),'exec'),env);names=set();env['peer_evidence'](name,names)
 case('main exact synthetic pinned native alias-list accepted '+str(count),lambda:list_case(lambda p:None))
 case('main native list wrong peer SHA rejected '+str(count),lambda:list_case(lambda p:None,wrong_pin=True),True)
 case('main native list unauthorized peer rejected '+str(count),lambda:list_case(lambda p:None,other_path=True),True)
 case('main native list wrong count rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'].pop()),True)
 case('main native list missing key rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].pop('original_path')),True)
 case('main native list extra key rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].update(extra=True)),True)
 case('main native list wrong row type rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'].__setitem__(0,'bad')),True)
 case('main native list duplicate original rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][1].update(original_path=p['original_closed_byte_aliases'][0]['original_path'])),True)
 case('main native list relative original rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].update(original_path='relative-original')),True)
 case('main native list NUL original rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].update(original_path='/tmp/bad\0')),True)
 case('main native list duplicate target rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][1].update(file=p['original_closed_byte_aliases'][0]['file'],sha256=p['original_closed_byte_aliases'][0]['sha256'])),True)
 case('main native list absolute target rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].update(file='/tmp/outside')),True)
 case('main native list parent traversal rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].update(file='../outside')),True)
 case('main native list bad hash rejected '+str(count),lambda:list_case(lambda p:p['original_closed_byte_aliases'][0].update(sha256='0'*64)),True)
 case('main native list bad closed hash rejected '+str(count),lambda:list_case(lambda p:p['closed_evidence_sha256'].update({next(iter(p['closed_evidence_sha256'])):'0'*64})),True)
# The metadata helper's optional code argument preserves strict exits while keeping actual failures as failures.
meta_functions=[x for x in meta_tree.body if isinstance(x,ast.FunctionDef)and x.name!='main'];metans={'ROOT':ROOT,'PUB':ROOT/'reports/book/publication-repo','Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess};exec(compile(ast.Module(body=meta_functions,type_ignores=[]),str(meta_path),'exec'),metans)
failed_stage='reports/full-coverage/stage-publication25-execution-v1.json';d,log=metans['actual'](failed_stage,1)
assert d['actual_command']==['python3','book/coverage/checks/root_stage_publication25_v6.py']
assert d['helper_sha256_before']==d['helper_sha256_after']=={'book/coverage/checks/root_stage_publication25_v6.py':H(ROOT/'book/coverage/checks/root_stage_publication25_v6.py')}
closed_native[failed_stage]=H(ROOT/failed_stage);closed_native[log]=H(ROOT/log)
case('metadata genuine failed stage1 accepted only as1',lambda:metans['actual'](failed_stage,1))
case('metadata genuine failed stage1 rejected from success gate',lambda:metans['actual'](failed_stage),True)
metadata_src=meta_path.read_text();assert "'stage-publication25-execution-v3'"in metadata_src and "if stem=='stage-publication25-execution-v3'"in metadata_src
for k,v in observations.items():
 v['all_existing_ten_actual_peer_closures_checked_not_just_wrapper_schemas']=actual_closures
 v['corrected_two_exact_native_list_schemas_with_strict_count_path_SHA_pins_checked']=True
 v['original_full_v6_peer']=ref(ROOT/('book/coverage/checks/future25-core/publication25-stage-independent-review-v6.json'if k=='main'else'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v6.json'))
# Read the actual amended configuration and preserve its earlier native body/time.
config2_name='reports/full-coverage/pages25-config-preparation-v2.json';config2=json.loads((ROOT/config2_name).read_text())
config1_name='reports/full-coverage/pages25-config-preparation-v1.json';config1=json.loads((ROOT/config1_name).read_text())
assert config2['entire_original_configuration_preparation_body_and_time']==config1
assert config2['original_configuration_preparation']=={'file':config1_name,'sha256':H(ROOT/config1_name)}
assert config2['excluded_count']==101 and set(config2['exclusions'])==set(config1['exclusions'])|{'reports/full-coverage/checkpoint-19-manifest.json','reports/full-coverage/checkpoint-19-selection.json'}
assert config2['helper']=={'file':consts['CONFIG_HELPER'],'sha256':consts['CONFIG_HELPER_SHA']}
assert config2['config_sha256']==H(ROOT/'reports/book/publication-repo/_config.yml')
assert config2['previous_configuration']['sha256']==config1['config_sha256']==H(ROOT/'reports/full-coverage/pages25-config-previous-original-v2.yml')
assert config2['required_publication_files_sha256']==config1['required_publication_files_sha256']
for n,h in config2['retained_original_native_files_sha256'].items():assert H(ROOT/n)==h
failed_stage2='reports/full-coverage/stage-publication25-execution-v2.json';fd,flog=metans['actual'](failed_stage2,1)
assert fd['actual_command']==['python3','book/coverage/checks/root_stage_publication25_v7.py']
assert fd['helper_sha256_before']==fd['helper_sha256_after']=={'book/coverage/checks/root_stage_publication25_v7.py':H(ROOT/'book/coverage/checks/root_stage_publication25_v7.py')}
closed_native[failed_stage2]=H(ROOT/failed_stage2);closed_native[flog]=H(ROOT/flog)
case('metadata true budgetfailed stage2 accepted onlyas1',lambda:metans['actual'](failed_stage2,1))
case('metadata true budgetfailed stage2 rejected success',lambda:metans['actual'](failed_stage2),True)
for k,v in observations.items():
 v['actual_amended_config2']=ref(ROOT/config2_name)
 v['earlier_config1_entire_native_body_time_and_backup_preserved']=True
 v['original_full_v7_peer']=ref(ROOT/('book/coverage/checks/future25-core/publication25-stage-independent-review-v7.json'if k=='main'else'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v7.json'))
for k,v in observations.items():
 v['actual_existing_wrapper_byte_bindings_checked_read_only']=closed_native
 v['future_actual_wrapper_not_inferred']=future
 v['original_full_v3_peer']=ref(ROOT/('book/coverage/checks/future25-core/publication25-stage-independent-review-v3.json'if k=='main'else'book/coverage/checks/future25-core/publication25-delivery-metadata-stager-independent-foundations-review-v3.json'))
 v['fresh_browser_delta_fixtures']=cases[77:]
 v['total_inherited_and_delta_fixture_count']=len(cases)
 v['config_code_peer_v2']=ref(ROOT/consts['CONFIG_CODE_PEER'])
 v['scope']='Full code/delta approval plus explicitly isolated synthetic fixtures and read-only native byte checks. No helper main execution, PUB copy, publication Git/Pages/deployment or future successful config3/current25 delivery claim. Every actual runtime gate remains mandatory.'
OUT=Path('/tmp/publication25-two-stagers-independent-foundations-observations-v5.json');assert not OUT.exists();OUT.write_text(json.dumps(observations,indent=2)+'\n');print(json.dumps({'status':'passed','fixtures':len(cases),'observation':ref(OUT)}))
