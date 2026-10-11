from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
helpers={'main':('book/coverage/checks/root_stage_publication26_v4.py','490beffeffd1879e5387d4c8f311516168ff5b8874784ecf3bc23bbdcacac489'),'metadata':('book/coverage/checks/root_stage_publication26_delivery_metadata_v4.py','8e7392e2d7096ee32ca384c556a702392269418ee102df3e821de5e3a5756d66')}
observations={};cases=[]
def case(name,fn,reject=False):
 try:fn()
 except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):assert reject,name;cases.append({'fixture':name,'observed':'rejected','synthetic_guard_fixture':True})
 else:assert not reject,name;cases.append({'fixture':name,'observed':'accepted','synthetic_guard_fixture':True})
def constants(tree):
 out={}
 for n in tree.body:
  if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
   try:out[n.targets[0].id]=ast.literal_eval(n.value)
   except (TypeError,ValueError):pass
 return out
realname='reports/full-coverage/prepare-browser26-execution-v1.log';rh=H(ROOT/realname)
for kind,(name,expected) in helpers.items():
 p=ROOT/name;assert H(p)==expected;src=p.read_text();tree=ast.parse(src);start=len(cases)
 basepath=ROOT/('book/coverage/checks/root_stage_publication26_v1.py' if kind=='main' else 'book/coverage/checks/root_stage_publication26_delivery_metadata_v1.py')
 base=ast.parse(basepath.read_text());oldfun={n.name:ast.dump(n,include_attributes=False) for n in base.body if isinstance(n,ast.FunctionDef) and n.name!='main'};newfun={n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,ast.FunctionDef) and n.name!='main'};assert oldfun==newfun
 old2path=ROOT/('book/coverage/checks/root_stage_publication26_v3.py' if kind=='main' else 'book/coverage/checks/root_stage_publication26_delivery_metadata_v3.py')
 old2tree=ast.parse(old2path.read_text());old2main=next(n for n in old2tree.body if isinstance(n,ast.FunctionDef) and n.name=='main');new3main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
 added2={'book/coverage/checks/root_stage_publication26_v3.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v3.py','book/coverage/checks/future26-core/publication26-stage-independent-review-v3.json','book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v3.json'}
 if kind=='metadata':added2.update({'reports/full-coverage/stage-publication26-execution-v1.json','reports/full-coverage/stage-publication26-execution-v1.log'})
 class UndoDelta(ast.NodeTransformer):
  def visit_Set(self,n):
   n=self.generic_visit(n);n.elts=[x for x in n.elts if not(isinstance(x,ast.Constant) and x.value in added2)];return n
  def visit_Constant(self,n):
   if kind=='metadata' and n.value=='stage-publication26-execution-v2':return ast.copy_location(ast.Constant(value='stage-publication26-execution-v1'),n)
   return n
 reversecopy=copy.deepcopy(new3main)
 if kind=='main':
  lo=next(i for i,n in enumerate(reversecopy.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='failed_name' for t in n.targets))
  hi=next(i for i,n in enumerate(reversecopy.body[lo:],lo) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='expected' for t in n.targets));del reversecopy.body[lo:hi]
  oldbrowser=next(n for n in ast.walk(old2main) if isinstance(n,ast.If) and ast.unparse(n.test)=='n == BROWSER_OUTPUT_PEER')
  for n in ast.walk(reversecopy):
   if isinstance(n,ast.If) and ast.unparse(n.test)=='n == BROWSER_OUTPUT_PEER':n.body=copy.deepcopy(oldbrowser.body)
   if isinstance(n,ast.Dict):
    remove=[i for i,k in enumerate(n.keys) if isinstance(k,ast.Constant) and k.value=='retained_actual_stager3_prewrite_failure_sha256']
    for i in reversed(remove):del n.keys[i];del n.values[i]
 reversedmain=UndoDelta().visit(reversecopy);assert ast.dump(reversedmain,include_attributes=False)==ast.dump(old2main,include_attributes=False),kind

 old2constants=constants(old2tree);new3constants=constants(tree);changed={k for k in old2constants if old2constants[k]!=new3constants[k]}
 assert changed==({'PEER'} if kind=='main' else {'PEER','PRIMARY_HELPER','PRIMARY_PEER'}),changed
 oldpeername=('book/coverage/checks/future26-core/publication26-stage-independent-review-v3.json' if kind=='main' else 'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v3.json')
 oldpeerhash=('a654795dc98de6f93d5e81fc01a05e343364cee2adb0503493b8546dd3228b6a' if kind=='main' else 'ac9a00b6da08538c74a84934d651f1392ed4f6745ee749119bb840d0cf4bf43d')
 assert H(ROOT/oldpeername)==oldpeerhash;oldpeer=json.loads((ROOT/oldpeername).read_text());assert 'passed' in oldpeer['status'] and oldpeer['errors']==[]
 case(kind+' exact v4 main AST inverse retains entire v3 flow',lambda:None)
 case(kind+' only declared version/config constants changed',lambda:None)
 for n in added2:assert (ROOT/n).is_file() and not (ROOT/n).is_symlink()
 case(kind+' all explicit prior v3 archival additions exist unchanged',lambda:None)
 ns={'ROOT':ROOT,'PUB':PUB,'Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess}
 funcs=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name!='main'];exec(compile(ast.Module(body=funcs,type_ignores=[]),name,'exec'),ns)
 case(kind+' safe canonical path',lambda:ns['safe'](realname))
 for bad in ['/tmp/file','../escape','book/coverage/../../escape','./book/coverage/a','book//coverage/a','x\0a','x\na','x\ra']:
  case(kind+' rejects unsafe '+repr(bad),lambda bad=bad:ns['safe'](bad),True)
 records={};ns['read']=lambda n:records[n]
 actual={'actual_exit_code':0,'exit_code':0,'log':realname,'raw_log':realname,'log_sha256':rh,'raw_log_sha256':rh}
 def actualcase(edit,code=0):
  d=copy.deepcopy(actual);edit(d);records['fixture']=d;return ns['actual']('fixture',code)
 case(kind+' strict zero record actual raw hash',lambda:actualcase(lambda d:None))
 for k,v in [('actual_exit_code',False),('exit_code',False),('exit_code',0.0),('exit_code',1),('log_sha256','0'*64),('raw_log_sha256','0'*64),('raw_log','reports/full-coverage/else.log')]:
  case(kind+' rejects conflicting/illtyped actual '+k+repr(v),lambda k=k,v=v:actualcase(lambda d:d.update({k:v})),True)
 case(kind+' missing exit fields rejected',lambda:actualcase(lambda d:(d.pop('actual_exit_code'),d.pop('exit_code'))),True)
 case(kind+' actual genuine failure schema retained as1',lambda:actualcase(lambda d:d.update(actual_exit_code=1,exit_code=1),1))
 case(kind+' failure excluded from zero gate',lambda:actualcase(lambda d:d.update(actual_exit_code=1,exit_code=1)),True)
 peer={'status':'synthetic_guard_passed','errors':[],'closed_evidence_sha256':{realname:rh}}
 def peercase(edit):
  d=copy.deepcopy(peer);edit(d);records['peer']=d;paths=set();return ns['peer_evidence']('peer',paths),paths
 orig='/tmp/synthetic-original.log';alias={'file':realname,'sha256':rh}
 def dictalias(d):d.update(closed_evidence_sha256={orig:rh},original_closed_byte_aliases={orig:alias})
 def listalias(d):d.update(closed_evidence_sha256={orig:rh},original_closed_byte_aliases=[{'original_path':orig,**alias}])
 case(kind+' canonical relative peer closure',lambda:peercase(lambda d:None))
 case(kind+' typed dict absolute alias exact canonical copy',lambda:peercase(dictalias))
 case(kind+' typed list absolute alias exact canonical copy',lambda:peercase(listalias))
 def duplicate(d):listalias(d);d['original_closed_byte_aliases'].append(copy.deepcopy(d['original_closed_byte_aliases'][0]))
 case(kind+' duplicate original list rejected',lambda:peercase(duplicate),True)
 def extra(d):listalias(d);d['original_closed_byte_aliases'][0]['extra']=True
 case(kind+' extra list schema key rejected',lambda:peercase(extra),True)
 def relative(d):listalias(d);d['original_closed_byte_aliases'][0]['original_path']='relative/path'
 case(kind+' relative original rejected',lambda:peercase(relative),True)
 def unsafed(d):dictalias(d);d['original_closed_byte_aliases'][orig]={'file':'../escape','sha256':rh}
 case(kind+' unsafe alias target rejected',lambda:peercase(unsafed),True)
 def wrong(d):dictalias(d);d['original_closed_byte_aliases'][orig]={'file':realname,'sha256':'0'*64}
 case(kind+' incorrect canonical alias digest rejected',lambda:peercase(wrong),True)
 case(kind+' absolute closed hash lacking alias rejected',lambda:peercase(lambda d:d.update(closed_evidence_sha256={orig:rh})),True)
 case(kind+' peer errors rejected',lambda:peercase(lambda d:d.update(errors=['failure'])),True)
 case(kind+' pending peer rejected',lambda:peercase(lambda d:d.update(status='pending')),True)
 def samebytes(d):dictalias(d);d['original_closed_byte_aliases']['/tmp/other-name']=dict(alias)
 case(kind+' two exact original aliases sharing content-addressed bytes accepted',lambda:peercase(samebytes))
 ns['subprocess']=type('MockSubprocess',(),{})
 def dirt(entries):
  ns['subprocess'].run=lambda *a,**kw:type('Result',(),{'stdout':''.join(e+'\0' for e in entries).encode()})();return ns['dirty']()
 case(kind+' NUL dirty parser handles space path',lambda:dirt([' M book/coverage/progress.json','?? reports/full-coverage/a b.log']))
 for entry in ['R  old',' R new','C  copy',' D gone','D  gone']:
  case(kind+' rename-copy-delete rejected '+repr(entry),lambda entry=entry:dirt([entry]),True)
 case(kind+' dirty unrelated path excluded',lambda:exec("assert dirt(['?? unrelated']) <= {'book/coverage/progress.json'}",{'dirt':dirt}),True)
 main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main');body=main.body
 firstcopy=next(i for i,n in enumerate(body) if isinstance(n,ast.For) and 'shutil.copyfile' in ast.unparse(n))
 assert not any(isinstance(x,ast.Call) and ast.unparse(x.func) in ['shutil.copyfile','shutil.copytree'] for n in body[:firstcopy] for x in ast.walk(n))
 assert not any(isinstance(x,ast.Call) and ast.unparse(x.func)=='subprocess.run' and any(t in ast.unparse(x) for t in ["'commit'","'push'"]) for x in ast.walk(main))
 assert "['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul']" in src and 'input=payload' in src
 for text in ['1167','9503','coverage_complete','sha(safe(n))==sha(target(n))','original_closed_byte_aliases','closed_evidence_sha256','assert dirty()<=','assert staged() and staged()<=']:assert text in src,(kind,text)
 c=constants(tree)
 if kind=='main':
  assert c['CONFIG_HELPER']=='book/coverage/checks/root_prepare_pages26_config_v3.py' and H(ROOT/c['CONFIG_HELPER'])==c['CONFIG_HELPER_SHA']=='30d7f41eb587b915230eaa272efd44355b6a1965864ec71624ae295c2c03b50f'
  assert c['CONFIG_CODE_PEER']=='book/coverage/checks/pages26-config-helper-independent-modules-review-v3.json'
  assert c['CONFIG_OUTPUT_PEER']=='book/coverage/checks/future26-core/pages26-config-independent-modules-output-v3.json'
  for text in ["config['excluded_count']==len(config['exclusions'])==116","binding['original_input_count']==len(rows)==44111","len(prior['proof_files'])==1156","'fresh_kernel_replay'","'reused_identical_module_and_transitive_local_imports'","set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}","len(removed)==(3 if owner=='applied' else 0)","0<=prospective<850_000_000"]:assert text in src,text
 else:
  assert c['PRIMARY_HELPER']==helpers['main'][0]
  for text in ["set(update['updated_sha256'])=={'book/coverage/progress.json','reports/full-coverage/README.md'}","for n,h in update['evidence_sha256'].items():assert sha(safe(n))==h,n","len({row['source'] for row in live['assets']})==31","row['http_status']==200 and row['matches'] is True","row['actual_sha256']==row['expected_sha256']==sha(safe(row['source']))","d['actual_command']==['python3',PRIMARY_HELPER]"]:assert text in src,text
 # Run the exact native byte budget block against a tiny isolated tree only.
 lo=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='exclusions' for t in n.targets))
 code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[lo:firstcopy]),type_ignores=[])),name,'exec')
 with tempfile.TemporaryDirectory(prefix='foundation26-stager-budget-fixture-') as td:
  rr=Path(td)/'root';pp=Path(td)/'pub';rr.mkdir();pp.mkdir();(rr/'new.log').write_bytes(b'new');(pp/'new.log').write_bytes(b'oldold');(pp/'keep.json').write_bytes(b'1234567890');(pp/'excluded').mkdir();(pp/'excluded/x').write_bytes(b'x'*100)
  env={'config':{'exclusions':['excluded']+['absent'+str(i) for i in range(115)]},'PUB':pp,'Path':Path,'json':json,'read':lambda n:{'exclusions':['excluded']+['absent'+str(i) for i in range(115)]},'safe':lambda n:rr/n,'target':lambda n:pp/n,'expected':{'new.log':'synthetic_hash'},'record':{'synthetic':True},'out':{'synthetic':True},'REPORT':'report.json'}
  exec(code,env);assert env['included_now']==16 and env['replacements']==-3
  case(kind+' exact additional/replacement/native report budget',lambda:None)
  bad=dict(env);bad['config']={'exclusions':['excluded']*116};bad['read']=lambda n:bad['config'];case(kind+' duplicate exclusions rejected',lambda:exec(code,bad),True)
  bad=dict(env);bad['config']={'exclusions':['*']+['absent'+str(i) for i in range(115)]};bad['read']=lambda n:bad['config'];case(kind+' wildcard exclusion rejected',lambda:exec(code,bad),True)
  for count in (115,117):
   bad=dict(env);bad['config']={'exclusions':['excluded']+['absent'+str(i) for i in range(count-1)]};bad['read']=lambda n,bad=bad:bad['config'];case(kind+' config wrong count '+str(count)+' rejected',lambda bad=bad:exec(code,bad),True)
  Huge=type('Huge',(),{'stat':lambda self:type('Stat',(),{'st_size':850_000_000})()});bad=dict(env);bad['safe']=lambda n:Huge();case(kind+' additional included bytes over850M rejected',lambda:exec(code,bad),True)
 # Execute actual current typed peer closures read-only, without main execution.
 realns={'ROOT':ROOT,'PUB':PUB,'Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess};exec(compile(ast.Module(body=funcs,type_ignores=[]),name,'exec'),realns)
 native_peers=(['book/coverage/checks/pages26-config-helper-independent-foundations-review-v1.json',c['BROWSER_CODE_PEER'],c['BROWSER_OUTPUT_PEER'],c['DOC_PEER'],c['CONFIG_CODE_PEER'],oldpeername,'book/coverage/checks/future26-core/owner26-live-interface-and-request-helpers-independent-foundations-review-v1.json'] if kind=='main' else [c['UPDATER_PEER'],oldpeername])
 closures={}
 for pn in native_peers:
  paths=set();realns['peer_evidence'](pn,paths)
  for n in paths:closures[n]=H(ROOT/n)
  case(kind+' actual native typed closure '+pn,lambda:None)
 if kind=='main':
  browser=json.loads((ROOT/'reports/full-coverage/browser-checkpoint-26.json').read_text());peer=json.loads((ROOT/c['BROWSER_OUTPUT_PEER']).read_text());role=next(n for n in ast.walk(main) if isinstance(n,ast.If) and ast.unparse(n.test)=='n == BROWSER_OUTPUT_PEER')
  rolecode=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(role.body),type_ignores=[])),name,'exec')
  def rolecase(peeredit=lambda x:None,recordedit=lambda n,x:None):
   pp=copy.deepcopy(peer);peeredit(pp);env={**realns,**c,'peer':pp,'browser':browser,'browser_name':'reports/full-coverage/browser-checkpoint-26.json','extra':set()}
   originalread=realns['read']
   def readrecord(n):
    x=originalread(n);recordedit(n,x);return x
   env['read']=readrecord
   def actualrecord(n,code=0):
    local={**realns,'read':readrecord};exec(compile(ast.Module(body=copy.deepcopy(funcs),type_ignores=[]),name,'exec'),local);local['read']=readrecord;return local['actual'](n,code)
   env['actual']=actualrecord;exec(rolecode,env);return env['extra']
  case('main actual native preparation and fresh-capture roles separately accepted',lambda:rolecase())
  case('main rejects fresh capture substituted for preparation peer',lambda:rolecase(lambda p:p.update(actual_execution={'file':browser['actual_execution'],'sha256':browser['actual_execution_sha256']})),True)
  case('main rejects incorrect preparation peer hash',lambda:rolecase(lambda p:p['actual_execution'].update(sha256='0'*64)),True)
  for label,field,value in [('failed preparation','actual_exit_code',1),('false preparation','actual_exit_code',False),('wrong preparation command','actual_command',['python3','wrong.py']),('wrong preparation helper','helper_sha256_after',{}),('wrong preparation log','log_sha256','0'*64)]:
   case('main role rejects '+label,lambda field=field,value=value:rolecase(recordedit=lambda n,x:x.update({field:value}) if n=='reports/full-coverage/prepare-browser26-execution-v1.json' else None),True)
  for field,value in [('exit_code',1),('exit_code',False),('log_sha256','0'*64)]:
   case('main role rejects fresh '+field+repr(value),lambda field=field,value=value:rolecase(recordedit=lambda n,x:x.update({field:value}) if n==browser['actual_execution'] else None),True)
  failurelo=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='failed_name' for t in n.targets));failurehi=next(i for i,n in enumerate(body[failurelo:],failurelo) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='expected' for t in n.targets));failurecode=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[failurelo:failurehi]),type_ignores=[])),name,'exec')
  case('main genuine stage3 failure retained strict1 with actual command/helper/raw',lambda:exec(failurecode,{**realns,'extra':set()}))
  case('main old failed stage3 cannot enter actual0 gate',lambda:realns['actual']('reports/full-coverage/stage-publication26-execution-v1.json'),True)
  assets={n:H(ROOT/n) for n in json.loads((ROOT/'reports/full-coverage/checkpoint-25-manifest.json').read_text())['frozen_inputs_sha256'] if n.startswith('SafeLearning/')}
  browsername='reports/full-coverage/browser-checkpoint-26.json';browser=json.loads((ROOT/browsername).read_text())
  lo=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='browser_name' for t in n.targets));hi=next(i for i,n in enumerate(body[lo:],lo) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='progress' for t in n.targets))
  code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[lo:hi]),type_ignores=[])),name,'exec')
  def browsercase(edit):
   d=copy.deepcopy(browser);edit(d);env={'assets':assets,'read':lambda n:d if n==browsername else json.loads((ROOT/n).read_text()),'sha':H,'safe':lambda n:ROOT/n,'target':lambda n:PUB/n,**c};exec(code,env)
  case('main genuine current53 browser5fresh140retained/manual6 read-only',lambda:browsercase(lambda d:None))
  for field,value in [('status','pending'),('coverage_complete',True),('page_count',28),('verified_viewport_count',144),('fresh_verified_viewport_count',4),('retained_verified_viewport_count',141),('screenshot_count',47),('skipped_capture_target_count',9),('source_sha256',{})]:
   case('main browser rejects '+field,lambda field=field,value=value:browsercase(lambda d:d.update({field:value})),True)
  case('main browser whole48 manual approval cannot be inferred',lambda:browsercase(lambda d:d['manual_visual_inspection'].update(status='passed')),True)
  paths=set();realns['add_refs'](browser,paths);realns['add_refs'](json.loads((ROOT/browser['fresh_run_inputs']).read_text()),paths)
  closures.update({n:H(ROOT/n) for n in paths});case('main real browser typed nested refs read-only',lambda:None)
 else:
  lo=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='assets' for t in n.targets));hi=next(i for i,n in enumerate(body[lo:],lo) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='audit_name' for t in n.targets))
  code=compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(body[lo:hi]),type_ignores=[])),name,'exec');aa={'SafeLearning/'+str(i)+'.html':str(i).zfill(64) for i in range(31)};live={'assets':[{'source':n,'expected_sha256':h,'actual_sha256':h,'http_status':200,'matches':True} for n,h in aa.items()]}
  def livecase(edit):
   d=copy.deepcopy(live);edit(d);exec(code,{'manifest':{'frozen_inputs_sha256':aa},'live':d,'sha':lambda n:aa[n],'safe':lambda n:n,'target':lambda n:n})
  case('metadata exact31 hypothetical future live hashes accepted',lambda:livecase(lambda d:None))
  for k,v in [('expected_sha256','f'*64),('actual_sha256','f'*64),('http_status',404),('matches',False),('source','SafeLearning/unlisted.html')]:
   case('metadata live change rejected '+k,lambda k=k,v=v:livecase(lambda d:d['assets'][1].update({k:v})),True)
  case('metadata duplicate live source rejected',lambda:livecase(lambda d:d['assets'].__setitem__(1,copy.deepcopy(d['assets'][0]))),True)
 observations[kind]={'status':'independent_full_publication26_'+kind+'_stager_code_and_native_schema_fixtures_passed','errors':[],'reviewer':'Independent Foundations agent; Root authored v4; all original v3/v2 decisions remain unchanged','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':name,'sha256':expected},'helper_sha256':expected,'full_code_and_v3_to_v4_delta_read':True,'exact_v4_main_inverse_to_original_v3_verified':True,'original_v3_review':{'file':oldpeername,'sha256':oldpeerhash},'entire_original_v3_review_body':oldpeer,'all_reusable_function_ASTs_unchanged_from_unexecuted_v1':True,'original_unexecuted_v1_helper':{'file':str(basepath.relative_to(ROOT)),'sha256':H(basepath)},'fixture_count':len(cases)-start,'fixtures':cases[start:],'actual_existing_typed_reference_closure_checked_read_only_sha256':closures,'new116_config_helper_and_expected_native_v1_paths_bound':True,'actual_main_metadata_producer_or_publication_executed':False,'scope':'Full code/delta review with isolated synthetic path, schema, exit, alias, dirty, budget and live-map fixtures plus read-only actual current browser/peer evidence. No audit26, prepared PUB26, config26 execution, Git publication stage, Pages or live26 result is inferred; all actual runtime prerequisites remain mandatory.'}
# Real temporary Git fixture checks force staging ignored logs under the same exact NUL whitelist.
with tempfile.TemporaryDirectory(prefix='foundation26-explicit-ignored-log-fixture-') as td:
 p=Path(td);subprocess.run(['git','init','-q'],cwd=p,check=True);(p/'.gitignore').write_text('*.log\n');(p/'actual.log').write_text('isolated actual fixture\n');(p/'unrelated.txt').write_text('excluded\n');subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=p,input=b'.gitignore\0actual.log\0',check=True);st=set(subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=p,check=True,capture_output=True).stdout.split(b'\0'))-{b''};assert st=={b'.gitignore',b'actual.log'}
for d in observations.values():d['real_temporary_git_exact_force_NUL_ignored_log_regression_passed']=True
out=Path('/tmp/publication26-two-stagers-independent-foundations-observations-v4.json');assert not out.exists();out.write_text(json.dumps(observations,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','fixtures':len(cases),'observation':str(out),'sha256':H(out)}))
