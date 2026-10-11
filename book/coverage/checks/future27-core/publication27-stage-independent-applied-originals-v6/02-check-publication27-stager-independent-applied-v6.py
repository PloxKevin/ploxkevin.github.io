from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_stage_publication27_v6.py')
OUT=Path('/tmp/publication27-stager-independent-applied-observations-v6.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HELPER)=='cc27c980d6393367e58f90e652e8c924c174dcd7ee4e656f53bf4e3548bc0e1c'
source=HELPER.read_text();tree=ast.parse(source)
def function(t,n):return next(x for x in t.body if isinstance(x,ast.FunctionDef) and x.name==n)
old4=ast.parse(Path('/tmp/root_stage_publication27_v4.py').read_text())
for n in ['safe','read','zero','actual','closed_peer','dirty','staged','main']:
 assert ast.dump(function(tree,n),include_attributes=False)==ast.dump(function(old4,n),include_attributes=False),n
old5=Path('/tmp/root_stage_publication27_v5.py').read_text()
reverse=source.replace('root_stage_publication27_v6.py','root_stage_publication27_v5.py').replace('root_prepare_pages27_supplemental_archives_v3.py','root_prepare_pages27_supplemental_archives_v2.py').replace('9b06ca5c50a93cae79a5a02bd8dd13400b2a69f331c013eb8a635812476377c0','97472d2120970e89a97cdab394ab9e5c6d6f3e67b8081adfe30e5f7507891191')
assert reverse==old5
def is_assignment(n,name):return isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets)
p6=function(tree,'prepare').body;p4=function(old4,'prepare').body
start6=next(i for i,n in enumerate(p6) if is_assignment(n,'base_config'))
start4=next(i for i,n in enumerate(p4) if is_assignment(n,'config'))
end6=next(i for i,n in enumerate(p6) if is_assignment(n,'production_peer_name'))
end4=next(i for i,n in enumerate(p4) if is_assignment(n,'production_peer_name'))
dump=lambda nodes:ast.dump(ast.Module(body=nodes,type_ignores=[]),include_attributes=False)
assert dump(p6[:start6])==dump(p4[:start4])
assert dump(p6[end6:-2])==dump(p4[end4:-2])
assert dump(p6[-1:])==dump(p4[-1:])
assert ast.unparse(p6[-2])=="assert 0 <= included + delta + (len(payload) if kept(REPORT) else 0) < BUDGET"
ns={'__name__':'isolated_review','__file__':str(HELPER)};exec(compile(source,str(HELPER),'exec'),ns)
oldns={'__name__':'isolated_prior','__file__':'/tmp/root_stage_publication27_v4.py'};exec(compile(Path('/tmp/root_stage_publication27_v4.py').read_text(),'/tmp/root_stage_publication27_v4.py','exec'),oldns)
overlay_execution='reports/full-coverage/pages27-supplemental-archive-configuration-execution-v1.json'
assert {k:v for k,v in ns['REQUIRED_EXECUTIONS'].items() if k!=overlay_execution}==oldns['REQUIRED_EXECUTIONS']
assert len(ns['REQUIRED_EXECUTIONS'])==18
config_guard=ast.FunctionDef(name='configuration_guard',args=ast.arguments(posonlyargs=[],args=[ast.arg(arg=x) for x in ['plan','expected','paths','manifest']],kwonlyargs=[],kw_defaults=[],defaults=[]),body=copy.deepcopy(p6[start6:end6]),decorator_list=[])
guard_tree=ast.fix_missing_locations(ast.Module(body=[config_guard],type_ignores=[]));exec(compile(guard_tree,'exact_config_guard','exec'),ns)
budget_tree=ast.fix_missing_locations(ast.Module(body=[copy.deepcopy(p6[-2])],type_ignores=[]));budget_code=compile(budget_tree,'exact_budget_guard','exec')
fixtures=[]
def reject(label,fn):
 try:fn()
 except (AssertionError,KeyError,FileNotFoundError,ValueError,TypeError):fixtures.append({'fixture':label,'result':'rejected'});return
 raise AssertionError('unexpected acceptance '+label)
def accept(label,fn):fn();fixtures.append({'fixture':label,'result':'accepted'})
with tempfile.TemporaryDirectory(prefix='publication27-overlay133-guards-') as td:
 r=Path(td)/'root';p=Path(td)/'pub';r.mkdir();p.mkdir();ns['ROOT']=r;ns['PUB']=p
 def put(n,b,root=r):
  q=root/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b if isinstance(b,bytes) else (json.dumps(b,separators=(',',':'))+'\n').encode());return q
 base_n='reports/full-coverage/pages27-config-preparation-v1.json';new_n='reports/full-coverage/pages27-supplemental-archive-configuration-v1.json'
 base=json.loads((ROOT/base_n).read_bytes());assert len(base['required_publication_files_sha256'])==1284
 # Exact current base129 native/config bytes; only required download body mapping is a labelled one-physical-file synthetic adapter. No future approval is claimed.
 base['required_publication_files_sha256']={'downloads/synthetic-retained.html':hashlib.sha256(b'synthetic download\n').hexdigest()}
 put('downloads/synthetic-retained.html',b'synthetic download\n',p)
 backup='reports/full-coverage/pages27-supplemental-archive-previous-original-v1.yml'
 header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
 base_config=(header+''.join('  - '+n+'\n' for n in sorted(base['exclusions']))).encode();assert hashlib.sha256(base_config).hexdigest()==base['config_sha256']
 put(backup,base_config);put(base_n,base)
 added={'book/coverage/checks/future27-core/original-documentation27-foundations-review-v1','book/coverage/checks/future27-core/original-pages27-config5-actual-output-independent-modules-v2','reports/full-coverage/working-inventory55-timestamp-regeneration-before-restoration28-v1.json',ns['REPORT']}
 exclusions=sorted(set(base['exclusions'])|added);assert len(exclusions)==133
 after=(header+''.join('  - '+n+'\n' for n in exclusions)).encode();put('_config.yml',after,p)
 helper3='book/coverage/checks/root_prepare_pages27_supplemental_archives_v3.py';put(helper3,(ROOT/helper3).read_bytes());assert sha(r/helper3)=='9b06ca5c50a93cae79a5a02bd8dd13400b2a69f331c013eb8a635812476377c0'
 config={'status':'passed_exact_checkpoint27_supplemental_archive_configuration_requires_actual_stage_and_pages','coverage_complete':False,'previous_configuration_report':{'file':base_n,'sha256':sha(r/base_n)},'previous_configuration':{'file':backup,'sha256':base['config_sha256']},'exclusions':exclusions,'new_literal_exclusions':sorted(added),'excluded_count':133,'required_publication_files_sha256':base['required_publication_files_sha256'],'required_download_count':1284,'website_budget_bytes':850000000,'config_sha256':sha(p/'_config.yml'),'helper':{'file':helper3,'sha256':sha(r/helper3)}}
 put(new_n,config)
 closure='fixtures/synthetic-closed-review.json';put(closure,b'{"synthetic_future_peer_only":true}\n');h=sha(r/closure)
 configpeer_n='book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json'
 overlaypeer_n='book/coverage/checks/future27-core/pages27-supplemental-archives-independent-modules-output-v1.json'
 configpeer={'status':'passed_independent_actual_checkpoint27_pages_configuration','errors':[],'helper':base['helper'],'config_sha256':base['config_sha256'],'excluded_count':129,'closed_evidence_sha256':{closure:h}}
 overlaypeer={'status':'passed_independent_actual_checkpoint27_supplemental_archive_configuration','errors':[],'helper':config['helper'],'config_sha256':config['config_sha256'],'excluded_count':133,'closed_evidence_sha256':{closure:h}}
 put(configpeer_n,configpeer);put(overlaypeer_n,overlaypeer)
 plan={'original_byte_aliases':{}};expected={closure:h};paths=set();manifest={'working_inputs_sha256':{}}
 run=lambda:ns['configuration_guard'](plan,expected,paths,manifest)
 accept('exact synthetic base129 to overlay133 including excluded native whitelist metadata',run)
 def mutate_file(label,name,body,mutator):
  bad=copy.deepcopy(body);mutator(bad);put(name,bad);reject(label,run);put(name,body)
 for label,mutation in [
  ('base failed status',lambda d:d.update(status='failed')),('base129 count drift',lambda d:d.update(excluded_count=128)),('wrong exact base config hash',lambda d:d.update(config_sha256='0'*64)),('base helper path changed',lambda d:d['helper'].update(file='unrelated.py')),('base helper digest changed',lambda d:d['helper'].update(sha256='0'*64))]:mutate_file(label,base_n,base,mutation)
 for label,mutation in [
  ('overlay failed status',lambda d:d.update(status='failed')),('overlay falsely whole coverage',lambda d:d.update(coverage_complete=True)),('wrong prior native report hash',lambda d:d['previous_configuration_report'].update(sha256='0'*64)),('wrong prior native report path',lambda d:d['previous_configuration_report'].update(file='elsewhere.json')),('wrong previous config hash',lambda d:d['previous_configuration'].update(sha256='0'*64)),('prior config backup traversal',lambda d:d['previous_configuration'].update(file='../escape.yml')),('missing one exact added exclusion',lambda d:d['exclusions'].remove(ns['REPORT'])),('unauthorized fifth exclusion',lambda d:d['exclusions'].append('current-downloads')),('duplicate exclusion',lambda d:d['exclusions'].append(d['exclusions'][0])),('changed new literal set',lambda d:d['new_literal_exclusions'].pop()),('unsorted new literal list',lambda d:d.update(new_literal_exclusions=list(reversed(d['new_literal_exclusions'])))),('required download map changed',lambda d:d['required_publication_files_sha256'].update({'extra':'0'*64})),('required count1284 drift',lambda d:d.update(required_download_count=1283)),('overlay133 count drift',lambda d:d.update(excluded_count=132)),('website budget changed',lambda d:d.update(website_budget_bytes=900000000)),('wrong current config digest',lambda d:d.update(config_sha256='0'*64)),('wrong designated overlay helper path',lambda d:d['helper'].update(file='book/coverage/checks/root_prepare_pages27_supplemental_archives_v2.py')),('wrong designated overlay helper hash',lambda d:d['helper'].update(sha256='0'*64))]:mutate_file(label,new_n,config,mutation)
 for name,body in [(configpeer_n,configpeer),(overlaypeer_n,overlaypeer)]:
  for label,mutation in [('failed peer status',lambda d:d.update(status='failed')),('peer errors nonempty',lambda d:d.update(errors=['bad'])),('missing peer errors',lambda d:d.pop('errors')),('empty closed evidence',lambda d:d.update(closed_evidence_sha256={})),('closed digest drift',lambda d:d.update(closed_evidence_sha256={closure:'0'*64})),('wrong peer helper',lambda d:d['helper'].update(sha256='0'*64)),('wrong peer config hash',lambda d:d.update(config_sha256='0'*64)),('wrong peer count',lambda d:d.update(excluded_count=0))]:mutate_file(label+' '+name,name,body,mutation)
 original=(p/'_config.yml').read_bytes();put('_config.yml',b'stale PUB config',p);reject('stale PUB config bytes',run);put('_config.yml',original,p)
 put(backup,b'stale old backup');reject('stale prior config backup bytes',run);put(backup,base_config)
 put('downloads/synthetic-retained.html',b'stale required download',p);reject('required retained download byte drift',run);put('downloads/synthetic-retained.html',b'synthetic download\n',p)
 (r/closure).unlink();(r/closure).symlink_to(r/backup);reject('closed evidence final symlink',run);(r/closure).unlink();put(closure,b'{"synthetic_future_peer_only":true}\n')
 log=overlay_execution.replace('.json','.log');put(log,b'synthetic eighteenth native wrapper; helper never invoked\n')
 command=ns['REQUIRED_EXECUTIONS'][overlay_execution]
 native={'status':'passed','actual_exit_code':0,'exit_code':0,'actual_command':command,'command':command,'actual_workdir':str(r),'cwd':str(r),'helper_sha256_before':{helper3:sha(r/helper3)},'helper_sha256_after':{helper3:sha(r/helper3)},'log':log,'raw_log':log,'log_sha256':sha(r/log),'raw_log_sha256':sha(r/log)}
 put(overlay_execution,native);native_run=lambda:ns['actual'](overlay_execution,command)
 accept('synthetic eighteenth actual wrapper strict exact overlay3 family',native_run)
 for label,mutation in [('false bool exit',lambda d:d.update(actual_exit_code=False)),('conflicting fail exit alias',lambda d:d.update(exit_code=1)),('failed wrapper status',lambda d:d.update(status='failed')),('wrong actual command',lambda d:d.update(actual_command=['python3','wrong.py','--apply'])),('conflicting command alias',lambda d:d.update(command=['python3','wrong.py'])),('wrong workdir alias',lambda d:d.update(cwd='/tmp/other')),('missing designated helper',lambda d:d.update(helper_sha256_before={log:sha(r/log)},helper_sha256_after={log:sha(r/log)})),('non-dict before map',lambda d:d.update(helper_sha256_before=[])),('wrong helper hash',lambda d:d.update(helper_sha256_before={helper3:'0'*64},helper_sha256_after={helper3:'0'*64})),('wrong raw log alias',lambda d:d.update(raw_log='other.log')),('wrong raw hash alias',lambda d:d.update(raw_log_sha256='0'*64))]:
  bad=copy.deepcopy(native);mutation(bad);put(overlay_execution,bad);reject('eighteenth '+label,native_run);put(overlay_execution,native)
 (r/overlay_execution).unlink();reject('absent eighteenth actual record remains pending rejection',native_run);put(overlay_execution,native)
 def budget(included,delta,payload,keep):exec(budget_code,dict(ns,included=included,delta=delta,payload=payload,kept=lambda n:keep))
 accept('excluded whitelist record not counted as website payload',lambda:budget(849999999,0,b'x'*200,False))
 reject('included whitelist record would exceed unchanged850M budget',lambda:budget(849999999,0,b'x'*200,True))
 reject('exact850M website boundary rejected',lambda:budget(850000000,0,b'',False))
 reject('negative replacement projection rejected',lambda:budget(2,-3,b'',False))
 accept('excluded payload plus included replacement delta within budget',lambda:budget(837725113,100000,b'x'*50000000,False))
 assert not (r/ns['REPORT']).exists() and not (p/ns['REPORT']).exists()
ns['ROOT']=ROOT;ns['PUB']=ROOT/'reports/book/publication-repo'
native=[];pending=[]
for name,command in ns['REQUIRED_EXECUTIONS'].items():
 if not (ROOT/name).exists():pending.append(name);continue
 d=ns['actual'](name,command);native.append({'file':name,'sha256':sha(ROOT/name),'helper':command[1],'status':d['status'],'actual_exit_code':d.get('actual_exit_code'),'raw_log_sha256':d['log_sha256']})
for name in ['book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json','book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json']:
 d=ns['read'](name);assert d['errors']==[]
 for original,h in d['closed_evidence_sha256'].items():
  if Path(original).is_absolute():
   if 'original_closed_byte_aliases' in d:row=d['original_closed_byte_aliases'][original]
   else:row=ns['read']('book/coverage/checks/future27-core/original-independent-module-production-output-peer-v1/original-closed-byte-aliases-v1.json')['original_closed_byte_aliases'][original]
   assert row['sha256']==h;original=row['file']
  assert sha(ns['safe'](ROOT,original))==h,original
prior=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v4.json'
result={'status':'passed_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'fixture_count':len(fixtures),'fixtures':fixtures,'native_read_only_families':native,'pending_actual_families':pending,'prior_v4_full_body_and_time':json.loads(prior.read_bytes()),'prior_v4_ref':{'file':str(prior),'sha256':sha(prior)},'whole_v5_to_v6_reverse_exact':True,'configuration_guard_ast_extraction_exact':True,'unchanged_core_main_and_raw_owner_routing_ast':True,'production_helper_execution':False,'production_pub_or_git_mutation':False,'scope':'Whole v6 source/delta read with exact AST-extracted configuration and budget guards plus exact actual()/closed_peer() functions in synthetic TMP root/PUB. Synthetic future overlay peer and18th wrapper do not assert production execution. Base129 current native and exact original config bytes are used; required1284 metadata with one physical synthetic required download is an explicitly labelled adapter. Prior61+33+28 full prepare/routing fixtures and original body/time are retained, not rerun or counted as new. Real available execution records and both current closed peer maps are read-only rehashed. No production prepare/main, producer copy, PUB/Git or website action.'}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixture_count':len(fixtures),'observations':str(OUT),'sha256':sha(OUT),'actual_native_families':len(native),'pending_actual_families':pending}))
