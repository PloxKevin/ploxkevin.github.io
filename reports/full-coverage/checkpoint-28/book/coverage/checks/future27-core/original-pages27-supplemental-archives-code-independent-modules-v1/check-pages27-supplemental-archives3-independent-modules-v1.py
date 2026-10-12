from pathlib import Path
from datetime import datetime, timezone
import ast,copy,hashlib,json,os,runpy,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/checks/root_prepare_pages27_supplemental_archives_v3.py'
OLD='book/coverage/checks/root_prepare_pages27_supplemental_archives_v2.py'
OUT=Path('/tmp/pages27-supplemental-archives3-independent-modules-code-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
assert sha(ROOT/HELPER)=='9b06ca5c50a93cae79a5a02bd8dd13400b2a69f331c013eb8a635812476377c0'
assert sha(ROOT/OLD)=='97472d2120970e89a97cdab394ab9e5c6d6f3e67b8081adfe30e5f7507891191'
source=(ROOT/HELPER).read_text();old=(ROOT/OLD).read_text()
# The complete original helper remains unchanged; compare the exact final delta.
restored=source.replace('_archives_v3.py','_archives_v2.py')
a=restored.index(" assert actual['status']=='passed'\n")
b=restored.index(" assert actual['helper_sha256_before']",a)
old_a=old.index(" assert actual['status']=='passed' and type(actual['actual_exit_code'])")
old_b=old.index(" assert actual['helper_sha256_before']",old_a)
restored=restored[:a]+old[old_a:old_b]+restored[b:]
a=restored.index(" assert sha(safe(ROOT,INPUTS))==")
b=restored.index(" for n,h in expected.items():",a)
old_a=old.index(" inputs=read(INPUTS);assert inputs['unresolved_references']==[]")
old_b=old.index(" for n,h in expected.items():",old_a)
restored=restored[:a]+old[old_a:old_b]+restored[b:]
restored=restored.replace("  assert not p.is_symlink(),n\n  if p.is_file():included+=p.stat().st_size","  if p.is_file():assert not p.is_symlink();included+=p.stat().st_size")
assert restored==old
ns=runpy.run_path(str(ROOT/HELPER),run_name='independent_read_only_module')
prepare=next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef)and n.name=='prepare')
body=prepare.body
actual_start=next(i for i,n in enumerate(body)if isinstance(n,ast.Assert)and ast.unparse(n.test)=="actual['status'] == 'passed'")
input_start=next(i for i,n in enumerate(body)if isinstance(n,ast.Assert)and 'd3a35541' in ast.unparse(n))
input_end=next(i for i,n in enumerate(body)if isinstance(n,ast.For)and ast.unparse(n.iter)=='expected.items()')
def extracted(name,stmts,args):
    fn=ast.FunctionDef(name=name,args=ast.arguments(posonlyargs=[],args=[ast.arg(arg=a)for a in args],kwonlyargs=[],kw_defaults=[],defaults=[]),body=copy.deepcopy(stmts),decorator_list=[])
    tree=ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[]));space=dict(ns)
    exec(compile(tree,str(ROOT/HELPER)+':extracted_exact_guard','exec'),space);return space[name],space
actual_guard,_=extracted('actual_guard',body[actual_start:input_start],['actual','prior'])
input_guard,ig=extracted('input_guard',body[input_start:input_end],[])
prior=json.loads((ROOT/'reports/full-coverage/pages27-config-preparation-v1.json').read_bytes())
actual=json.loads((ROOT/'reports/full-coverage/pages27-config-execution-v2.json').read_bytes())
cases=[]
def accept(label,f):f();cases.append({'case':label,'expected':'accept','actual':'accepted'})
def reject(label,f):
    try:f()
    except (AssertionError,KeyError,TypeError,ValueError):cases.append({'case':label,'expected':'reject','actual':'rejected'});return
    raise AssertionError('Unexpected accept: '+label)
accept('real native actual config5 strict contract',lambda:actual_guard(actual,prior))
equal=copy.deepcopy(actual);equal.update(exit_code=0,command=actual['actual_command'],cwd=str(ROOT),working_directory=str(ROOT),raw_log=actual['log'],raw_log_sha256=actual['log_sha256'])
accept('all present native aliases agree',lambda:actual_guard(equal,prior))
for key,value in [('exit_code',False),('exit_code','0'),('exit_code',1),('actual_exit_code',False),('command',['wrong']),('actual_command',['wrong']),('cwd','/tmp'),('working_directory','/tmp'),('raw_log','reports/wrong.log'),('raw_log_sha256','0'*64),('status','pending')]:
    v=copy.deepcopy(equal);v[key]=value;reject('native alias rejects '+key+':'+repr(value),lambda v=v:actual_guard(v,prior))
inputs=json.loads((ROOT/ns['INPUTS']).read_bytes())
accept('actual pinned singleton input plan body',input_guard)
original_read=ig['read'];original_sha=ig['sha']
for key,value in [('status','pending'),('coverage_complete',True),('coverage_complete',0),('unresolved_references',['missing']),('supplemental_inputs_sha256',list(inputs['supplemental_inputs_sha256'])),('supplemental_inputs_sha256',{})]:
    bad=copy.deepcopy(inputs);bad[key]=value;ig['read']=lambda n,bad=bad:bad
    reject('input body rejects '+key+':'+type(value).__name__,input_guard)
ig['read']=original_read;ig['sha']=lambda p:'0'*64
reject('input exact byte SHA drift',input_guard);ig['sha']=original_sha
loop_start=next(i for i,n in enumerate(body)if isinstance(n,ast.Assign)and ast.unparse(n)=='included = 0')
loop_end=next(i for i,n in enumerate(body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='delta'for t in n.targets))
counter, cg=extracted('count_included',body[loop_start:loop_end]+[ast.Return(value=ast.Name(id='included',ctx=ast.Load()))],['excluded'])
with tempfile.TemporaryDirectory(prefix='supplemental27-fixtures-',dir='/tmp')as tmp:
    t=Path(tmp);cg['PUB']=t
    (t/'included.txt').write_bytes(b'abc');(t/'outside').mkdir();(t/'outside'/'file.txt').write_bytes(b'abcdef')
    (t/'excluded').mkdir();(t/'excluded'/'alias').symlink_to(t/'outside',target_is_directory=True)
    accept('excluded directory symlink skipped before rejection',lambda:counter({'excluded'}))
    assert counter({'excluded'})==9
    (t/'include-dir').symlink_to(t/'outside',target_is_directory=True)
    reject('included directory symlink rejected',lambda:counter({'excluded'}));(t/'include-dir').unlink()
    (t/'include-file').symlink_to(t/'outside'/'file.txt');reject('included file symlink rejected',lambda:counter({'excluded'}));(t/'include-file').unlink()
    for n in ('../escape','/absolute','unsafe*glob','bad\nline','bad\0nul'):
        reject('unsafe canonical path '+repr(n),lambda n=n:ns['safe'](t,n))
    accept('safe ordinary canonical path',lambda:ns['safe'](t,'included.txt'))
accept('exact exclusion descendants omitted',lambda: (_ for _ in ()).throw(AssertionError())if ns['kept']('archive/nested/a',{'archive'})else None)
accept('similar sibling prefix stays public',lambda: (_ for _ in ()).throw(AssertionError())if not ns['kept']('archive-other/a',{'archive'})else None)
for original,r in inputs['original_byte_aliases'].items():
    assert type(r)is dict and set(r)=={'file','sha256'}
    assert sha(ns['safe'](ROOT,r['file']))==r['sha256'],original
native_before={n:sha(ROOT/n)for n in ('book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json','book/coverage/material-corrections.json',HELPER,OLD,ns['INPUTS'])}
config_before=sha(ns['PUB']/'_config.yml')
report_paths=[ns['safe'](base,n)for base in (ROOT,ns['PUB'])for n in (ns['REPORT'],ns['BACKUP'])]
assert all(not p.exists()for p in report_paths)
start=datetime.now(timezone.utc).isoformat();after,payload,previous=ns['prepare']();native=json.loads(payload)
assert len(native['exclusions'])==native['excluded_count']==133
assert set(native['new_literal_exclusions'])==ns['ADDED']|{ns['GENERATED_METADATA_EXCLUSION']}
assert set(native['exclusions'])==set(prior['exclusions'])|set(native['new_literal_exclusions'])
assert native['required_publication_files_sha256']==prior['required_publication_files_sha256']and len(native['required_publication_files_sha256'])==1284
assert previous==(ns['PUB']/'_config.yml').read_bytes()and sha(ns['PUB']/'_config.yml')==config_before==ns['BEFORE']
assert all(not p.exists()for p in report_paths)
assert native_before=={n:sha(ROOT/n)for n in native_before}
# Independent os.walk budget, including the exact prospective 211 copies.
excluded=set(native['exclusions']);kept=lambda n:not any(n==e or n.startswith(e+'/')for e in excluded)
included=0
for directory,dirs,files in os.walk(ns['PUB'],followlinks=False):
    d=Path(directory);dirs[:]=[n for n in dirs if n!='.git'and kept((d/n).relative_to(ns['PUB']).as_posix())]
    for n in dirs:assert not (d/n).is_symlink()
    for name in files:
        p=d/name;n=p.relative_to(ns['PUB']).as_posix()
        if kept(n):assert not p.is_symlink();included+=p.stat().st_size
delta=sum((ROOT/n).stat().st_size-((ns['PUB']/n).stat().st_size if (ns['PUB']/n).is_file()else 0)for n in inputs['supplemental_inputs_sha256']if kept(n))
total=included+delta-len(previous)+len(after)
assert total==native['prospective_website_bytes_with_explicit_supplemental_copy']
assert total+len(payload)+131072<850000000
closure={n:sha(ROOT/n)for n in (HELPER,OLD,ns['INPUTS'],'reports/full-coverage/pages27-config-preparation-v1.json','reports/full-coverage/pages27-config-execution-v2.json','book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json','reports/full-coverage/checkpoint-27-manifest.json')}
closure.update(inputs['supplemental_inputs_sha256'])
out={'status':'passed_independent_checkpoint27_supplemental_archive_helper_code_review','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':start,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'helper_sha256':sha(ROOT/HELPER),'entire_helper_read':source,'exact_reverse_to_preserved_helper2':True,'preserved_helper2':ref(OLD),'targeted_fixtures':cases,'fixture_count':len(cases),'real_read_only_prepare_passed':True,'entire_real_prospective_native_report_and_time':native,'excluded_count':133,'input_plan':ref(ns['INPUTS']),'supplemental_inputs_count':211,'original_byte_aliases_count':len(inputs['original_byte_aliases']),'all_original_byte_aliases_current_hashes_verified':True,'independent_prospective_website_bytes':total,'independent_prospective_bytes_with_native_report_and_reserve':total+len(payload)+131072,'new_literal_exclusions':native['new_literal_exclusions'],'required_publication_files_sha256':native['required_publication_files_sha256'],'closed_evidence_sha256':closure,'scope':'Independent full-code/exact-delta and extracted actual guard fixtures, then actual read-only prepare and independently counted prospective website bytes. Existing 129 configuration/report/actual-output review bodies and times remain unchanged. All helper-produced destinations/config/owners remain unchanged. No apply, stage, Git, Pages or delivery claim.'}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'findings':{'file':str(OUT),'sha256':sha(OUT)},'fixtures':len(cases),'prospective_bytes':total}))
