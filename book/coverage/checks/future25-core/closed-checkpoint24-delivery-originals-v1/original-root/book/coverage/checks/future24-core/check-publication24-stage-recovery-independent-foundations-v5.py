"""Read-only actual recovery preflight and isolated rejection fixtures; no stage execution."""
from pathlib import Path
from datetime import datetime,timezone
from types import SimpleNamespace
import ast,copy,json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
HELPER=ROOT/'book/coverage/checks/root_stage_publication24_recovery_v5.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
src=HELPER.read_text();tree=ast.parse(src)
assert H(HELPER)=='dfddae1d82dd15e5432df357a2f6d9eef54d65b85050db93fa39c5aab6aa04dd'
ns={'ROOT':ROOT,'PUB':ROOT/'reports/book/publication-repo','Path':Path,'json':json,'hashlib':hashlib,'subprocess':__import__('subprocess'),'__file__':str(HELPER),'REPORT':'reports/full-coverage/publication24-prestage-v3.json','OLD':'reports/full-coverage/publication24-prestage-v2.json','FAILED':'reports/full-coverage/stage-publication24-execution-v2.json','PEER':'book/coverage/checks/future24-core/publication24-stage-recovery-independent-review-v5.json','SELF':str(HELPER.relative_to(ROOT))}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef)],type_ignores=[]),str(HELPER),'exec'),ns)
prefix=src[src.index('assert not safe(REPORT)'):src.index('peer=read(PEER)')]
# This exact original prefix only reads ROOT/PUB/Git status; its first copy is later.
exec(compile(prefix,str(HELPER),'exec'),ns)
assert len(ns['expected'])==45213
cases=[]
def case(name,body,reject=False):
 try:body()
 except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):assert reject,name;cases.append({'fixture':name,'observed':'rejected'})
 else:assert not reject,name;cases.append({'fixture':name,'observed':'accepted'})
for p in ['/tmp/out','../outside','bad\0path','bad\npath','bad\rpath']:
 case('reject_unsafe_closure_'+repr(p),lambda p=p:ns['safe'](p),True)
case('canonical_closed_path',lambda:ns['safe'](str(HELPER.relative_to(ROOT))))
failed_block=src[src.index('failed=read(FAILED)'):src.index('manifest=read(')]
original_failed=copy.deepcopy(ns['failed'])
def failure_fixture(edit):
 local=dict(ns);obj=copy.deepcopy(original_failed);edit(obj)
 local['read']=lambda n:obj
 exec(compile(failed_block,str(HELPER),'exec'),local)
case('actual_stage4_failure_retained_as_exit1',lambda:failure_fixture(lambda x:None))
case('reject_failed_execution_relabeled_zero',lambda:failure_fixture(lambda x:x.update(actual_exit_code=0)),True)
case('reject_boolean_exit',lambda:failure_fixture(lambda x:x.update(actual_exit_code=True)),True)
case('reject_wrong_executed_helper_command',lambda:failure_fixture(lambda x:x.update(actual_command=['python3','other.py'])),True)
case('reject_changed_executed_helper_digest',lambda:failure_fixture(lambda x:x.update(helper_sha256_after={})),True)
case('reject_failed_rawlog_digest',lambda:failure_fixture(lambda x:x.update(log_sha256='0'*64)),True)
# Run the exact read-only closure and dirty/index gates using a clearly synthetic future peer.
closure=src[src.index('peer=read(PEER)'):src.index('for n in extra:')]
fixture_peer={'status':'synthetic_fixture_passed','errors':[],'helper_sha256':H(HELPER),'closed_evidence_sha256':{str(HELPER.relative_to(ROOT)):H(HELPER)}}
def closure_fixture(edit=None,dirty=None,index=None):
 local=dict(ns);p=copy.deepcopy(fixture_peer)
 if edit:edit(p)
 local['read']=lambda n:p;local['changed']=lambda:set() if dirty is None else set(dirty);local['staged']=lambda:set() if index is None else set(index)
 exec(compile(closure,str(HELPER),'exec'),local)
case('synthetic_future_peer_canonical_closure_and_original_partial_index',lambda:closure_fixture(index=set(ns['staged']())))
case('reject_peer_errors',lambda:closure_fixture(lambda p:p.update(errors=['problem'])),True)
case('reject_wrong_peer_helper_digest',lambda:closure_fixture(lambda p:p.update(helper_sha256='0'*64)),True)
case('reject_absolute_closed_evidence',lambda:closure_fixture(lambda p:p.update(closed_evidence_sha256={'/tmp/out':'0'*64})),True)
case('reject_changed_closed_evidence_digest',lambda:closure_fixture(lambda p:p.update(closed_evidence_sha256={str(HELPER.relative_to(ROOT)):'0'*64})),True)
case('reject_outside_dirty_path',lambda:closure_fixture(dirty={'outside.json'}),True)
case('reject_outside_already_staged_path',lambda:closure_fixture(index={'outside.json'}),True)
# The actual parser functions execute with isolated subprocess responses only.
def status_fixture(raw):
 local=dict(ns);local['subprocess']=SimpleNamespace(run=lambda *a,**k:SimpleNamespace(stdout=raw))
 exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name in ['changed','staged']],type_ignores=[]),str(HELPER),'exec'),local)
 return local['changed']()
case('tracked_and_untracked_whitelist_status',lambda:status_fixture(b' M SafeLearning/landscape.html\0?? some file.json\0'))
for st in [b' D ',b'R  ',b' R ',b'C  ',b' C ']:case('reject_deleted_or_renamed_status_'+repr(st),lambda st=st:status_fixture(st+b'file\0'),True)
# Verify the copied-byte loop on isolated in-memory file stand-ins, without copying anything.
loop=src[src.index('for n in sorted(paths):'):src.index('assets={')]
class P:
 def __init__(self,side,path):self.side=side;self.path=str(path)
 def __truediv__(self,n):return P(self.side,n)
 def is_file(self):return True
 def is_symlink(self):return False
 def __str__(self):return self.side+':'+self.path
def file_fixture(rootdigest,pubdigest,frozen=None):
 local={'paths':{'file'},'old':{'config_sha256':'unused'},'manifest':{'frozen_inputs_sha256':{} if frozen is None else {'file':frozen}},'expected':{},'PUB':P('pub',''),'safe':lambda n:P('root',n),'sha':lambda p:rootdigest if p.side=='root'else pubdigest}
 exec(compile(loop,str(HELPER),'exec'),local)
case('current_closed_root_copy_matches_publication',lambda:file_fixture('a','a'))
case('frozen_scope_uses_frozen_hash_instead_of_changed_working_root',lambda:file_fixture('working','frozen','frozen'))
case('reject_publication_copy_changed',lambda:file_fixture('a','b'),True)
case('reject_publication_frozen_hash_changed',lambda:file_fixture('working','wrong','frozen'),True)
assert "['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul']"in src
assert "input=payload,check=True"in src
payload=''.join(n+'\0'for n in sorted(ns['paths'])).encode();assert payload.split(b'\0')[:-1]==[n.encode()for n in sorted(ns['paths'])]
assert 'assert changed()<=paths|extra and staged()<=paths|extra'in src
assert 'assert changed()<=paths and staged()<=paths'in src
assert 'assert staged() and staged()<=paths'in src
assert 'sha(PUB/n)==d'in src and "git','diff','--name-only','-z'"in src
assert "with safe(REPORT).open('x')"in src
assert not any(isinstance(n,ast.Call)and ast.unparse(n.func)=='subprocess.run'and any(x in ast.unparse(n)for x in ['commit','push'])for n in ast.walk(tree))
first_copy=src.index('shutil.copyfile(source,target)');assert src.index('assert changed()<=paths|extra')<first_copy
prior=ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-review-v4.json';priorbody=json.loads(prior.read_text());assert H(prior)=='8de426ecdee4fd3b9ce01554a9655028b47830f4ebaf6fd05559db374e0aef13'
for n,d in priorbody['closed_evidence_sha256'].items():assert H(ROOT/n)==d
obs={'status':'independent_publication24_stage_recovery_code_and_focused_readonly_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':H(HELPER),'helper':ref(HELPER),'checker':ref(Path(__file__)),'original_stage_v4_code_peer':ref(prior),'entire_original_stage_v4_peer_body_and_time':priorbody,'original_failed_stage_v4_execution':ref(ROOT/ns['FAILED']),'entire_original_failed_stage_v4_execution_and_time':original_failed,'original_native_whitelist':ref(ROOT/ns['OLD']),'actual_readonly_preflight':{'verified_publication_paths':len(ns['expected']),'frozen_bound_paths':len(ns['manifest']['frozen_inputs_sha256']),'actual_partial_index_paths':len(ns['staged']()),'31_source_assets_exact':True,'original_failure_exit':1},'fixture_count':len(cases),'fixtures':cases,'scope':'Author-independent full code read and actual read-only preflight of the exact 45,213 already-copied PUB files, followed by explicitly isolated synthetic assertion/parser/file fixtures. Original failed helper and actual exit1/time/log remain exact. Force-add is confined to the already audited whitelist plus safe canonical recovery closure and exclusive new native report. No recovery main, file copy, Git add/commit/push, Pages operation or coverage mutation was executed by this checker. Production must still run all guards again; the future recovery approval fixture was explicitly synthetic.'}
out=BASE/'publication24-stage-recovery-independent-observations-v5.json'
with out.open('x')as f:f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':obs['status'],'fixtures':len(cases),'verified_publication_files':len(ns['expected']),'observations':ref(out)}))
