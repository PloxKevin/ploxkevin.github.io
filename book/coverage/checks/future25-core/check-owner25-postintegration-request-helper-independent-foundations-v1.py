"""Read-only request-preparer prefix fixtures, no alias/report/request writes."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,runpy
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future25-core'
HELPER=ROOT/'book/coverage/checks/prepare_root_owner25_interfaces_request_v1.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(HELPER)=='a37cdb4c83402745377d81f2bae2c0dc4c534c4b413a741b802d12b8eb000373'
tree=ast.parse(HELPER.read_text())
stop=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.Assign)and ast.unparse(n.targets[0])=='alias_dir')
# Execute only the prefix ending before mkdir/open/x writes. All execution,
# installation and global records here are explicitly synthetic in-memory data.
defs=[n for n in tree.body[:stop]if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))or isinstance(n,ast.Assign)and ast.unparse(n.targets[0])in {'ROOT','BASE','DEST','BINDING'}]
gates=[n for n in tree.body[:stop]if n not in defs]
f=runpy.run_path(str(BASE/'owner25-live-interface-in-memory-fixture-support-v2.py'),run_name='explicit_synthetic_memory_fixture')
base=dict(f['store']);store={};cases=[]
BIND='book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json'
EXE='reports/full-coverage/owner25-integration-apply-execution-v1.json'
RESULT='reports/full-coverage/owner25-reviewed-candidate-integration-v1.json'
GLOBAL='reports/full-coverage/root-source52-final-owner-integration25-v1.json'
SYNLOG='reports/full-coverage/explicit-synthetic-no-execution.log'
def put(n,d):store[n]=(json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode()
def read(n):return json.loads(store[n])if n in store else json.loads((ROOT/n).read_text())
def sha(n):return hashlib.sha256(store[n]).hexdigest()if n in store else H(ROOT/n)
def reset():
 store.clear();store.update(base)
 binding=json.loads((ROOT/BIND).read_text());put(BIND,binding)
 result=copy.deepcopy(f['result']);result['binding_manifest']=BIND;result['binding_manifest_sha256']=sha(BIND)
 for row in result['exact_replacements']:
  target='reports/full-coverage/owner24-originals-before-owner25-integration-v1/'+Path(row['destination']).name
  store[target]=store[row['original24_byte_copy']];row['original24_byte_copy']=target
 put(RESULT,result)
 store[SYNLOG]=b'explicit synthetic fixture, no Root execution\n'
 put(EXE,{'actual_exit_code':0,'actual_command':['python3','book/coverage/checks/root_integrate_owner25_candidates_v3.py',BIND,'--apply'],'log':SYNLOG,'log_sha256':sha(SYNLOG)})
 put(GLOBAL,{'integrity_status':'passed','errors':[]})
def run(label,edit=lambda:None,reject=False):
 reset();edit()
 ns={'__name__':'independent_explicit_synthetic_request_gate_fixture','__file__':str(HELPER)}
 exec(compile(ast.Module(body=defs,type_ignores=[]),str(HELPER),'exec'),ns)
 ns.update(sha=sha,read=read,ref=lambda n:{'file':n,'sha256':sha(n)})
 try:exec(compile(ast.Module(body=gates,type_ignores=[]),str(HELPER),'exec'),ns)
 except(AssertionError,KeyError,ValueError,TypeError):
  assert reject,label;observed='rejected'
 else:
  assert not reject,label;observed='accepted'
 cases.append({'fixture':label,'observed':observed})
def mutate(n,edit):d=read(n);edit(d);put(n,d)
run('synthetic_complete_guard_prefix_accepts_real_four_owner_provenance_and_five_archives')
for label,n,edit in [
 ('boolean_exit',EXE,lambda d:d.update(actual_exit_code=False)),
 ('failed_exit',EXE,lambda d:d.update(actual_exit_code=1)),
 ('wrong_command',EXE,lambda d:d['actual_command'].__setitem__(3,'--dry-run')),
 ('wrong_raw_log',EXE,lambda d:d.update(log_sha256='0'*64)),
 ('unapplied',RESULT,lambda d:d.update(applied=False)),
 ('wrong_binding',RESULT,lambda d:d.update(binding_manifest_sha256='0'*64)),
 ('wrong_count',RESULT,lambda d:d['exact_replacements'].pop()),
 ('wrong_archive_prefix',RESULT,lambda d:d['exact_replacements'][0].update(original24_byte_copy='wrong.json')),
 ('wrong_old_hash',RESULT,lambda d:d['exact_replacements'][0].update(before_sha256='0'*64)),
 ('wrong_installed_hash',RESULT,lambda d:d['exact_replacements'][0]['candidate'].update(sha256='0'*64)),
 ('failed_global',GLOBAL,lambda d:d.update(integrity_status='failed')),
 ('global_errors',GLOBAL,lambda d:d.update(errors=['synthetic error'])),
 ('wrong_new_source_count',BIND,lambda d:d.update(new_proof_sources=13)),
 ('stale_owner_provenance',BIND,lambda d:d['owners']['core']['additional_exact_provenance'][0].update(sha256='0'*64)),
]:run('reject_'+label,lambda n=n,edit=edit:mutate(n,edit),True)
# Full code was read. Prefix guards precede every write. Outputs are exclusive
# new original-byte aliases/catalog/request and never owner or source targets.
write_nodes=[n for n in ast.walk(tree)if isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and n.func.attr in {'open','mkdir','write_text','write_bytes'}]
assert len(write_nodes)==4
assert all(isinstance(n,ast.Call)for n in write_nodes)
text=HELPER.read_text()
assert "target.open('xb')"in text and "(ROOT / alias_name).open('x')"in text and "(ROOT / DEST).open('x')"in text
assert "path.suffix in {'.json', '.log', '.py', '.lean', '.txt', '.cjs', '.md'}"in text
assert "'__pycache__' not in path.parts"in text
assert "assert not (ROOT / name).exists()"in text
assert "sha(name) == row['sha256']"in text
assert not any(isinstance(n,ast.Import)and any(x.name in {'subprocess','os'}for x in n.names)for n in tree.body)
report={'status':'independent_owner25_postintegration_request_helper_full_code_and_isolated_prefix_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; helper author Root','helper_sha256':H(HELPER),'helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':H(HELPER)},'fixtures':cases,'fixture_count':len(cases),'write_scope':'The actual helper writes only new content-addressed original-report aliases, their unique catalog and the unique postintegration request. All guard prefix tests finish before mkdir/open and retain real original owner and compiler evidence bytes. No production helper main was executed.','closed_before_synthetic_execution':'No synthetic records were written. Synthetic candidate installed hashes, apply/global records and archives exist only in memory, explicitly code tests; no Root installation or global/compile/audit claim.','scope':'Code review only; the actual request still requires genuine Root apply/global and the downstream interface validates exact command/helper/cwd/log/status/schema again. Fresh actual interface output peer remains required.'}
name='owner25-postintegration-request-helper-independent-foundations-observations-v1.json';out=BASE/name;assert not out.exists();out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'fixture_count':len(cases),'observation':str(out.relative_to(ROOT)),'sha256':H(out)}))
