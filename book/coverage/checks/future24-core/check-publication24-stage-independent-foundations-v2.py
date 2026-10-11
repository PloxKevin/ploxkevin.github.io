"""Read-only staging-helper code fixtures; never execute its top-level module."""
from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/checks/root_stage_publication24_v1.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
src=HELPER.read_text();tree=ast.parse(src)
# Execute only the pure/read-only safe and actual record-validation functions.
ns={'ROOT':ROOT,'Path':Path,'sha':H,'hashlib':hashlib,'json':json}
functions=[n for n in tree.body if isinstance(n,ast.FunctionDef)]
exec(compile(ast.Module(body=functions,type_ignores=[]),str(HELPER),'exec'),ns)
cases=[]
def case(name,body,reject=False):
 try:body()
 except (AssertionError,KeyError,ValueError,TypeError):assert reject,name;cases.append({'fixture':name,'observed':'rejected'})
 else:assert not reject,name;cases.append({'fixture':name,'observed':'accepted'})
case('canonical_allowed_source_path',lambda:ns['safe']('SafeLearning/primer-basics.html'))
for name in ['/tmp/file','../outside','book/coverage/../../../../etc/passwd','bad\0path','bad\npath','bad\rpath']:
 case('reject_unsafe_path_'+repr(name),lambda name=name:ns['safe'](name),True)
records={};ns['read']=lambda n:records[n]
real_log=ROOT/'book/coverage/checks/future24-core/pages24-config-helper-independent-foundations-actual-v1.log';record={'actual_exit_code':0,'exit_code':0,'log':str(real_log.relative_to(ROOT)),'log_sha256':H(real_log)}
def actual_fixture(edit,exit_code=0):
 r=dict(record);edit(r);records['fixture']=r;return ns['actual']('fixture',exit_code)
case('matching_real_hash_native_zero_aliases',lambda:actual_fixture(lambda r:None))
case('historical_failure_accepted_only_as_failure',lambda:actual_fixture(lambda r:r.update(actual_exit_code=1,exit_code=1),1))
case('failed_record_rejected_from_success_stems',lambda:actual_fixture(lambda r:r.update(actual_exit_code=1,exit_code=1)),True)
case('conflicting_exit_alias_rejected',lambda:actual_fixture(lambda r:r.update(exit_code=1)),True)
case('boolean_exit_rejected',lambda:actual_fixture(lambda r:r.update(actual_exit_code=False)),True)
case('wrong_log_hash_rejected',lambda:actual_fixture(lambda r:r.update(log_sha256='0'*64)),True)
case('missing_exit_codes_rejected',lambda:actual_fixture(lambda r:(r.pop('actual_exit_code'),r.pop('exit_code'))),True)
# Exercise the exact staged path status rules and NUL argument construction.
def parse(entries,allowed):
 changed=set()
 for entry in entries:
  assert entry[:2]not in {'R ',' R','C ',' C'}and 'D'not in entry[:2]
  changed.add(entry[3:])
 assert changed<=allowed
 return changed
allowed={'SafeLearning/primer-basics.html','reports/full-coverage/some report.json'}
case('strict_whitelisted_tracked_and_untracked_status',lambda:parse([' M SafeLearning/primer-basics.html','?? reports/full-coverage/some report.json'],allowed))
case('out_of_whitelist_dirty_path_rejected',lambda:parse(['?? outside'],allowed),True)
case('deleted_path_rejected',lambda:parse([' D SafeLearning/primer-basics.html'],allowed),True)
case('renamed_path_rejected',lambda:parse(['R  SafeLearning/primer-basics.html'],allowed),True)
payload=''.join(n+'\0'for n in sorted(allowed)).encode();assert payload.split(b'\0')[:-1]==[n.encode()for n in sorted(allowed)]
assert "['git','add','--pathspec-from-file=-','--pathspec-file-nul']"in src
assert "input=payload"in src and "check=True"in src
assert "assert {n for n in staged if n}<=paths"in src
first_copy=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.For)and ast.unparse(n.target)=='n'and 'shutil.copyfile'in ast.unparse(n))
assert all('1144'in src and n in src for n in ['9279','38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'])
for text in ["audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}","manifest['successful_verification']['report_sha256']","selection['coverage_complete'] is False","config['excluded_count']==70","config['prospective_included_website_bytes']<900_000_000","assert len(assets)==31","sha(safe(n))==sha(PUB/n)==d","'awaits an actual GitHub Pages build'","'checkpoint24_awaiting_actual_pages_and_live_checks'","set(manifest['frozen_inputs_sha256'])<=paths"]:assert text in src,text
for text in ['source52-dry-execution-v1','source52-corrected-paragraphs24-capture-execution-v1','actual(record,1)','source52-dry-execution-v2','source52-apply-execution-v1','verify-checkpoint24-execution-v1','export-checkpoint24-execution-v1','export-checkpoint24-output-integrity-execution-v1','pages24-config-execution-v1','browser-checkpoint24-binding-execution-v1','stage_peer[\'helper_sha256\']==sha(Path(__file__))','config_peer[\'config_sha256\']==config[\'config_sha256\']','closed_evidence_sha256']:assert text in src,text
assert not any(isinstance(n,ast.Call)and ast.unparse(n.func)=='subprocess.run'and any(x in ast.unparse(n)for x in ['commit','push'])for n in ast.walk(tree))
for i,n in enumerate(tree.body[:first_copy]):
 assert not ('shutil.copyfile'in ast.unparse(n)or '.open(\'x\')'in ast.unparse(n))
assert not (ROOT/'reports/full-coverage/publication24-prestage-v1.json').exists()
obs={'status':'independent_publication24_stage_helper_code_and_focused_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','helper':ref(HELPER),'helper_sha256':H(HELPER),'checker':ref(Path(__file__)),'fixture_count':len(cases),'fixtures':cases,'full_read_scope':['future actual1144-source9279-export kernel/standard-axiom report byte bindings','exact frozen/prepared whitelist and snapshot bytes with only explicit mutable progress','actual31current source52 HTML assets and frozen publication owner validation','truthful awaiting-Pages progress/README guard','success and genuine failure execution stems retain native exits and rawlogs','explicit closed peer/evidence catalogs with exact code/config identity','no broad stage; strict dirty subset and NUL Git add; no commit/push','exclusive new report, original immutable inputs and future25 active-proof exclusion'],'scope':'Code-only author-independent approval. Only isolated read-only functions and explicitly synthetic dictionary/status fixtures were executed. No future audit/config/preparation/output was assumed present or approved; production assertions remain required at actual staging. No preparer/main, PUB copy, Git add/commit/push, live source, owner, inventory or selected-proof mutation occurred.'}
out=ROOT/'book/coverage/checks/future24-core/publication24-stage-independent-observations-v2.json'
with out.open('x')as f:f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':obs['status'],'observations':ref(out),'fixture_count':len(cases)}))
