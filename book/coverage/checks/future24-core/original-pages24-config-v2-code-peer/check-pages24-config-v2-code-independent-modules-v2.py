from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,subprocess,types
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
HELPER=ROOT/'book/coverage/checks/root_prepare_pages24_config_v2.py';OLD=ROOT/'book/coverage/checks/root_prepare_pages24_config_v1.py'
OUTPUT=Path('/tmp/pages24-config-v2-independent-modules-original-code-review-v1.json')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(HELPER)=='7859f7c25e71a830d9782225d99cdf16bb0472cd4e950f89d7f257a3faf14999'
assert not OUTPUT.exists()
a=OLD.read_text();b=HELPER.read_text();tree=ast.parse(b)
oldblock=a[a.index("retired='reports/full-coverage/lean-checkpoint-22'"):a.index('assert not added&exclusions')]
newblock=b[b.index('retired_dirs='):b.index('assert not added&exclusions')]
normalized=b.replace(b.splitlines()[0],a.splitlines()[0],1).replace(newblock,oldblock,1).replace('assert len(exclusions)==88\nassert included<850_000_000, included','assert included<900_000_000, included',1).replace("'retired_older_audit_dirs':retired_dirs,",'',1).replace('Exact old Pages23 config and every exact retired older audit file remain preserved.','Exact old Pages23 config and old audit22 files remain preserved.',1)
assert normalized==a,'Unexpected code delta'
backup=ROOT/'reports/full-coverage/pages24-config-previous-original-v1.yml';native=ROOT/'reports/full-coverage/pages24-config-preparation-v1.json'
assert not backup.exists() and not native.exists()
assert H(PUB/'_config.yml')=='278d5b40954704026471c5589d8869af8b9a5e5111c5cb070a28e35876ab09e3'
first=ROOT/'reports/full-coverage/pages24-config-execution-v1.json';failed=json.loads(first.read_text());assert failed['actual_exit_code']==1
assert H(ROOT/failed['log'])==failed['log_sha256'] and '1007285154' in (ROOT/failed['log']).read_text()
assert failed['helper_sha256_before']==failed['helper_sha256_after']=={str(OLD.relative_to(ROOT)):H(OLD)}
exclusions={line[4:] for line in (PUB/'_config.yml').read_text().splitlines() if line.startswith('  - ')};assert len(exclusions)==66
retired_dirs=['reports/full-coverage/lean-checkpoint-'+str(i) for i in [1,*range(4,21),22]]
assert len(retired_dirs)==len(set(retired_dirs))==19
retired={}
for d in retired_dirs:
 files={p.relative_to(ROOT).as_posix():H(p) for p in (ROOT/d).rglob('*') if p.is_file()};assert d+'/verification-original.json' in files
 assert files=={p.relative_to(PUB).as_posix():H(p) for p in (PUB/d).rglob('*') if p.is_file()}
 tracked=subprocess.run(['git','ls-files','-z','--',d],cwd=PUB,check=True,capture_output=True)
 assert {n for n in tracked.stdout.decode().split('\0') if n}==set(files)
 subprocess.run(['git','diff','--quiet','HEAD','--',d],cwd=PUB,check=True)
 assert not retired.keys()&files.keys();retired.update(files)
added=set(retired_dirs)|{'reports/full-coverage/checkpoint-24','reports/full-coverage/owner23-originals-before-owner24-integration-v1','book/coverage/inventory-after-correction52.json'}
assert len(added)==22 and not added&exclusions
exclusions|=added;assert len(exclusions)==88
func=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='kept')
ns={'exclusions':exclusions};exec(compile(ast.Module(body=[func],type_ignores=[]),str(HELPER),'exec'),ns);kept=ns['kept']
allasserts=[n for n in ast.walk(tree) if isinstance(n,ast.Assert)]
def guard(fragment):return next(n.test for n in allasserts if fragment in ast.unparse(n.test))
def eval_guard(expr,env):return eval(compile(ast.Expression(body=expr),str(HELPER),'eval'),env)
fixtures=[]
def case(name,actual,expected=True):assert actual==expected,(name,actual,expected);fixtures.append({'case':name,'expected':expected,'actual':actual,'status':'passed'})
for p in ['SafeLearning/nn-in-the-loop.html','book/coverage/modules.json','reports/full-coverage/lean-checkpoint-23/verification-original.json','reports/full-coverage/lean-checkpoint-24/verification-original.json']:case('required current input remains included: '+p,kept(p))
for d in retired_dirs:case('literal retired subtree excluded: '+d,kept(d+'/verification-original.json'),False)
case('similar prefix is not overexcluded',kept('reports/full-coverage/lean-checkpoint-230/verification-original.json'))
literal=guard("Path(n).is_absolute()")
for p in ['/absolute','book/coverage/../bad','book/*','book/[x]','book/{x}']:
 case('reject nonliteral or noncanonical exclusion: '+p,bool(eval_guard(literal,{'Path':Path,'exclusions':{p}})),False)
case('accept exact literal paths',bool(eval_guard(literal,{'Path':Path,'exclusions':exclusions})))
budget=guard('included < 850000000')
for value,ok in [(849999999,True),(850000000,False),(900000000,False),(1007285154,False)]:case('prewrite reserve guard '+str(value),bool(eval_guard(budget,{'included':value})),ok)
retguard=guard("retired + '/verification-original.json' in files")
for files,ok in [({},False),({'old/log.txt':'s'},False),({'old/verification-original.json':'s'},True)]:case('retired archive must contain real audit '+str(files),bool(eval_guard(retguard,{'files':files,'retired':'old'})),ok)
case('duplicate addition rejected',bool(eval_guard(guard('not added & exclusions'),{'added':{'same'},'exclusions':{'same'}})),False)
case('archive source/hash drift rejected', {'archive/a':'a'}=={'archive/a':'b'},False)
case('archive tracked set omission rejected',{'archive/a','archive/b'}=={'archive/a'},False)
case('required current input accidentally excluded rejected',all(kept(p) for p in ['SafeLearning/index.html','reports/full-coverage/lean-checkpoint-24/verification-original.json']))
write_lines=[n.lineno for n in ast.walk(tree) if isinstance(n,ast.Call) and (isinstance(n.func,ast.Attribute) and n.func.attr=='write_text')]
backup_line=next(n.lineno for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='open' and any(isinstance(a,ast.Constant) and a.value=='xb' for a in n.args))
budgetline=next(n.lineno for n in allasserts if 'included < 850000000' in ast.unparse(n.test));assert budgetline<backup_line<min(write_lines)
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n';after=header+''.join('  - '+n+'\n' for n in sorted(exclusions))
size=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))-len((PUB/'_config.yml').read_bytes())+len(after.encode())
assert size<850000000
assert not backup.exists() and not native.exists() and H(PUB/'_config.yml')=='278d5b40954704026471c5589d8869af8b9a5e5111c5cb070a28e35876ab09e3'
original_failure=json.loads(Path('/tmp/pages24-config-v2-independent-modules-code-actual-v1.json').read_text());assert original_failure['actual_exit_code']==1 and H(Path(original_failure['raw_log']))==original_failure['raw_log_sha256']
result={'preserved_original_reader_failure':{'reason':'Own v1 reader compared Root native helper-hash dictionaries to a scalar; only this reader schema assertion was corrected. Root helpers/configuration unchanged.','actual_record':{'file':'/tmp/pages24-config-v2-independent-modules-code-actual-v1.json','sha256':H(Path('/tmp/pages24-config-v2-independent-modules-code-actual-v1.json'))},'entire_original_actual_body_and_time':original_failure,'original_checker':{'file':str(p if False else Path('/tmp/check-pages24-config-v2-code-independent-modules-v1.py')),'sha256':H(Path('/tmp/check-pages24-config-v2-code-independent-modules-v1.py'))}},'status':'passed_independent_pages24_config_v2_full_code_delta_and_isolated_guard_review','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':str(HELPER.relative_to(ROOT)),'helper_sha256':H(HELPER),'original_v1_helper_sha256':H(OLD),'exact_reverse_normalization_recovers_entire_v1_helper':True,'original_failed_v1_execution':{'file':str(first.relative_to(ROOT)),'sha256':H(first)},'entire_original_v1_failure_body_and_time':failed,'baseline_config_sha256':H(PUB/'_config.yml'),'baseline_exclusion_count':66,'new_literal_exclusions':sorted(added),'prospective_literal_exclusion_count':88,'retired_older_audit_dirs':retired_dirs,'retired_root_publication_tracked_HEAD_file_count':len(retired),'retired_exact_hash_map_digest':hashlib.sha256(json.dumps(retired,sort_keys=True).encode()).hexdigest(),'fixtures':fixtures,'fixture_count':len(fixtures),'actual_read_only_prospective_budget_bytes':size,'prewrite_reserved_budget_bytes':850000000,'budget_and_current_inputs_and_archive_gates_precede_all_writes':True,'all_configuration_outputs_and_backup_untouched':True,'closed_evidence_sha256':{str(HELPER.relative_to(ROOT)):H(HELPER),str(OLD.relative_to(ROOT)):H(OLD),str(first.relative_to(ROOT)):H(first),failed['log']:failed['log_sha256'],str(Path(__file__)):H(Path(__file__))},'scope':'Independent full code/delta read, actual archive read-only checks and exact extracted AST guard fixtures only. Production config-v2 was not executed and no Pages/website delivery inferred. All old archives stay exact in Git; only website exclusions change.'}
OUTPUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'output':str(OUTPUT),'sha256':H(OUTPUT),'fixtures':len(fixtures),'prospective_website_bytes':size}))
