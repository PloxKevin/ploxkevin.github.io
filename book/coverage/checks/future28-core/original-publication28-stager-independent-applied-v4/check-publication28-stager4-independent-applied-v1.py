"""Full-code/native guard fixtures in a wholly synthetic TMP publication tree."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, importlib.util, json, shutil, subprocess, tempfile

REAL = Path('/home/oxrexkevin/SafetyBased')
HELPER = REAL/'book/coverage/checks/root_stage_publication28_v4.py'
EXPECTED_HELPER = '885a96476b8bd66e1b473a54a2e2993781d53708df61770c0db6a78d1ff16541'
assert hashlib.sha256(HELPER.read_bytes()).hexdigest() == EXPECTED_HELPER
compile(HELPER.read_text(), str(HELPER), 'exec')
spec = importlib.util.spec_from_file_location('independent_stager28v4', HELPER)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
TEMP = Path(tempfile.mkdtemp(prefix='applied-stager28v4-fixtures-'))
m.ROOT = TEMP; m.PUB = TEMP/'reports/book/publication-repo'; m.PUB.mkdir(parents=True)
PUB = m.PUB
def dump(n, d, pub=False):
    p = (PUB if pub else TEMP)/n; p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(d, separators=(',', ':'))+'\n')
    return {'file': n, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
def put(n, b, pub=False):
    p=(PUB if pub else TEMP)/n;p.parent.mkdir(parents=True, exist_ok=True);p.write_bytes(b)
def digest(n, pub=False):
    return hashlib.sha256(((PUB if pub else TEMP)/n).read_bytes()).hexdigest()
proofs = {'verification/lean/SafeLearning/Synthetic%d.lean'%i: {'sha256': hashlib.sha256(b'-- synthetic source\n').hexdigest()} for i in range(1186)}
for n in proofs: put(n,b'-- synthetic source\n');put(n,b'-- synthetic source\n',True)
assets = {'SafeLearning/asset%d.html'%i:hashlib.sha256(b'fixture asset\n').hexdigest() for i in range(31)}
for n in assets:put(n,b'fixture asset\n');put(n,b'fixture asset\n',True)
frozen = {n:r['sha256'] for n,r in proofs.items()};frozen.update(assets)
for domain in ['core','foundations','applied','modules','applied-promotions']:
    n='book/coverage/'+domain+'.json';put(n,b'{}\n');put(n,b'{}\n',True);frozen[n]=digest(n)
put('book/coverage/inventory.json',b'{}\n');put('book/coverage/inventory.json',b'{}\n',True);frozen['book/coverage/inventory.json']=digest('book/coverage/inventory.json')
progress={'publication_status':'prepared_source_exact_checkpoint_28_awaiting_delivery','verified_checkpoint':{'coverage_complete':False},'working_next_checkpoint_preparation':{'exercise_counts':{'complete':523,'partial':14,'pending':19},'material_review_units':{'reviewed':4621,'pending':8153}}}
dump('book/coverage/progress.json',progress);dump('book/coverage/progress.json',progress,True)
put('reports/full-coverage/README.md',b'fixture pending delivery\n');put('reports/full-coverage/README.md',b'fixture pending delivery\n',True)
frozen['book/coverage/progress.json']=digest('book/coverage/progress.json');frozen['reports/full-coverage/README.md']=digest('reports/full-coverage/README.md')
baseline_name='reports/full-coverage/checkpoint-27-selection.json'
dump(baseline_name,{'proof_files':dict(list(proofs.items())[:1175])})
# The sole digest adapter represents the literal old baseline pin in this
# synthetic workspace; no real checkpoint bytes/native outputs are fabricated.
original_sha=m.sha
def sha(root,n):
    if root==TEMP and n==baseline_name:return 'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
    return original_sha(root,n)
m.sha=sha
added=list(proofs)[1175:]
audit={'status':'passed','proof_file_count':1186,'theorem_count':9896,'proof_sha256':{n:r['sha256'] for n,r in proofs.items()},'declarations':[{'name':'Synthetic.theorem%d'%i,'file':added[i%11] if i<252 else list(proofs)[i%1175]} for i in range(9896)],'axiom_dependencies':{'Synthetic.theorem%d'%i:[] for i in range(9896)},'allowed_standard_axioms':['propext','Classical.choice','Quot.sound'],'checks':[{'exit_code':0,'command':['synthetic','only'],'actual_workdir':str(TEMP),'status':'passed','evidence_mode':'fresh_kernel_replay' if i<11 else 'reused_identical_module_and_transitive_local_imports'} for i in range(1186)]}
selection={'proof_files':proofs,'proof_file_count':1186,'new_file_count':11}
audit_ref=dump('fixture/audit.json',audit)
manifest={'status':'formal_verification_passed_partial_coverage','coverage_complete':False,'proof_files':proofs,'successful_verification':{'report_sha256':audit_ref['sha256']},'frozen_inputs_sha256':frozen,'working_inputs_sha256':frozen}
publedger={'integrity_status':'passed','errors':[],'mathematical_coverage_complete':False,'inventory_sha256':frozen['book/coverage/inventory.json'],'domains':[{'domain':n,'ledger_sha256':frozen['book/coverage/'+n+'.json']} for n in ['core','foundations','applied','modules']]}
exclusions=['excluded/%03d'%i for i in range(153)]
put('_config.yml',('exclude:\n'+''.join('  - '+n+'\n' for n in exclusions)).encode(),True)
config={'status':'passed_exact_pages28_archival_configuration_requires_actual_pages_and_live_checks','website_budget_bytes':850000000,'excluded_count':153,'exclusions':exclusions,'included_website_bytes_including_configuration_evidence':0,'config_sha256':digest('_config.yml',True),'required_publication_files_sha256':{}}
prerequisite_commands={
'verify-checkpoint28-execution-v1':['python3','reports/full-coverage/checkpoint-28/verification/lean/verify.py','--reuse-kernel-from',str(TEMP/'reports/full-coverage/checkpoint-27')],
'export-checkpoint28-execution-v1':['python3','book/coverage/export_audit28_v1.py','--snapshot','reports/full-coverage/checkpoint-28','--output','reports/full-coverage/lean-checkpoint-28'],
'export-integrity28-execution-v1':['python3','book/coverage/checks/root_check_export28_integrity_v1.py'],
'static-checkpoint28-execution-v1':['python3','book/validate28_v1.py','--allow-reviewed-corrections','--output','reports/full-coverage/integration-28.json'],
'frozen-ledger-checkpoint28-execution-v1':['python3','reports/full-coverage/checkpoint-28/book/coverage/validate.py','--output','reports/full-coverage/lean-checkpoint-28/ledger-audit.json'],
'prepare-publication28-execution-v1':['python3','book/coverage/prepare_publication.py','28'],
'publication28-ledger-check-execution-v1':['python3','reports/book/publication-repo/book/coverage/validate.py','--output','reports/full-coverage/publication-checks/ledger-checkpoint-28.json'],
'pages28-config-application-execution-v1':['python3','book/coverage/checks/root_prepare_pages28_config_v3.py','--apply'],
'prepare-documents28-execution-v1':['python3','book/coverage/checks/root_prepare_checkpoint28_documents_v2.py']}
records={}
for key,cmd in prerequisite_commands.items():
    if not (TEMP/cmd[1]).exists():put(cmd[1],b'# synthetic designated helper\n')
    log='reports/full-coverage/'+key+'.log';put(log,b'synthetic actual-record fixture\n')
    records[key]={'status':'passed','actual_exit_code':0,'actual_command':cmd,'actual_workdir':str(TEMP),'log':log,'log_sha256':digest(log),'helper_sha256_before':{cmd[1]:digest(cmd[1])},'helper_sha256_after':{cmd[1]:digest(cmd[1])}}
prepared=list(frozen)
extra={'book/coverage/progress.json':digest('book/coverage/progress.json'),'reports/full-coverage/README.md':digest('reports/full-coverage/README.md')}
plan={'status':'explicit_actual_audited_checkpoint28_publication_plan','baseline_publication_head':m.HEAD,'manifest':dump('fixture/manifest.json',manifest),'selection':dump('fixture/selection.json',selection),'original_audit':audit_ref,'prepared_file_list':dump('fixture/prepared.json',prepared),'supplementary_paths_sha256':extra,'publication_ledger':dump('fixture/publedger.json',publedger),'configuration_preparation':dump('fixture/config.json',config),'actual_prerequisites':{key:dump('reports/full-coverage/'+key+'.json',r) for key,r in records.items()}}
PLAN='fixture/plan.json'
def publish_plan():
    r=dump(PLAN,plan);dump(PLAN,plan,True);return r['sha256']
def git(args,data=None,check=True):
    assert args in [['rev-parse','HEAD'],['diff','--cached','--name-only','-z'],['status','--porcelain','-z','--untracked-files=all']], ('unexpected Git action in prepare fixture',args)
    return subprocess.CompletedProcess(args,0,(m.HEAD+'\n').encode() if args==['rev-parse','HEAD'] else b'',b'')
m.git=git
cases=[]
def accepted(label,fn):
    fn();cases.append({'case':label,'result':'accepted'})
def rejected(label,fn):
    try:fn()
    except (AssertionError,KeyError,ValueError):cases.append({'case':label,'result':'rejected'});return
    raise AssertionError('defective acceptance: '+label)
accepted('complete synthetic 1186/9896/11+1175 native contract',lambda:m.prepare(PLAN,publish_plan()))
for key in records:
    saved=copy.deepcopy(records[key])
    for field,value in [('actual_exit_code',False),('actual_command',['python3','wrong-helper.py']),('actual_workdir','/wrong/cwd'),('status','pending'),('helper_sha256_after',{})]:
        changed=copy.deepcopy(saved);changed[field]=value
        plan['actual_prerequisites'][key]=dump('reports/full-coverage/'+key+'.json',changed)
        rejected(key+' rejects '+field,lambda:m.prepare(PLAN,publish_plan()))
    plan['actual_prerequisites'][key]=dump('reports/full-coverage/'+key+'.json',saved)
for field,value in [('status','passed'),('website_budget_bytes',850000001),('exclusions',list(reversed(exclusions))),('excluded_count',152)]:
    changed=copy.deepcopy(config);changed[field]=value;plan['configuration_preparation']=dump('fixture/config.json',changed)
    rejected('config rejects '+field,lambda:m.prepare(PLAN,publish_plan()))
plan['configuration_preparation']=dump('fixture/config.json',config)
saved_selection=copy.deepcopy(selection)
selection['proof_files']=dict(list(proofs.items())[:-1]);plan['selection']=dump('fixture/selection.json',selection)
rejected('physical proof map omission',lambda:m.prepare(PLAN,publish_plan()))
selection=saved_selection;selection['new_file_count']=10;plan['selection']=dump('fixture/selection.json',selection)
rejected('wrong fresh source count',lambda:m.prepare(PLAN,publish_plan()))
selection['new_file_count']=11;plan['selection']=dump('fixture/selection.json',selection)
for n in ['/absolute','../escape','a//b','a\nb','x*','x?','x[1]']:
    rejected('unsafe path '+repr(n),lambda n=n:m.safe(TEMP,n))
target=TEMP/'symlink-target';target.write_text('x');(PUB/'included-symlink').symlink_to(target)
rejected('included file symlink',m.website_size);(PUB/'included-symlink').unlink()
(PUB/'included-dir-symlink').symlink_to(TEMP/'fixture',target_is_directory=True)
rejected('included directory symlink',m.website_size);(PUB/'included-dir-symlink').unlink()
(PUB/exclusions[0]).parent.mkdir(parents=True,exist_ok=True);(PUB/exclusions[0]).symlink_to(TEMP/'fixture',target_is_directory=True)
accepted('explicitly excluded directory symlink contributes no website bytes',m.website_size);(PUB/exclusions[0]).unlink()
large=PUB/'included-budget-fixture';
with large.open('wb') as f:f.truncate(850000000)
rejected('fresh current website overflow despite stale zero config budget',lambda:m.prepare(PLAN,publish_plan()));large.unlink()
# Git regression is executed only in an unrelated temporary repository.
repo=TEMP/'isolated-git';repo.mkdir();subprocess.run(['git','init','-q'],cwd=repo,check=True)
(repo/'.gitignore').write_text('*.log\n');(repo/'exact.log').write_text('literal archived evidence\n')
raw=b'exact.log\0'
p=subprocess.run(['git','add','--pathspec-from-file=-','--pathspec-file-nul'],cwd=repo,input=raw,capture_output=True)
assert p.returncode != 0;cases.append({'case':'old unforced ignored-log add genuinely fails in isolated Git','result':'rejected'})
subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=repo,input=raw,capture_output=True,check=True)
assert subprocess.run(['git','show',':exact.log'],cwd=repo,capture_output=True,check=True).stdout==(repo/'exact.log').read_bytes();cases.append({'case':'forced explicit NUL whitelist stages exact ignored log in isolated Git','result':'accepted'})
report={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(HELPER.relative_to(REAL)),'sha256':EXPECTED_HELPER},'fixture_count':len(cases),'fixtures':cases,'synthetic_adapter':'Only pinned old-baseline digest uses a labelled adapter. All nine future native records and both prepared trees are entirely synthetic; no actual prerequisite/PUB preparation is claimed.','actual_prepare_function_exercised':True,'actual_website_size_function_exercised':True,'isolated_temporary_git_only':True,'production_invocation':False,'scope':'Full helper read plus meaningful negative native/physical-count/path/symlink/budget/ignored-log fixtures. No actual audit28 or producer/PUB staging.'}
OUT=Path('/tmp/publication28-stager4-independent-applied-fixture-findings-v1.json');assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':'passed','fixtures':len(cases),'findings':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest()}))
