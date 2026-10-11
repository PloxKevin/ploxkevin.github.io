"""Independent code fixtures only: all future delivery inputs are explicitly synthetic.

Runs the reviewed AST bodies only in disposable temporary directories. subprocess.run
is replaced by a recording fake; no Git, Pages, Lean, or production helper executes.
"""
from pathlib import Path
from datetime import datetime, timezone
import ast, contextlib, copy, hashlib, io, json, shutil, subprocess, tempfile

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).parent
UP = 'book/coverage/checks/root_update_publication24_delivery_progress_v1.py'
ST = 'book/coverage/checks/root_stage_publication24_delivery_metadata_v3.py'
OLD2 = 'book/coverage/checks/root_stage_publication24_delivery_metadata_v2.py'
ORIGINAL_PEER = 'book/coverage/checks/future24-core/publication24-delivery-metadata-helpers-independent-foundations-review-v1.json'
OLD = 'book/coverage/checks/root_stage_publication24_delivery_metadata_v1.py'
PINS = {UP:'a1bf7711dbe29157b7ea187e17a05d9d3ea6d79483a69dcc7d2ff6c130a3718c',
        ST:'b319489a2d51993ecae05835a4fcc727fd69be1b7accac08878e41fdedfc81cd',
        OLD2:'4591398d5b8cdfad224d0992781b4c78fdea5e03f886ca1ce55c8bbfb4b23a80',
        OLD:'ec12c713f19127882f2e070d0eb5a8ab13c5a185544b8dda6266993b9192ec81'}
INV = '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
COMMIT = 'd'*40
RUN_ID = 4700123456789
PEER = 'book/coverage/checks/future24-core/publication24-delivery-metadata-helpers-independent-foundations-review-v2.json'
OBS = HERE/'publication24-delivery-metadata-independent-foundations-observations-v3.json'
assert not OBS.exists()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def put(p, v):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(v, indent=2)+'\n')
def raw(p, v):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(v)
for n,d in PINS.items(): assert sha(ROOT/n)==d
assert sha(ROOT/'book/coverage/inventory.json')==INV
uptext=(ROOT/UP).read_text(); sttext=(ROOT/ST).read_text(); oldtext=(ROOT/OLD).read_text()
assert sha(ROOT/ORIGINAL_PEER)=='fa4bcc5ca39375a0b25692fb038c64f9ce99add9f8a4109031cf067e6f9a275c'
original_peer_body=load(ROOT/ORIGINAL_PEER)
for n,d in original_peer_body['closed_evidence_sha256'].items(): assert sha(ROOT/n)==d
reverse=sttext.replace("SELF,'book/coverage/checks/root_stage_publication24_delivery_metadata_v1.py','book/coverage/checks/root_stage_publication24_delivery_metadata_v2.py',", "SELF,'book/coverage/checks/root_stage_publication24_delivery_metadata_v1.py',")
reverse=reverse.replace("for stem in ['stage-publication24-execution-v2',", "for stem in ['stage-publication24-execution-v1',")
reverse=reverse.replace("peer_name='book/coverage/checks/future24-core/publication24-delivery-metadata-helpers-independent-foundations-review-v2.json'", "peer_name='book/coverage/checks/future24-core/publication24-delivery-metadata-helpers-independent-foundations-review-v1.json'")
a=reverse.index("failed_stem='stage-publication24-execution-v1'");b=reverse.index("assert all(not n.startswith('verification/lean/')",a)
reverse=reverse[:a]+reverse[b:]
assert reverse==(ROOT/OLD2).read_text()
doc=(ROOT/'book/coverage/checks/root_prepare_checkpoint24_documentation_v2.py').read_text()
oldparagraph=('Checkpoint 24 has passed its local audit and awaits an actual GitHub Pages build\n'
              'and live asset checks. Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)\n')
assert oldparagraph in doc
trees={UP:ast.parse(uptext), ST:ast.parse(sttext)}
compiled={}
for n,t in trees.items():
    k=next(i for i,x in enumerate(t.body) if isinstance(x,ast.Assign) and any(isinstance(a,ast.Name) and a.id=='out' for a in x.targets))
    compiled[n]=(compile(ast.Module(t.body[:k],type_ignores=[]),n,'exec'),compile(ast.Module(t.body[k:],type_ignores=[]),n,'exec'))

class FakeSubprocess:
    """Only recognizes the five explicit Git reads/stage command; never executes."""
    def __init__(self, dirty=()): self.dirty=set(dirty); self.staged=set(); self.calls=[]
    def run(self, command, **kw):
        self.calls.append({'command':command,'cwd':str(kw.get('cwd'))})
        assert command[0]=='git'
        if command==['git','rev-parse','HEAD']: out=(COMMIT+'\n').encode()
        elif command==['git','diff','--name-only','-z']: out=b'\0'.join(n.encode() for n in sorted(self.dirty))
        elif command==['git','diff','--cached','--name-only','-z']: out=b'\0'.join(n.encode() for n in sorted(self.staged))
        elif command==['git','ls-files','--others','--exclude-standard','-z']: out=b''
        elif command==['git','add','--pathspec-from-file=-','--pathspec-file-nul']:
            payload=kw['input']; assert isinstance(payload,bytes) and payload.endswith(b'\0')
            self.staged={s.decode() for s in payload.split(b'\0') if s};out=b''
        else: raise AssertionError(('unexpected subprocess request',command))
        return subprocess.CompletedProcess(command,0,stdout=out,stderr=b'')

def record(r, stem):
    p=r/'reports/full-coverage'/f'{stem}.json'; log=p.with_suffix('.log')
    if stem=='publication24-pages-view-execution-v1':
        put(log,{'headSha':COMMIT,'status':'completed','conclusion':'success','jobs':[{'conclusion':'success'}]})
        command=['gh','run','view',str(RUN_ID),'--json','headSha,status,conclusion,jobs']
    else: raw(log,'explicit synthetic fixture output\n');command=['fixture',stem]
    put(p,{'actual_exit_code':0,'actual_command':command,'log':log.relative_to(r).as_posix(),'log_sha256':sha(log),
           'fixture_only':True,'no_actual_production_execution':True})
    if stem=='stage-publication24-execution-v1':
        d=load(p);d['actual_exit_code']=1;put(p,d)

def setup(r):
    for n in PINS: raw(r/n,(ROOT/n).read_text())
    shutil.copyfile(ROOT/ORIGINAL_PEER, r/ORIGINAL_PEER)
    for n in original_peer_body['closed_evidence_sha256']:
        target=r/n;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/n,target)
    # The real unchanged inventory is read only through a temporary symlink, never written.
    inv=r/'book/coverage/inventory.json';inv.parent.mkdir(parents=True,exist_ok=True);inv.symlink_to(ROOT/'book/coverage/inventory.json')
    put(r/'book/coverage/material-corrections.json',{'corrections':[{'fixture':i} for i in range(52)]})
    progress={'verified_checkpoint':{'proof_files':1144,'theorems':9279,'coverage_complete':False},
              'publication_status':'checkpoint24_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks',
              'last_published_content_commit':'e384ffa82cea432f274dd83abbe498f988c756e4',
              'last_published_commit':'e384ffa82cea432f274dd83abbe498f988c756e4',
              'working_next_checkpoint_preparation':{'status':'pending','coverage_complete':False},
              'immutable_fixture_marker':{'nested':[1,2,3]}}
    put(r/'book/coverage/progress.json',progress)
    raw(r/'reports/full-coverage/README.md','unchanged opening\n'+oldparagraph+'unchanged closing\n')
    put(r/'reports/full-coverage/live-checkpoint-24-attempt1.json',{'status':'passed_all31_asset_sha256','assets':[{'fixture':i} for i in range(31)],'commit':COMMIT,'remote_main':COMMIT})
    put(r/'reports/full-coverage/pages-checkpoint-24-attempt1.json',{'status':'passed','commit':COMMIT,'expected_commit':COMMIT})
    raw(r/'reports/full-coverage/pages-checkpoint-24-attempt1.log','explicit synthetic Pages verification fixture\n')
    for stem in ['stage-publication24-execution-v2','stage-publication24-execution-v1','publication24-delivery-progress-update-execution-v1',
                 'publication24-content-commit-execution-v1','publication24-content-push-execution-v1',
                 'publication24-pages-watch-execution-v1','publication24-pages-view-execution-v1',
                 'publication24-pages-artifact-execution-v1','live24-attempt1-execution-v1']: record(r,stem)
    audit={'status':'passed','proof_file_count':1144,'theorem_count':9279,'checks':[{'exit_code':0}], 'fixture_only':True}
    put(r/'reports/full-coverage/lean-checkpoint-24/verification-original.json',audit)
    assets={}
    for i in range(31):
        n=f'SafeLearning/fixture-asset-{i:02}.html';raw(r/n,f'fixture asset {i}');raw(r/'reports/book/publication-repo'/n,f'fixture asset {i}');assets[n]=sha(r/n)
    put(r/'reports/full-coverage/checkpoint-24-manifest.json',{'status':'formal_verification_passed_partial_coverage',
        'proof_files':{str(i):{'fixture':True} for i in range(1144)},'frozen_inputs_sha256':assets,
        'successful_verification':{'report_sha256':sha(r/'reports/full-coverage/lean-checkpoint-24/verification-original.json')},'fixture_only':True})
    put(r/'reports/full-coverage/frozen-ledger-checkpoint24-v1.json',{'integrity_status':'passed','errors':[],
        'mathematical_coverage_complete':False,'counts':{'statuses':{'exercise:complete_math':514,'exercise:partial':19,'exercise:pending':23},
        'material_review_statuses':{'reviewed':4478,'pending':8296}},'fixture_only':True})
    put(r/'reports/full-coverage/publication24-prestage-v2.json',{'fixture_only':True,'status':'synthetic_native_path_fixture'})
    raw(r/'book/coverage/checks/future24-core/fixture-closed-evidence.txt','isolated fixture provenance only\n')
    ev='book/coverage/checks/future24-core/fixture-closed-evidence.txt'
    put(r/PEER,{'status':'independent_fixture_passed','errors':[],
        'helpers_sha256':{n:sha(r/n) for n in [ST,UP]},'closed_evidence_sha256':{ev:sha(r/ev)},'fixture_only':True})

def execute(r,n,fake):
    ns={'__file__':str(r/n),'__name__':'isolated_code_fixture'}
    exec(compiled[n][0],ns)
    assert ns['ROOT']==r
    ns['subprocess']=fake
    with contextlib.redirect_stdout(io.StringIO()): exec(compiled[n][1],ns)
    return ns

results=[]
def mutate_json(r,n, fn):
    p=r/n;v=load(p);fn(v);put(p,v)
def mutate_workflow(r,fn):
    n='reports/full-coverage/publication24-pages-view-execution-v1.log'
    mutate_json(r,n,fn)
    mutate_json(r,'reports/full-coverage/publication24-pages-view-execution-v1.json',lambda d:d.__setitem__('log_sha256',sha(r/n)))
def insert_forbidden_proof(r):
    n='verification/lean/future25.lean';raw(r/n,'explicit synthetic unselected proof fixture\n')
    mutate_json(r,PEER,lambda d:d['closed_evidence_sha256'].__setitem__(n,sha(r/n)))
def expect(name,which=UP,change=None,accept=False,verify=None,dirty=()):
    with tempfile.TemporaryDirectory(prefix='foundation24-delivery-code-fixture-') as td:
        r=Path(td);setup(r);fake=FakeSubprocess(dirty)
        if which==ST: execute(r,UP,fake)
        before={n:sha(r/n) for n in ['book/coverage/progress.json','reports/full-coverage/README.md']}
        if change:change(r)
        try:ns=execute(r,which,fake)
        except (AssertionError,KeyError,IndexError,FileNotFoundError,ValueError,TypeError) as e:
            assert not accept,(name,type(e).__name__,str(e))
            # All rejection fixtures must stop before any staging subprocess.
            assert not any(c['command'][1]=='add' for c in fake.calls)
            if which==UP:
                assert not (r/'reports/full-coverage/progress-checkpoint24-delivery-update-v1.json').exists()
            results.append({'fixture':name,'observed':'rejected','exception_type':type(e).__name__})
        else:
            assert accept,name
            if verify:verify(r,ns,fake)
            results.append({'fixture':name,'observed':'accepted','scope':'explicit synthetic isolated fixture'})

def updater_valid(r,ns,fake):
    p=load(r/'book/coverage/progress.json');rec=load(r/'reports/full-coverage/progress-checkpoint24-delivery-update-v1.json')
    assert rec['pages_run']==RUN_ID and rec['content_commit']==COMMIT and rec['coverage_complete'] is False
    assert p['last_published_content_commit']==p['last_published_commit']==COMMIT
    assert p['verified_checkpoint']=={'proof_files':1144,'theorems':9279,'coverage_complete':False}
    assert p['immutable_fixture_marker']=={'nested':[1,2,3]}
    old=load(r/'reports/full-coverage/progress-checkpoint24-before-delivery-update-original-v1.json')
    reconstructed=copy.deepcopy(p)
    for k in ['last_published_commit','last_published_content_commit','live_delivery_status','live_delivery_evidence','publication_status']:
        if k in old: reconstructed[k]=old[k]
        else: reconstructed.pop(k,None)
    reconstructed['working_next_checkpoint_preparation']['status']=old['working_next_checkpoint_preparation']['status']
    assert reconstructed==old
    text=(r/'reports/full-coverage/README.md').read_text()
    assert str(RUN_ID) in text and COMMIT in text and oldparagraph not in text
    assert text.startswith('unchanged opening\n') and text.endswith('unchanged closing\n')
    assert not any(c['command'][1]=='add' for c in fake.calls)

def stage_valid(r,ns,fake):
    rec=load(r/'reports/full-coverage/publication24-delivery-metadata-prestage-v1.json')
    assert rec['coverage_complete'] is False and rec['content_commit']==COMMIT
    assert fake.staged==ns['names']
    assert 'reports/full-coverage/publication24-prestage-v2.json' in fake.staged
    assert 'reports/full-coverage/publication24-prestage-v1.json' not in fake.staged
    assert OLD in fake.staged and OLD2 in fake.staged and ORIGINAL_PEER in fake.staged
    assert 'reports/full-coverage/stage-publication24-execution-v1.json' in fake.staged
    assert 'reports/full-coverage/stage-publication24-execution-v2.json' in fake.staged
    assert load(r/'reports/full-coverage/stage-publication24-execution-v1.json')['actual_exit_code']==1
    assert load(r/'reports/full-coverage/stage-publication24-execution-v2.json')['actual_exit_code']==0
    assert all(not n.startswith(('verification/lean/','SafeLearning/')) for n in fake.staged)
    for n,d in rec['paths_sha256'].items(): assert sha(r/n)==sha(r/'reports/book/publication-repo'/n)==d

expect('dynamic_run_id_exact_metadata_reverse_and_readme_replace',accept=True,verify=updater_valid)
for name,path,key,value in [
    ('live_failure','reports/full-coverage/live-checkpoint-24-attempt1.json','status','failed'),
    ('live_remote_commit_mismatch','reports/full-coverage/live-checkpoint-24-attempt1.json','remote_main','c'*40),
    ('pages_failure','reports/full-coverage/pages-checkpoint-24-attempt1.json','status','failed'),
    ('pages_expected_commit_mismatch','reports/full-coverage/pages-checkpoint-24-attempt1.json','expected_commit','c'*40),
    ('unverified_manifest','reports/full-coverage/checkpoint-24-manifest.json','status','frozen_inputs_not_yet_aggregate_verified'),
    ('audit_bad_theorem_count','reports/full-coverage/lean-checkpoint-24/verification-original.json','theorem_count',9278),
    ('complete_coverage_misstatement','reports/full-coverage/frozen-ledger-checkpoint24-v1.json','mathematical_coverage_complete',True),
    ('progress_wrong_publication_state','book/coverage/progress.json','publication_status','already_delivered')]:
    expect(name,change=lambda r,p=path,k=key,v=value:mutate_json(r,p,lambda d:d.__setitem__(k,v)))
expect('missing_live_asset',change=lambda r:mutate_json(r,'reports/full-coverage/live-checkpoint-24-attempt1.json',lambda d:d['assets'].pop()))
expect('actual_execution_failure',change=lambda r:mutate_json(r,'reports/full-coverage/publication24-content-push-execution-v1.json',lambda d:d.__setitem__('actual_exit_code',1)))
expect('actual_raw_log_tamper',change=lambda r:raw(r/'reports/full-coverage/publication24-content-push-execution-v1.log','tampered'))
expect('wrong_view_command',change=lambda r:mutate_json(r,'reports/full-coverage/publication24-pages-view-execution-v1.json',lambda d:d.__setitem__('actual_command',['fixture','not','gh','42'])))
expect('nonnumeric_dynamic_run_id',change=lambda r:mutate_json(r,'reports/full-coverage/publication24-pages-view-execution-v1.json',lambda d:d['actual_command'].__setitem__(3,'not-a-run')))
expect('empty_workflow_jobs',change=lambda r:mutate_workflow(r,lambda d:d.__setitem__('jobs',[])))
expect('failed_workflow_job',change=lambda r:mutate_workflow(r,lambda d:d['jobs'][0].__setitem__('conclusion','failure')))
expect('wrong_exercise_counts',change=lambda r:mutate_json(r,'reports/full-coverage/frozen-ledger-checkpoint24-v1.json',lambda d:d['counts']['statuses'].__setitem__('exercise:partial',18)))
expect('wrong_material_counts',change=lambda r:mutate_json(r,'reports/full-coverage/frozen-ledger-checkpoint24-v1.json',lambda d:d['counts']['material_review_statuses'].__setitem__('pending',8295)))
expect('readme_pending_paragraph_changed',change=lambda r:raw(r/'reports/full-coverage/README.md','incorrect pending prose'))
expect('preexisting_original_backup',change=lambda r:raw(r/'reports/full-coverage/progress-checkpoint24-before-delivery-update-original-v1.json','original must not overwrite'))
expect('explicit_closed_only_nul_metadata_stage',ST,accept=True,verify=stage_valid)
expect('out_of_whitelist_dirty_path',ST,dirty=['verification/lean/UnselectedFuture25.lean'])
expect('native_v2_stage_record_required',ST,change=lambda r:(r/'reports/full-coverage/publication24-prestage-v2.json').unlink())
expect('replacement_stage_actual_execution_failure',ST,change=lambda r:mutate_json(r,'reports/full-coverage/stage-publication24-execution-v2.json',lambda d:d.__setitem__('actual_exit_code',1)))
expect('first_stage_failure_cannot_be_relabeled_success',ST,change=lambda r:mutate_json(r,'reports/full-coverage/stage-publication24-execution-v1.json',lambda d:d.__setitem__('actual_exit_code',0)))
expect('first_stage_failure_raw_log_tamper',ST,change=lambda r:raw(r/'reports/full-coverage/stage-publication24-execution-v1.log','changed'))
expect('original_v1_peer_body_tamper',ST,change=lambda r:mutate_json(r,ORIGINAL_PEER,lambda d:d.__setitem__('reviewed_at_utc','changed')))
expect('original_v1_closed_checker_tamper',ST,change=lambda r:raw(r/next(iter(original_peer_body['closed_evidence_sha256'])),'changed'))
expect('stage_update_hash_tamper',ST,change=lambda r:mutate_json(r,'reports/full-coverage/progress-checkpoint24-delivery-update-v1.json',lambda d:d['updated_sha256'].__setitem__('book/coverage/progress.json','0'*64)))
expect('peer_wrong_helper_hash',ST,change=lambda r:mutate_json(r,PEER,lambda d:d['helpers_sha256'].__setitem__(ST,'0'*64)))
expect('peer_report_error',ST,change=lambda r:mutate_json(r,PEER,lambda d:d['errors'].append('real guard problem')))
expect('closed_provenance_hash_tamper',ST,change=lambda r:raw(r/'book/coverage/checks/future24-core/fixture-closed-evidence.txt','altered'))
expect('proof_source_inserted_into_metadata_evidence',ST,change=insert_forbidden_proof)
expect('preserved_root_asset_tamper',ST,change=lambda r:raw(r/'SafeLearning/fixture-asset-00.html','changed'))
expect('preserved_publication_asset_tamper',ST,change=lambda r:raw(r/'reports/book/publication-repo/SafeLearning/fixture-asset-00.html','changed'))
for n,d in PINS.items(): assert sha(ROOT/n)==d
out={'status':'independent_delivery_metadata_helper_code_fixtures_passed','errors':[],
     'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helpers_sha256':{n:PINS[n] for n in [UP,ST]},
     'preserved_entire_original_peer_body_and_time':original_peer_body,
     'preserved_original_peer':{'file':ORIGINAL_PEER,'sha256':sha(ROOT/ORIGINAL_PEER)},
     'preserved_unexecuted_metadata_stager_v2':{'file':OLD2,'sha256':PINS[OLD2]},
     'preserved_unexecuted_metadata_stager_v1':{'file':OLD,'sha256':PINS[OLD]},
     'fixture_count':len(results),'fixtures':results,
     'scope':'Code and explicit synthetic fixtures only. The two Root helpers were not run in production; no Git, gh, Pages, Lean, live owner, source, inventory, progress or publication checkout was mutated.',
     'actual_delivery_still_required':True,'future_audit_still_required':True,
     'readme_parent_helper':{'file':'book/coverage/checks/root_prepare_checkpoint24_documentation_v2.py','sha256':sha(ROOT/'book/coverage/checks/root_prepare_checkpoint24_documentation_v2.py')}}
with OBS.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'status':'passed','fixture_count':len(results),'production_execution':False}))
