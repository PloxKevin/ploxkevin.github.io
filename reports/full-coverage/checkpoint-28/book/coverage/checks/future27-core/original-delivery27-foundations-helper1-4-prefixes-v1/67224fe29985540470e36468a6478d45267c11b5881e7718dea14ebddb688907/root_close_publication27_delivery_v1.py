"""Root-only checkpoint27 delivery metadata update and explicit metadata staging.

prepare_update() reads native evidence and returns exact prospective bytes.
Neither authoring nor a fixture constitutes successful live delivery.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,re,subprocess,yaml

ROOT=Path('/home/oxrexkevin/SafetyBased')
PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_close_publication27_delivery_v1.py'
REPORT='reports/full-coverage/progress-checkpoint27-delivery-update-v1.json'
STAGE_REPORT='reports/full-coverage/publication27-delivery-metadata-prestage-v1.json'
PROGRESS='book/coverage/progress.json';README='reports/full-coverage/README.md'
BACKUPS={PROGRESS:'reports/full-coverage/progress-checkpoint27-before-delivery-update-original-v1.json',README:'reports/full-coverage/README-checkpoint27-before-delivery-update-original-v1.md'}
PINS={PROGRESS:'246fd7146ed5ce902c0f50d078c33dd784d290eeab18e8054adbd73faca3ad1e',README:'1f3d89b2cd265652cc518db748edbe200371acd5496fc10d33f3458f74f6d0e9','book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94','reports/full-coverage/checkpoint-27-selection.json':'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd','reports/full-coverage/checkpoint-27-manifest.json':'196700f9fd69a0a7610f4a2b3d6bad20cfcb34688faa53f5f2fb8b688c085044','reports/full-coverage/lean-checkpoint-27/verification-original.json':'fdd431eea1137c48032d20cdb31270b8d76a4ca715f19715167a1ec67cff194f','reports/full-coverage/verify-checkpoint27-execution-v1.json':'76fc3800338dd07c11f11b273c0138a90f40afb9c40cb31373d4f4b5aebc349c','reports/full-coverage/lean-checkpoint-27/ledger-audit.json':'c3b6a0a8c3f6761c0cb24ff16537aa6d2c970bafe7b575de79a89a534e9972f4','book/coverage/verify_live19.py':'2a06c87ff21b5c0385076d22e7b3ce8ea8865a4be678da4002c47b48f61cb62b'}
LIVE='reports/full-coverage/live-checkpoint-27-attempt1.json'
PAGES='reports/full-coverage/pages-checkpoint-27-attempt1.json'
STEMS=['publication27-content-commit-execution-v1','publication27-content-push-execution-v1','publication27-pages-view-execution-v1','live27-attempt1-execution-v1']
OLD="Checkpoint 26's completed GitHub Pages\nand live delivery remain in the progress history. Checkpoint 27 delivery\nawaits an actual push, Pages build and live asset-hash checks.\n"
def safe(n,base=None):
    base=ROOT if base is None else base
    assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in ('\0','\n','\r'))
    p=base/n;assert p.resolve().is_relative_to(base.resolve()) and not p.is_symlink();return p
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def encoded(d):return (json.dumps(d,indent=2)+'\n').encode()
def read(n):return json.loads(safe(n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(safe(n))}
def aliases(d,keys):
    values=[d[k] for k in keys if k in d];assert values and all(v==values[0] for v in values)
    return values[0]
def zero(d):
    values=[d[k] for k in ('exit_code','actual_exit_code','actual_runner_exit_code') if k in d]
    assert values and all(type(v) is int and v==0 for v in values)
def actual(n):
    d=read(n);zero(d)
    command=aliases(d,('command','actual_command'));cwd=aliases(d,('cwd','working_directory','actual_workdir'))
    log=aliases(d,('log','raw_log'));h=aliases(d,('log_sha256','raw_log_sha256'));assert sha(safe(log))==h
    assert type(command) is list and all(type(x) is str for x in command)
    assert cwd in (str(ROOT),str(PUB))
    return d,command,cwd,log
def git(command):return subprocess.run(['git',*command],cwd=PUB,check=True,capture_output=True).stdout
def immutable():
    for n,h in PINS.items():
        if n not in (PROGRESS,README):assert sha(safe(n))==h,n
    selection=read('reports/full-coverage/checkpoint-27-selection.json');manifest=read('reports/full-coverage/checkpoint-27-manifest.json');audit=read('reports/full-coverage/lean-checkpoint-27/verification-original.json')
    proofmap={n:r['sha256'] for n,r in selection['proof_files'].items()}
    assert len(proofmap)==selection['proof_file_count']==audit['proof_file_count']==1175
    assert proofmap=={n:r['sha256'] for n,r in manifest['proof_files'].items()}==audit['proof_sha256']
    assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets)==31 and assets==audit['source_sha256']
    for n,h in {**proofmap,**assets}.items():assert sha(safe(n))==sha(safe(n,PUB))==h,n
    owners=read('reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements'];assert len(owners)==5
    for r in owners:assert sha(safe(r['destination']))==sha(safe(r['destination'],PUB))==r['candidate']['sha256']
    assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
    assert manifest['selection_sha256']==PINS['reports/full-coverage/checkpoint-27-selection.json']
    assert manifest['successful_verification']['report_sha256']==PINS['reports/full-coverage/lean-checkpoint-27/verification-original.json']
    assert audit['status']=='passed' and audit['theorem_count']==9644
    assert len(audit['checks'])==1178
    for c in audit['checks']:zero(c)
    assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==8
    assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1167
    names={r['name'] for r in audit['declarations']}
    assert len(audit['declarations'])==len(names)==len(audit['axiom_dependencies'])==9644 and names==set(audit['axiom_dependencies'])
    assert all(r['file'] in proofmap for r in audit['declarations'])
    allowed={'propext','Classical.choice','Quot.sound'};assert set(audit['allowed_standard_axioms'])==allowed
    assert all(set(xs)<=allowed for xs in audit['axiom_dependencies'].values())
    execution,command,cwd,_=actual('reports/full-coverage/verify-checkpoint27-execution-v1.json')
    assert command==['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(ROOT/'reports/full-coverage/checkpoint-26')] and cwd==str(ROOT)
    verify='reports/full-coverage/checkpoint-27/verification/lean/verify.py'
    assert execution['helper_sha256_before']==execution['helper_sha256_after']=={verify:sha(safe(verify))}
    ledger=read('reports/full-coverage/lean-checkpoint-27/ledger-audit.json')
    assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
    counts=ledger['counts'];assert (counts['exercises'],counts['material_source_units'])==(556,12774)
    assert {k:counts['statuses']['exercise:'+v] for k,v in [('complete','complete_math'),('partial','partial'),('pending','pending')]}=={'complete':519,'partial':16,'pending':21}
    assert counts['material_review_statuses']=={'reviewed':4574,'pending':8200}
    assert len(read('book/coverage/material-corrections.json')['corrections'])==55
    return assets
def delivery():
    assets=immutable();live=read(LIVE);commit=live['commit'];assert re.fullmatch(r'[0-9a-f]{40}',commit)
    assert live['status']=='passed_all31_asset_sha256' and live['remote_main']==commit
    assert len(live['assets'])==31 and {r['source']:r['expected_sha256'] for r in live['assets']}==assets
    assert len({r['source'] for r in live['assets']})==31
    for r in live['assets']:assert type(r['http_status']) is int and r['http_status']==200 and r['matches'] is True and r['actual_sha256']==assets[r['source']]
    remote=live['remote_head_check'];zero(remote)
    assert aliases(remote,('command','actual_command'))==['git','ls-remote','origin','refs/heads/main']
    assert aliases(remote,('cwd','working_directory','actual_workdir'))==str(PUB)
    assert remote['output'].split()==[commit,'refs/heads/main']
    assert git(['rev-parse','HEAD']).decode().strip()==commit
    assert git(['ls-remote','origin','refs/heads/main']).decode().split()==[commit,'refs/heads/main']
    pages,command,cwd,pageslog=actual(PAGES)
    assert pages['status']=='passed' and pages['build_status']=='built' and pages['commit']==pages['expected_commit']==commit
    assert command==['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest'] and cwd==str(PUB)
    build=read(pageslog);assert build['status']=='built' and build['commit']==commit
    evidence={LIVE:sha(safe(LIVE)),PAGES:sha(safe(PAGES)),pageslog:sha(safe(pageslog))}
    records=[]
    for stem in STEMS:
        n='reports/full-coverage/'+stem+'.json';d,cmd,cwd,log=actual(n)
        evidence.update({n:sha(safe(n)),log:sha(safe(log))});records.append((d,cmd,cwd,log))
    cc,cmd,cwd,_=records[0]
    assert cwd==str(ROOT) and cmd[:5]==['git','-C',str(PUB),'commit','-m'] and len(cmd)==6
    assert git(['show','-s','--format=%s',commit]).decode().rstrip('\n')==cmd[5]
    assert records[1][1]==['git','-C',str(PUB),'push','origin','main'] and records[1][2]==str(ROOT)
    view,cmd,_,log=records[2];assert cmd[:3]==['gh','run','view'] and cmd[3].isdigit();run=int(cmd[3])
    tails=[['--json','headSha,status,conclusion,jobs,url,databaseId'],['--repo','PloxKevin/ploxkevin.github.io','--json','headSha,status,conclusion,jobs,url,databaseId'],['--repo','ploxkevin/ploxkevin.github.io','--json','headSha,status,conclusion,jobs,url,databaseId']]
    assert cmd[4:] in tails
    workflow=read(log);assert workflow['headSha']==commit and workflow['status']=='completed' and workflow['conclusion']=='success'
    assert type(workflow['databaseId']) is int and workflow['databaseId']==run
    assert workflow['url'].lower()==f'https://github.com/ploxkevin/ploxkevin.github.io/actions/runs/{run}'
    assert workflow['jobs'] and all(j['status']=='completed' and j['conclusion']=='success' for j in workflow['jobs'])
    liveactual,cmd,cwd,_=records[3]
    assert cmd==['python3','book/coverage/verify_live19.py','27',commit,'--attempt','1'] and cwd==str(ROOT)
    assert liveactual['helper_sha256_before']==liveactual['helper_sha256_after']=={'book/coverage/verify_live19.py':PINS['book/coverage/verify_live19.py']}
    summary=json.loads(safe(records[3][3]).read_text());assert summary=={'live':'passed_all31_asset_sha256','matching_assets':31,'pages':'passed','remote_main':commit}
    evidence.update({n:sha(safe(n)) for n in PINS if n not in (PROGRESS,README)})
    return commit,run,evidence
def prepare_update():
    for n in (PROGRESS,README):assert sha(safe(n))==PINS[n]
    assert all(not safe(n).exists() for n in [REPORT,*BACKUPS.values()])
    commit,run,evidence=delivery();p=read(PROGRESS);before=safe(README).read_text();assert before.count(OLD)==1
    assert p['publication_status']=='checkpoint27_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks' and p['live_delivery_evidence'] is None
    assert p['verified_checkpoint']['coverage_complete'] is False and (p['verified_checkpoint']['proof_files'],p['verified_checkpoint']['theorems'])==(1175,9644)
    assert p['working_next_checkpoint_preparation']['exercise_counts']=={'complete':519,'partial':16,'pending':21}
    assert p['working_next_checkpoint_preparation']['material_review_units']=={'reviewed':4574,'pending':8200}
    assert p['last_published_content_commit']==p['previous_checkpoint26_delivery']['content_commit']=='68fa8a62c5085c3dbc92ec6c80e5dfd9f3e2e381'
    p.update(last_published_commit=commit,last_published_content_commit=commit,live_delivery_status='passed_all31_asset_sha256',live_delivery_evidence=LIVE,publication_status='checkpoint27_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial')
    p['working_next_checkpoint_preparation']['status']='checkpoint27_passed_actual_frozen_audit_and_live_delivery_full_coverage_work_continues'
    new=("Checkpoint 26's completed GitHub Pages\nand live delivery remain in the progress history. "
        f'Checkpoint 27 is [pushed to GitHub](https://github.com/PloxKevin/ploxkevin.github.io/commit/{commit}).\n'
        f'The [actual Pages workflow](https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/{run})\n'
        'completed successfully, and [live delivery](live-checkpoint-27-attempt1.json)\n'
        'matched all 31 book asset hashes and the built commit exactly. Full coverage work continues.\n')
    outputs={PROGRESS:encoded(p),README:before.replace(OLD,new,1).encode()}
    outputs.update({backup:safe(original).read_bytes() for original,backup in BACKUPS.items()})
    record={'status':'passed_actual_checkpoint27_delivery_progress_update','updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':SELF,'sha256':sha(Path(__file__))},'content_commit':commit,'pages_run':run,'originals':{n:{'file':b,'sha256':PINS[n]} for n,b in BACKUPS.items()},'updated_sha256':{n:hashlib.sha256(outputs[n]).hexdigest() for n in (PROGRESS,README)},'evidence_sha256':evidence,'exercise_counts':{'complete':519,'partial':16,'pending':21},'material_review_units':{'reviewed':4574,'pending':8200},'coverage_complete':False,'scope':'Actual delivery metadata only. Original prepared documents retain their bytes and times; all prior delivery history, source55, selected proofs, owner records and semantic reviews remain unchanged.'}
    outputs[REPORT]=encoded(record);return record,outputs
def update(apply):
    d,outputs=prepare_update()
    if apply:
        for n in (PROGRESS,README):assert sha(safe(n))==PINS[n]
        for n,b in outputs.items():
            safe(n).parent.mkdir(parents=True,exist_ok=True)
            if n in (PROGRESS,README):safe(n).write_bytes(b)
            else:
                with safe(n).open('xb') as f:f.write(b)
        immutable()
    print(json.dumps({'status':'applied' if apply else 'prospective_only','record':d,'prospective_paths_sha256':{n:hashlib.sha256(b).hexdigest() for n,b in outputs.items()}}))
def metadata(n):
    safe(n);assert n in (PROGRESS,README) or n.startswith(('reports/full-coverage/','book/coverage/checks/'))
    assert not n.startswith(('reports/full-coverage/checkpoint-','reports/full-coverage/lean-checkpoint-'))
def stage(supplement,supplement_sha,apply):
    commit,run,_=delivery();update_record=read(REPORT)
    assert update_record['status']=='passed_actual_checkpoint27_delivery_progress_update' and update_record['content_commit']==commit and update_record['coverage_complete'] is False
    assert update_record['helper']=={'file':SELF,'sha256':sha(Path(__file__))}
    for n,h in {**update_record['evidence_sha256'],**update_record['updated_sha256']}.items():assert sha(safe(n))==h,n
    for n,r in update_record['originals'].items():assert r=={'file':BACKUPS[n],'sha256':PINS[n]} and sha(safe(r['file']))==PINS[n]
    assert sha(safe(supplement))==supplement_sha;extra=read(supplement)
    assert extra['status']=='explicit_reviewed_checkpoint27_delivery_metadata_plan' and extra['content_commit']==commit and extra['coverage_complete'] is False
    assert extra['files_sha256'] and extra['independent_reviews']
    names={SELF,REPORT,PROGRESS,README,supplement,*BACKUPS.values(),LIVE,PAGES}
    names.update(n for n in update_record['evidence_sha256'] if n not in PINS)
    names.update(extra['files_sha256'])
    for r in extra['independent_reviews']:
        assert r['file'] in names and extra['files_sha256'][r['file']]==r['sha256']
        peer=read(r['file']);assert peer['status']=='passed_independent_full_delivery27_helper_review' and peer['errors']==[] and peer['helper_sha256']==sha(Path(__file__))
    expected={}
    for n in names:
        metadata(n);p=safe(n);assert p.is_file() and not p.is_symlink() and p.stat().st_size<100_000_000
        expected[n]=sha(p)
        if n in extra['files_sha256']:assert expected[n]==extra['files_sha256'][n]
    assert not safe(STAGE_REPORT).exists() and not safe(STAGE_REPORT,PUB).exists()
    assert git(['diff','--cached','--name-only','-z'])==b''
    dirty=git(['status','--porcelain','-z','--untracked-files=all']).decode().split('\0')
    for entry in filter(None,dirty):assert entry[:2] in (' M','??') and entry[3:] in names,entry
    assert safe('_config.yml',PUB).read_bytes()==git(['show','HEAD:_config.yml'])
    config=yaml.safe_load(safe('_config.yml',PUB).read_text());excluded=config['exclude']
    assert type(excluded) is list and len(excluded)==len(set(excluded))
    for n in excluded:safe(n);assert not any(c in n for c in ('*','?','[','{'))
    kept=lambda n:not any(n==e or n.startswith(e+'/') for e in excluded)
    total=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
    delta=sum(safe(n).stat().st_size-(safe(n,PUB).stat().st_size if safe(n,PUB).is_file() else 0) for n in expected if kept(n))
    d={'status':'passed_explicit_completed27_delivery_metadata','checked_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(Path(__file__)),'content_commit':commit,'pages_run':run,'paths_sha256':expected,'supplement':ref(supplement),'included_website_bytes_before_copy':total,'included_replacement_byte_delta':delta,'coverage_complete':False}
    b=encoded(d);assert 0<=total+delta+(len(b) if kept(STAGE_REPORT) else 0)<850_000_000
    if apply:
        for n,h in expected.items():assert sha(safe(n))==h,n
        with safe(STAGE_REPORT).open('xb') as f:f.write(b)
        expected[STAGE_REPORT]=sha(safe(STAGE_REPORT))
        for n,h in expected.items():
            p=safe(n,PUB);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(safe(n).read_bytes());assert sha(p)==h
        git(['add','--',*sorted(expected)])
        staged={n for n in git(['diff','--cached','--name-only','-z']).decode().split('\0') if n};assert staged<=set(expected)
        for n in staged:assert hashlib.sha256(git(['show',':'+n])).hexdigest()==expected[n]
        immutable()
    print(json.dumps({'status':'staged' if apply else 'prospective_only','record':d,'coverage_complete':False}))
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=['update','stage']);parser.add_argument('--apply',action='store_true');parser.add_argument('--supplement');parser.add_argument('--supplement-sha')
    args=parser.parse_args()
    if args.mode=='update':assert args.supplement is None and args.supplement_sha is None;update(args.apply)
    else:assert args.supplement and args.supplement_sha;stage(args.supplement,args.supplement_sha,args.apply)
if __name__=='__main__':main()
