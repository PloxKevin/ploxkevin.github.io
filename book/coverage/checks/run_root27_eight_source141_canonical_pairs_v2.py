"""Copy eight exact reviewed future27 sources and record sixteen real compiler commands.

Unexecuted draft. This installs new unselected sources and evidence only, retaining
original peer bodies, commands, times, warnings and failures through exact byte
aliases. No owner, HTML, inventory, selection, aggregate or publication writes.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,re,subprocess,sys,os
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future27-core/eight-source141-canonical-v1'
INPUT=Path('/tmp/root27-eight-source141-canonical-pair-draft-v2/eight-source141-reviewed-canonical-pair-inputs-v2.json')
INPUT_SHA='a6b357554b0ea32db067f381737da81a1a9a9259a80dcf83649a10fdea3e31ef'
RESULT=BASE/'eight-source141-actual-canonical-paired-readiness27-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def locate(n):
    p=Path(n)
    if p.is_absolute():
        assert p.resolve().is_relative_to(Path('/tmp')) or p.resolve().is_relative_to(ROOT)
    else:
        assert p.as_posix()==n and '..' not in p.parts and '.' not in p.parts
        p=ROOT/p
        assert p.resolve().is_relative_to(ROOT)
    assert p.is_file() and not p.is_symlink(),str(p)
    return p
def checked(ref):
    assert set(ref)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',ref['sha256'])
    p=locate(ref['file']);assert sha(p)==ref['sha256'],str(p)
    return p
def protection():
    PINNED = {
        'reports/full-coverage/checkpoint-26-selection.json': '12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f',
        'reports/full-coverage/checkpoint-25-selection.json': '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff',
        'reports/full-coverage/checkpoint-25-manifest.json': '0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363',
        'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json': '00a94eefea80aff4bd57ee2d511d3102f1a8652dfda1977272aefd9b7fe41cfb',
        'reports/full-coverage/owner26-reviewed-candidate-integration-v1.json': '7fa88d829c47797ab8258eb84ff5c7ce3399da66c9b03b591ea9820ca1eca06e',
        'reports/full-coverage/root-source53-final-owner-integration26-v1.json': '4029138dca32a74e8fd718fbe563d0b867d8ed408ad49a869e7308ea9867259d',
        'book/coverage/inventory.json': '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
        'book/coverage/inventory-after-correction55.json': '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
        'reports/full-coverage/source54-55-corrections-application-v1.json': '845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528',
        'reports/full-coverage/source54-55-corrections-application-execution-v1.json': 'a255862de464e0f1acf284807c4a48b732bc69055cf71b445ea2df5920494805',
        'book/coverage/material-corrections.json': '21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94',
        'book/coverage/inventory-after-correction53.json': '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be',
    }
    for name, digest in PINNED.items(): assert sha(ROOT / name) == digest, name
    selection = read('reports/full-coverage/checkpoint-26-selection.json')
    baseline = read('reports/full-coverage/checkpoint-25-selection.json')
    binding = read('book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json')
    integration = read('reports/full-coverage/owner26-reviewed-candidate-integration-v1.json')
    global_audit = read('reports/full-coverage/root-source53-final-owner-integration26-v1.json')
    assert selection['proof_file_count'] == len(selection['proof_files']) == 1167
    assert selection['new_file_count'] == binding['new_proof_sources'] == 11
    assert len(baseline['proof_files']) == 1156
    assert set(baseline['proof_files']) <= set(selection['proof_files'])
    assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline['proof_files'].items())
    assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
    assert integration['applied'] is True and integration['all44111_frozen25_inputs_exact'] is True
    assert integration['all1156_selected25_root_source_hashes_exact'] is True
    application = read('reports/full-coverage/source54-55-corrections-application-v1.json')
    assert application['status'] == 'passed_actual_source54_and_source55_corrections_full29_inventory_owner_identity_rebase_pending'
    assert application['selected26_proof_sources_unchanged'] == 1167
    assert application['five_installed26_owner_ledgers_unchanged'] is True
    assert application['coverage_complete'] is False
    assert [r['correction_id'] for r in application['applications']] == [54,55]
    expected_changed_assets = {
        'SafeLearning/lyapunov-mpc.html': '63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f',
        'SafeLearning/verification.html': 'd01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53',
    }
    assert {r['source_after']['file']:r['source_after']['sha256'] for r in application['applications']} == expected_changed_assets
    assets = {**binding['exact_current53_safelearning_assets_sha256'],**expected_changed_assets}
    assert len(assets) == 31
    assert read('book/coverage/inventory-after-correction55.json')['source_sha256'] == {n:h for n,h in assets.items() if n.endswith('.html')}
    owners = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
    assert len(owners) == 5
    for row in global_audit['domains']:
        assert row['ledger_sha256'] == owners['book/coverage/' + row['domain'] + '.json']
    held = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    held.update(assets)
    held.update(owners)
    corrections = 'book/coverage/material-corrections.json'
    assert len(read(corrections)['corrections']) == 55
    old_corrections_path = ROOT / 'reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root/book/coverage/material-corrections.json'
    assert sha(old_corrections_path) == binding['source53_corrections_sha256']
    assert read(corrections)['corrections'][:53] == json.loads(old_corrections_path.read_text())['corrections']
    assert [r['correction_id'] for r in read(corrections)['corrections'][53:]] == [54,55]
    for stem in ('owner26-integration-apply-execution-v1', 'root-source53-final-owner-integration26-execution-v1', 'prepare-checkpoint26-selection-execution-v1', 'source54-55-corrections-application-execution-v1'):
        name = 'reports/full-coverage/' + stem + '.json'
        actual = read(name)
        codes = [actual[k] for k in ('actual_exit_code', 'exit_code') if k in actual]
        assert codes and all(type(code) is int and code == 0 for code in codes)
        assert actual['actual_workdir'] == str(ROOT)
        assert actual['helper_sha256_before'] == actual['helper_sha256_after']
        assert sha(ROOT / actual['log']) == actual['log_sha256']
        for helper, digest in actual['helper_sha256_after'].items():
            assert sha(ROOT / helper) == digest
            PINNED[helper] = digest
        PINNED[name] = sha(ROOT / name)
        PINNED[actual['log']] = actual['log_sha256']
    for name in ('verification/lean/lean-toolchain', 'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json'):
        PINNED[name] = sha(ROOT / name)

    return {**held,**PINNED}

def check_guard(protected,helper_sha):
    for n,h in protected.items():assert sha(ROOT/n)==h,n
    assert sha(Path(__file__))==helper_sha

def canonical_name(n):
    p=Path(n);assert p.as_posix()==n and p.parent==Path('verification/lean/SafeLearning')
    assert p.suffix=='.lean' and p.stem.startswith('Complete') and p.stem.isidentifier()
    return p.stem

def preflight():
    assert sha(INPUT)==INPUT_SHA
    d=json.loads(INPUT.read_text());assert d['source_count']==len(d['source_rows'])==8
    assert d['public_theorem_count']==sum(r['public_theorem_count'] for r in d['source_rows'])==141
    assert d['planned_real_compiler_commands']==16
    assert d['current55_guard_runner']['sha256']=='3336a4d2b00252decb7b7b010f62adfdc9d564d78cbc749ee8f1584242e787b0'
    checked(d['current55_guard_runner'])
    expected_helpers={'standalone':('book/coverage/check_core_standalone.py','124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a'),'named':('book/coverage/check_core_named_build.py','605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069')}
    for kind,(n,h) in expected_helpers.items():assert d['actual_compiler_helpers'][kind]=={'file':n,'sha256':h};checked(d['actual_compiler_helpers'][kind])
    protected=protection();helper_sha=sha(Path(__file__));check_guard(protected,helper_sha)
    selection=read('reports/full-coverage/checkpoint-26-selection.json')
    assert not BASE.exists() and not RESULT.exists()
    originals={}
    for item in d['explicit_original_byte_alias_rows']:
        assert set(item)=={'original_file','original_sha256','exact_existing_byte_copy'}
        assert item['original_sha256']==item['exact_existing_byte_copy']['sha256']
        checked(item['exact_existing_byte_copy'])
        key=item['original_file']+'::'+item['original_sha256'];assert key not in originals
        originals[key]=item
    for r in d['original_input_packets']:checked(r)
    names=set();exports=set()
    for r in d['source_rows']:
        name=canonical_name(r['canonical_source']);assert name not in names;names.add(name)
        assert r['canonical_source'] not in selection['proof_files'] and not (ROOT/r['canonical_source']).exists()
        for suffix in ('-standalone.json','.log','-named-build.json','-named-build.log'):
            assert not (ROOT/'book/coverage/checks'/(name+suffix)).exists()
        src=checked(r['source']);assert src.suffix=='.lean' and src.is_absolute() and src.resolve().is_relative_to(Path('/tmp'))
        assert len(r['all_public_declarations'])==r['public_theorem_count'] and not exports.intersection(r['all_public_declarations']);exports.update(r['all_public_declarations'])
        assert sorted(re.findall(r'^theorem\s+([A-Za-z0-9_]+)',src.read_text(),re.M))==sorted(n.rsplit('.',1)[1] for n in r['all_public_declarations'])
        peer=json.loads(checked(r['original_semantic_peer']).read_text());assert peer['errors']==[]
        if r['original_semantic_peer']['sha256']=='554fcbf844cbb8ef0f79e2df86cc0a09a42e009e94408f416cdf61666dc5d3f5':
            assert peer['status']=='independent_full_source55_virtual_whole_exercise_and_five_literals_approved' and peer['source55_virtual_exercise']['whole_exercise_approved'] is True
        else:assert 'passed' in peer['status']
        actual=json.loads(checked(r['actual_original_tmp_standalone']).read_text())
        codes=[actual[k] for k in ('actual_exit_code','exit_code','actual_runner_exit_code') if k in actual]
        assert codes and all(type(c) is int and c==0 for c in codes)
        assert actual['source_sha256_before']==actual['source_sha256_after']==r['source']['sha256']
        assert actual['actual_command']==['lake','env','lean',r['source']['file']]
        assert actual['actual_workdir']==str(ROOT/'verification/lean')
        checked({'file':actual['raw_log'],'sha256':actual['raw_log_sha256']})
        assert actual['source_snapshot_sha256']==r['source']['sha256']
        checked({'file':actual['source_snapshot'],'sha256':actual['source_snapshot_sha256']})
        for ref in (r['source'],r['original_semantic_peer'],r['actual_original_tmp_standalone']):
            key=ref['file']+'::'+ref['sha256'];assert key in originals
    assert len(exports)==141
    for p in (INPUT,Path(__file__),checked(d['prepared_by'])):
        key=str(p)+'::'+sha(p)
        if key not in originals:originals[key]={'original_file':str(p),'original_sha256':sha(p),'exact_existing_byte_copy':{'file':str(p),'sha256':sha(p)}}
    check_guard(protected,helper_sha)
    return d,protected,helper_sha,originals

def copy_new(source,target,digest):
    assert sha(source)==digest and not source.is_symlink()
    target.parent.mkdir(parents=True,exist_ok=True)
    assert not target.exists()
    with target.open('xb') as f:f.write(source.read_bytes())
    assert sha(target)==digest

def execute():
    d,protected,helper_sha,originals=preflight()
    # All input hashes, current guards and sixteen unused record/log destinations
    # have been checked before the first archive or canonical source write.
    aliases={};copied={}
    for key,item in sorted(originals.items()):
        p=checked(item['exact_existing_byte_copy']);h=item['original_sha256']
        # Content-hash directories avoid basename length expansion and retain the
        # literal original filename without rewriting the original record body.
        target=BASE/'original-closed-bytes'/h/p.name
        if target in copied:assert copied[target]==h
        else:copy_new(p,target,h);copied[target]=h
        aliases[key]={'original_file':item['original_file'],'original_sha256':h,'file':target.relative_to(ROOT).as_posix(),'sha256':h}
    source_snapshots={}
    for r in d['source_rows']:
        src=checked(r['source']);h=r['source']['sha256'];dest=ROOT/r['canonical_source']
        copy_new(src,dest,h);snapshot=BASE/'source-snapshots'/dest.name
        copy_new(src,snapshot,h);source_snapshots[r['canonical_source']]={'file':snapshot.relative_to(ROOT).as_posix(),'sha256':h}
    check_guard(protected,helper_sha)
    pairs=[];child_environment=dict(os.environ);child_environment.pop('PYTHONHOME',None)
    for r in d['source_rows']:
        name=canonical_name(r['canonical_source']);h=r['source']['sha256']
        for kind,suffix in (('standalone','-standalone.json'),('named','-named-build.json')):
            check_guard(protected,helper_sha)
            for other in d['source_rows']:assert sha(ROOT/other['canonical_source'])==other['source']['sha256']
            helper=d['actual_compiler_helpers'][kind];checked(helper)
            command=[sys.executable,helper['file'],name]
            run=subprocess.run(command,cwd=ROOT,env=child_environment)
            check_guard(protected,helper_sha)
            p=ROOT/'book/coverage/checks'/(name+suffix);assert p.is_file()
            record=json.loads(p.read_text());assert type(record['exit_code']) is int
            assert record['exit_code']==run.returncode
            assert record['source']==r['canonical_source'] and record['source_sha256_before']==record['source_sha256_after']==h
            expected=['lake','env','lean','SafeLearning/'+name+'.lean'] if kind=='standalone' else ['lake','build','SafeLearning.'+name]
            assert record['command']==expected and record['actual_workdir']==str(ROOT/'verification/lean')
            log=checked({'file':record['log'],'sha256':record['log_sha256']})
            assert log==ROOT/'book/coverage/checks'/(name+('.log' if kind=='standalone' else '-named-build.log'))
            pairs.append({'kind':kind,'source':{'file':r['canonical_source'],'sha256':h},'actual_record':{'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)},'raw_log':{'file':record['log'],'sha256':record['log_sha256']},'source_snapshot':source_snapshots[r['canonical_source']],'actual_exit_code':record['exit_code'],'actual_helper':helper,'actual_helper_invocation':command})
            if run.returncode:raise SystemExit(run.returncode)
    check_guard(protected,helper_sha)
    for row in d['source_rows']:
        assert sha(ROOT/row['canonical_source'])==row['source']['sha256']
    assert len(pairs)==16 and all(x['actual_exit_code']==0 for x in pairs)
    for item in aliases.values():assert sha(ROOT/item['file'])==item['sha256']
    result={'status':'passed_actual_eight_source141_canonical_standalone_and_named_pairs_unselected_future27','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':8,'public_theorem_count':141,'actual_compiler_command_count':16,'sources':d['source_rows'],'actual_paired_records':pairs,'source_snapshots':source_snapshots,'original_closed_byte_aliases':aliases,'entire_original_input_packet_and_time':d,'actual_helper':{'file':str(Path(__file__)),'sha256':helper_sha},'protected_selected26_source_count':1167,'protected_current55_asset_count':31,'protected_installed26_owner_count':5,'protected_input_sha256':protected,'coverage_complete':False,'owner_installation_claimed':False,'selection_or_aggregate_or_publication_claimed':False,'scope':'Exact new unselected canonical source copies and sixteen actual compiler commands. Every historical peer/record/log/source/failure body and original time remains unchanged through explicit byte aliases. Mathematical scope decisions remain those of the original independent peers; Root Core11 is precise components only.'}
    with RESULT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','readiness':RESULT.relative_to(ROOT).as_posix(),'sha256':sha(RESULT),'sources':8,'exports':141,'actual_commands':16}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--apply',action='store_true');args=parser.parse_args()
    assert args.apply,'This draft performs no default execution. Root must explicitly run reviewed --apply.'
    execute()
