"""Stage audited25 inputs and closed preparation evidence after every actual gate.

Root executes this helper. Authoring or reviewing this code does not execute any
audit, publication copy, Git operation, Pages build, or live delivery check.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
REPORT='reports/full-coverage/publication25-prestage-v1.json'
PEER='book/coverage/checks/future25-core/publication25-stage-independent-review-v3.json'
CONFIG_HELPER='book/coverage/checks/root_prepare_pages25_config_v1.py'
CONFIG_HELPER_SHA='04207875a69824919c74a78d0fc95b415369cbceaab24989815b7b96dafaccad'
CONFIG_CODE_PEER='book/coverage/checks/pages25-config-helper-independent-modules-review-v1.json'
CONFIG_OUTPUT_PEER='book/coverage/checks/future25-core/pages25-config-independent-modules-review-v1.json'
ROOT_OUTPUT='book/coverage/checks/future25-core/root-checkpoint25-production-output-independent-confirmation-v1.json'
MODULE_OUTPUT='book/coverage/checks/future25-core/modules-checkpoint25-production-output-independent-confirmation-v1.json'

def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert str(Path(n))==n and not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve())
    return p
def target(n):
    safe(n);p=PUB/n;assert p.resolve().is_relative_to(PUB.resolve());return p
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def zero(d,code=0):
    values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(v) is int and v==code for v in values)
def actual(n,code=0):
    d=read(n);zero(d,code)
    logs=[d[k] for k in ('log','raw_log') if k in d]
    hashes=[d[k] for k in ('log_sha256','raw_log_sha256') if k in d]
    assert logs and hashes and all(x==logs[0] for x in logs) and all(x==hashes[0] for x in hashes)
    assert sha(safe(logs[0]))==hashes[0]
    return d,logs[0]
def dirty():
    raw=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=PUB,check=True,capture_output=True).stdout
    out=set()
    for entry in filter(None,raw.decode().split('\0')):
        assert entry[:2] not in {'R ',' R','C ',' C'} and 'D' not in entry[:2],entry
        out.add(entry[3:])
    return out
def staged():
    return {n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,
       check=True,capture_output=True).stdout.split(b'\0') if n}
def peer_evidence(n,paths):
    peer=read(n);assert 'passed' in peer['status'] and peer.get('errors',[])==[]
    paths.add(n)
    aliases=peer.get('original_closed_byte_aliases',{})
    assert isinstance(aliases,dict)
    canonical=set()
    for original,row in aliases.items():
        assert isinstance(original,str) and Path(original).is_absolute()
        assert not any(c in original for c in ('\0','\n','\r'))
        assert isinstance(row,dict) and set(row)=={'file','sha256'}
        n2=row['file'];digest=row['sha256']
        assert n2 not in canonical and isinstance(digest,str) and len(digest)==64
        assert all(c in '0123456789abcdef' for c in digest) and sha(safe(n2))==digest
        canonical.add(n2);paths.add(n2)
    closed=peer.get('closed_evidence_sha256',{})
    assert isinstance(closed,dict)
    for original,digest in closed.items():
        if Path(original).is_absolute():
            assert original in aliases and aliases[original]['sha256']==digest
            n2=aliases[original]['file']
        else:n2=original
        assert sha(safe(n2))==digest;paths.add(n2)
    return peer

def main():
    assert not safe(REPORT).exists() and not target(REPORT).exists()
    manifest_name='reports/full-coverage/checkpoint-25-manifest.json'
    selection_name='reports/full-coverage/checkpoint-25-selection.json'
    audit_name='reports/full-coverage/lean-checkpoint-25/verification-original.json'
    manifest,selection,audit=map(read,(manifest_name,selection_name,audit_name))
    assert manifest['status']=='formal_verification_passed_partial_coverage'
    assert manifest['selection_sha256']==sha(safe(selection_name))
    assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1156
    assert manifest['proof_files']==selection['proof_files']
    assert selection['new_file_count']==12 and selection['coverage_complete'] is False
    assert audit['status']=='passed' and audit['theorem_count']==9369
    assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
    assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==12
    assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1144
    assert audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}
    assert manifest['successful_verification']['report_sha256']==sha(safe(audit_name))
    assert selection['current_inventory_sha256']==sha(safe('book/coverage/inventory.json'))==sha(safe('book/coverage/inventory-after-correction52.json'))=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
    ledger_name='reports/full-coverage/publication-checks/ledger-checkpoint-25.json'
    ledger=read(ledger_name)
    assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
    assert ledger['inventory_sha256']==selection['current_inventory_sha256']
    for row in ledger['domains']:assert row['ledger_sha256']==sha(target('book/coverage/'+row['domain']+'.json'))
    paths=set(read('reports/full-coverage/publication-prepared-25-files.json'))
    assert set(manifest['frozen_inputs_sha256'])<=paths
    snapshot=safe(manifest['snapshot'])
    for n,digest in manifest['frozen_inputs_sha256'].items():
        assert sha(snapshot/n)==digest and target(n).is_file(),n
        if n not in {'book/coverage/progress.json','reports/full-coverage/README.md'}:assert sha(target(n))==digest,n
    for n,row in manifest['proof_files'].items():assert sha(safe(n))==sha(target(n))==row['sha256'],n
    assets={n:d for n,d in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets)==31
    for n,d in assets.items():assert sha(safe(n))==sha(target(n))==d,n
    config_name='reports/full-coverage/pages25-config-preparation-v1.json';config=read(config_name)
    assert 'passed' in config['status'] and config['coverage_complete'] is False
    assert config['selected_sources']==1156 and config['public_theorems']==9369
    assert config['all31_source52_assets_exact'] is True
    assert config['excluded_count']==len(config['exclusions'])==97
    assert type(config['prospective_included_website_bytes_before_new_native_records']) is int
    assert 0<=config['prospective_included_website_bytes_before_new_native_records']<850_000_000
    assert sha(PUB/'_config.yml')==config['config_sha256']
    assert config['helper']=={'file':CONFIG_HELPER,'sha256':CONFIG_HELPER_SHA}
    assert sha(safe(CONFIG_HELPER))==CONFIG_HELPER_SHA
    progress=read('book/coverage/progress.json')
    assert progress['verified_checkpoint']['proof_files']==1156 and progress['verified_checkpoint']['theorems']==9369
    assert progress['verified_checkpoint']['coverage_complete'] is False
    assert progress['publication_status']=='checkpoint25_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
    assert progress['live_delivery_status']=='checkpoint25_awaiting_actual_pages_and_live_checks'
    assert progress['current_documented_material_corrections']==52
    assert 'awaits an actual GitHub Pages build' in safe('reports/full-coverage/README.md').read_text()
    extra={SELF,PEER,'book/coverage/checks/root_stage_publication25_v1.py','book/coverage/checks/root_stage_publication25_v2.py',ledger_name,CONFIG_HELPER,CONFIG_CODE_PEER,CONFIG_OUTPUT_PEER,ROOT_OUTPUT,MODULE_OUTPUT,
      'book/coverage/progress.json','reports/full-coverage/README.md',
      'book/coverage/checks/root_prepare_checkpoint25_documentation_v1.py',
      'book/coverage/checks/future25-core/checkpoint25-documentation-independent-applied-review-v1.json',
      config_name,'reports/full-coverage/pages25-config-previous-original-v1.yml',
      'reports/full-coverage/pages25-config-previous-original-v1.json',
      'reports/full-coverage/progress-checkpoint25-before-preparation-original-v1.json',
      'reports/full-coverage/README-checkpoint25-before-preparation-original-v1.md',
      'reports/full-coverage/progress-checkpoint25-preparation-update-v1.json',
      'reports/full-coverage/publication-prepared-25-files.json'}
    stems=['static-checkpoint25-execution-v1','prepare-owner25-binding-request-execution-v1',
      'prepare-owner25-bindings-execution-v1','prepare-owner25-binding-request-execution-v2',
      'prepare-owner25-bindings-execution-v2','prepare-owner25-future-code-authorization-execution-v1',
      'owner25-integration-dry-execution-v2','owner25-integration-apply-execution-v1',
      'root-source52-final-owner-integration25-execution-v1','prepare-owner25-interface-request-execution-v1',
      'prepare-owner25-live-interfaces-execution-v1','prepare-owner25-selection-plan-execution-v1',
      'close-owner25-selection-plan-execution-v1','prepare-checkpoint25-selection-execution-v1',
      'root-independent-selection25-output-execution-v1','freeze-checkpoint25-execution-v1',
      'cache-checkpoint25-execution-v1','verify-checkpoint25-execution-v1','export-checkpoint25-execution-v1',
      'export-checkpoint25-output-integrity-execution-v1','frozen-ledger-checkpoint25-execution-v1',
      'prepare-checkpoint25-documentation-execution-v1','prepare-publication25-execution-v1',
      'publication25-ledger-check-execution-v1','pages25-config-execution-v1']
    closed={}
    for stem in stems:
        n='reports/full-coverage/'+stem+'.json';d,log=actual(n)
        extra.update([n,log]);closed[n]=sha(safe(n));closed[log]=sha(safe(log))
    failed_name='reports/full-coverage/owner25-integration-dry-execution-v1.json'
    failed,log=actual(failed_name,1);extra.update([failed_name,log])
    closed[failed_name]=sha(safe(failed_name));closed[log]=sha(safe(log))
    for n in [PEER,CONFIG_CODE_PEER,CONFIG_OUTPUT_PEER,ROOT_OUTPUT,MODULE_OUTPUT,
       'book/coverage/checks/future25-core/checkpoint25-documentation-independent-applied-review-v1.json']:
        peer=peer_evidence(n,extra)
        if n==PEER:assert peer['helper_sha256']==sha(Path(__file__))
        if n==CONFIG_CODE_PEER:assert peer['helper_sha256']==CONFIG_HELPER_SHA
        if n==CONFIG_OUTPUT_PEER:
            assert peer['config_sha256']==config['config_sha256'] and peer['excluded_count']==97
            assert peer['selected_sources']==1156 and peer['public_theorems']==9369
        if n in {ROOT_OUTPUT,MODULE_OUTPUT}:assert peer['selection']=={'file':selection_name,'sha256':sha(safe(selection_name))}
        if n==ROOT_OUTPUT:
            assert peer['status']=='passed_independent_root_actual_selection25_output_review'
            assert (peer['selected_proof_sources'],peer['public_theorems'],peer['new_sources'])==(1156,9369,12)
            checker=peer['actual_checker'];assert sha(safe(checker['file']))==checker['sha256'];extra.add(checker['file'])
    expected={}
    for n in extra:
        p=safe(n);assert p.is_file() and not p.is_symlink();expected[n]=sha(p)
    paths.update(extra);paths.update(['_config.yml',REPORT])
    assert not any(n.startswith('book/coverage/checks/future26') for n in extra)
    assert dirty()<=paths and staged()<=paths,sorted(dirty()-paths)
    record={'status':'passed_explicit_audited_checkpoint25_publication_whitelist_ready_to_stage',
      'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(Path(__file__)),
      'selection_sha256':sha(safe(selection_name)),'manifest_sha256':sha(safe(manifest_name)),
      'sources':1156,'public_theorems':9369,'new_sources':12,'source52_assets_sha256':assets,
      'config_sha256':config['config_sha256'],'staged_paths':sorted(paths),
      'additional_closed_paths_sha256':expected,'closed_actual_execution_evidence_sha256':closed,
      'changed_paths_before_explicit_copy':sorted(dirty()),'coverage_complete':False,
      'publication_still_awaits_actual_commit_push_pages_and_live_checks':True,
      'historical_frozen_archive_scope':'All exact frozen inputs remain archival evidence. No unselected future26 proof or live owner promotion is added as approved25 coverage.'}
    # Account exactly for current included files, every explicit replacement/addition,
    # and the serialized new native record before any publication copy.
    exclusions=config['exclusions']
    assert isinstance(exclusions,list) and len(exclusions)==len(set(exclusions))==97
    assert all(isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
       and not any(c in n for c in ('\0','\n','\r','*','?','[','{')) for n in exclusions)
    kept=lambda n:not any(n==e or n.startswith(e+'/') for e in exclusions)
    included_now=sum(p.stat().st_size for p in PUB.rglob('*')
       if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
    assert included_now>=0
    replacements=sum(safe(n).stat().st_size-(target(n).stat().st_size if target(n).is_file() else 0)
       for n in expected if kept(n))
    record['included_website_bytes_before_explicit_copy']=included_now
    record['included_closed_replacement_byte_delta']=replacements
    record_bytes=(json.dumps(record,indent=2)+'\n').encode()
    prospective=included_now+replacements+(len(record_bytes) if kept(REPORT) else 0)
    assert 0<=prospective<850_000_000,prospective
    for n,digest in expected.items():
        p=target(n);p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(n),p)
        assert sha(safe(n))==sha(p)==digest,n
    for n in paths:assert n=='_config.yml' or safe(n)
    assert all(target(n).is_file() for n in paths if n!=REPORT)
    with safe(REPORT).open('xb') as f:f.write(record_bytes)
    shutil.copyfile(safe(REPORT),target(REPORT))
    assert dirty()<=paths and staged()<=paths
    payload=''.join(n+'\0' for n in sorted(paths)).encode()
    subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
    assert staged() and staged()<=paths
    for n,digest in expected.items():assert sha(target(n))==digest,n
    assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
    print(json.dumps({'status':'passed_explicit_staging','whitelist':len(paths),'actual_staged_paths':len(staged()),
      'sources':1156,'theorems':9369,'coverage_complete':False}))

if __name__=='__main__':main()
