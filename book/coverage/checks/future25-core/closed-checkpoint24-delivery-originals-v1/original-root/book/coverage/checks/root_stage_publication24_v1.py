"""Stage only the explicitly audited24 inputs and closed delivery preparation."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
REPORT='reports/full-coverage/publication24-prestage-v1.json'
def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in ['\0','\n','\r']) and (ROOT/n).resolve().is_relative_to(ROOT.resolve())
    return ROOT/n
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def actual(n,exit_code=0):
    d=read(n);codes=[d[k] for k in ['actual_exit_code','exit_code'] if k in d]
    assert codes and all(type(c) is int and c==exit_code for c in codes),n
    assert sha(safe(d['log']))==d['log_sha256']
    return d
assert not safe(REPORT).exists()
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
selection=read('reports/full-coverage/checkpoint-24-selection.json')
audit=read('reports/full-coverage/lean-checkpoint-24/verification-original.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert manifest['selection_sha256']==sha(safe('reports/full-coverage/checkpoint-24-selection.json'))
assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1144
assert selection['new_file_count']==13 and audit['status']=='passed' and audit['theorem_count']==9279
assert all(c['exit_code']==0 for c in audit['checks']) and selection['coverage_complete'] is False
assert audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}
assert manifest['successful_verification']['report_sha256']==sha(safe('reports/full-coverage/lean-checkpoint-24/verification-original.json'))
config=read('reports/full-coverage/pages24-config-preparation-v1.json')
assert sha(PUB/'_config.yml')==config['config_sha256'] and config['prospective_included_website_bytes']<900_000_000
assert config['excluded_count']==70
config_code_peer=read('book/coverage/checks/pages24-config-helper-independent-foundations-review-v1.json')
assert 'passed' in config_code_peer['status'] and config_code_peer.get('errors',[])==[]
assert config_code_peer['helper_sha256']==sha(safe('book/coverage/checks/root_prepare_pages24_config_v1.py'))
ledger_name='reports/full-coverage/publication-checks/ledger-checkpoint-24.json'
ledger=read(ledger_name)
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['inventory_sha256']==sha(safe('book/coverage/inventory.json'))=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for row in ledger['domains']:
    assert row['ledger_sha256']==sha(PUB/('book/coverage/'+row['domain']+'.json'))
paths=set(read('reports/full-coverage/publication-prepared-24-files.json'))
assert set(manifest['frozen_inputs_sha256'])<=paths
progress=read('book/coverage/progress.json')
assert progress['verified_checkpoint']['proof_files']==1144 and progress['verified_checkpoint']['theorems']==9279
assert progress['publication_status']=='checkpoint24_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
assert progress['live_delivery_status']=='checkpoint24_awaiting_actual_pages_and_live_checks'
assert progress['current_documented_material_corrections']==52
assert 'awaits an actual GitHub Pages build' in safe('reports/full-coverage/README.md').read_text()
mutable={'book/coverage/progress.json'}
snapshot=safe(manifest['snapshot'])
for n,digest in manifest['frozen_inputs_sha256'].items():
    assert sha(snapshot/n)==digest
    assert (PUB/n).is_file()
    if n not in mutable:assert sha(PUB/n)==digest,n
for n,row in manifest['proof_files'].items():assert sha(safe(n))==row['sha256']==sha(PUB/n)
assets={n:d for n,d in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31
for n,d in assets.items():assert sha(safe(n))==sha(PUB/n)==d
stems=['source52-dry-execution-v2','source52-apply-execution-v1','static-checkpoint24-execution-v1',
    'prepare-owner24-bindings-execution-v1','owner24-integration-dry-execution-v1','owner24-integration-apply-execution-v1',
    'owner24-global-integrity-execution-v1','prepare-owner24-interface-request-execution-v1',
    'prepare-owner24-live-interfaces-execution-v1','prepare-owner24-selection-plan-execution-v1',
    'prepare-checkpoint24-selection-execution-v1','checkpoint24-root-independent-output-execution-v1',
    'freeze-checkpoint24-execution-v1','cache-checkpoint24-execution-v1','verify-checkpoint24-execution-v1',
    'export-checkpoint24-execution-v1','export-checkpoint24-output-integrity-execution-v1',
    'frozen-ledger-checkpoint24-execution-v1','prepare-checkpoint24-documentation-execution-v1',
    'prepare-publication24-execution-v1','publication24-ledger-check-execution-v1','pages24-config-execution-v1',
    'browser-source52-24-runner-execution-v1','browser-checkpoint24-binding-execution-v1',
    'source52-corrected-paragraphs24-capture-execution-v2']
extra={ledger_name,'book/coverage/progress.json','reports/full-coverage/README.md',
    'reports/full-coverage/pages24-config-preparation-v1.json','reports/full-coverage/pages24-config-previous-original-v1.yml',
    'reports/full-coverage/progress-checkpoint24-before-preparation-original-v1.json',
    'reports/full-coverage/README-checkpoint24-before-preparation-original-v1.md',
    'reports/full-coverage/progress-checkpoint24-preparation-update-v1.json',
    'reports/full-coverage/publication-prepared-24-files.json',
    str(Path(__file__).relative_to(ROOT)),
    'book/coverage/checks/root_prepare_checkpoint24_documentation_v1.py',
    'book/coverage/checks/root_prepare_checkpoint24_documentation_v2.py',
    'book/coverage/checks/root_prepare_pages24_config_v1.py',
    'book/coverage/checks/pages24-config-helper-independent-foundations-review-v1.json'}
for stem in stems:
    record='reports/full-coverage/'+stem+'.json';actual(record);extra.update([record,record[:-5]+'.log'])
for stem in ['source52-dry-execution-v1','source52-corrected-paragraphs24-capture-execution-v1']:
    record='reports/full-coverage/'+stem+'.json';actual(record,1);extra.update([record,record[:-5]+'.log'])
for folder in ['source52-corrected-paragraphs24-captures-v1','browser-artifacts-24']:
    for p in (ROOT/'reports/full-coverage'/folder).iterdir():
        if p.is_file():extra.add(str(p.relative_to(ROOT)))
extra.add('reports/full-coverage/source52-corrected-paragraphs24-capture-v1.json')
# Closed code/output peers may be named in these explicit publication24 catalogs.
for n in ['book/coverage/checks/future24-core/publication24-stage-independent-review-v1.json',
          'book/coverage/checks/future24-core/pages24-config-independent-output-review-v1.json']:
    peer=read(n);assert 'passed' in peer['status'] and peer.get('errors',[])==[]
    extra.add(n)
    for name,digest in peer['closed_evidence_sha256'].items():
        assert sha(safe(name))==digest;extra.add(name)
stage_peer=read('book/coverage/checks/future24-core/publication24-stage-independent-review-v1.json')
assert stage_peer['helper_sha256']==sha(Path(__file__))
config_peer=read('book/coverage/checks/future24-core/pages24-config-independent-output-review-v1.json')
assert config_peer['config_sha256']==config['config_sha256']
# Exact old/root source bytes are copied only through the frozen whitelist above.
# Explicit additional closed reports and current metadata use their current bytes.
for n in sorted(extra):
    source=safe(n);assert source.is_file() and not source.is_symlink()
    destination=PUB/n;destination.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,destination);assert sha(source)==sha(destination)
    paths.add(n)
paths.add('_config.yml')
paths.add(REPORT)
for n in paths:
    assert n=='_config.yml' or safe(n)
    assert (PUB/n).is_file() or n==REPORT,n
    assert not n.startswith('book/coverage/checks/future25')
allowed_before=set(paths)
status=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=PUB,check=True,capture_output=True).stdout.decode().split('\0')
changed=set()
for entry in filter(None,status):
    assert entry[:2] not in {'R ',' R','C ',' C'} and 'D' not in entry[:2],entry
    changed.add(entry[3:])
assert changed<=allowed_before,sorted(changed-allowed_before)
out={'status':'passed_explicit_audited_checkpoint24_publication_whitelist_ready_to_stage',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'selection_sha256':sha(safe('reports/full-coverage/checkpoint-24-selection.json')),
    'manifest_sha256':sha(safe('reports/full-coverage/checkpoint-24-manifest.json')),
    'helper_sha256':sha(Path(__file__)),'sources':1144,'public_theorems':9279,'source52_assets_sha256':assets,
    'config_sha256':config['config_sha256'],'staged_paths':sorted(paths),'changed_paths':sorted(changed),
    'publication_still_awaits_actual_commit_push_pages_and_live_checks':True,'coverage_complete':False}
with safe(REPORT).open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
shutil.copyfile(safe(REPORT),PUB/REPORT)
payload=''.join(n+'\0' for n in sorted(paths)).encode()
subprocess.run(['git','add','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
staged=subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout.decode().split('\0')
assert {n for n in staged if n}<=paths
print(json.dumps({'status':'passed_explicit_staging','whitelist':len(paths),'changed':len(changed),'sources':1144,'theorems':9279}))
