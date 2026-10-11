"""Verify exact frozen21 publication bytes and force only an explicit whitelist."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
SNAPSHOT=REPORTS/'checkpoint-21'
PUBLICATION=ROOT/'reports/book/publication-repo'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def copy(name):
    source=ROOT/name;target=PUBLICATION/name
    assert source.is_file() and not source.is_symlink() and source.stat().st_size<100_000_000,name
    target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
    assert sha(source)==sha(target),name
    return sha(source)
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
manifest=read(REPORTS/'checkpoint-21-manifest.json')
audit=read(REPORTS/'lean-checkpoint-21/verification-original.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert audit['status']=='passed' and audit['proof_file_count']==1089 and audit['theorem_count']>=8821
assert all(c['exit_code']==0 for c in audit['checks'])
for name in ('freeze-checkpoint21-execution-v1','cache-checkpoint21-execution-v1','verify-checkpoint21-execution-v1','export-checkpoint21-execution-v1','prepare-publication21-execution-v1'):
    assert read(REPORTS/(name+'.json'))['actual_exit_code']==0,name
baseline=read(REPORTS/'checkpoint-20-selection.json')
for name,row in baseline['proof_files'].items():
    assert manifest['proof_files'][name]['sha256']==row['sha256']==sha(SNAPSHOT/name),name
names=set(read(REPORTS/'publication-prepared-21-files.json'))
extras={'book/coverage/checks/root_prepare_and_stage_publication21_v2.py','book/coverage/checks/publication21-helper-independent-applied-review-v2.json','book/coverage/checks/pages21-config-independent-foundations-review-v1.json','book/coverage/checks/future21-core/modules-checkpoint21-actual-selection-content-map-independent-confirmation-v1.json'}
for name in ('prepare-checkpoint21-selection-execution-v1','prepare-checkpoint21-selection-execution-v2','freeze-checkpoint21-execution-v1','cache-checkpoint21-execution-v1','verify-checkpoint21-execution-v1','export-checkpoint21-execution-v1','prepare-publication21-execution-v1','browser-source48-21-v1-execution','frozen-ledger-checkpoint21-execution-v1'):
    extras.update('reports/full-coverage/'+name+ext for ext in ('.json','.log'))
extras.update('reports/full-coverage/'+name for name in ('checkpoint21-cache-preparation.json','browser-source48-21-v1.json','browser-source48-21-v1-inputs.json','publication-prepared-21-files.json'))
for directory in ('browser-artifacts-source48-21-v1','lean-checkpoint-21'):
    extras.update(str(p.relative_to(ROOT)) for p in (REPORTS/directory).rglob('*') if p.is_file())
extras.update(str(p.relative_to(ROOT)) for p in (ROOT/'book/coverage/checks/future21-core').glob('modules-checkpoint21-production-output-*'))
extras.update(str(p.relative_to(ROOT)) for p in (ROOT/'book/coverage/checks').glob('root_capture_chow21*.mjs'))
extras.update(str(p.relative_to(ROOT)) for p in REPORTS.glob('chow21-*.json'))
extras.update(str(p.relative_to(ROOT)) for p in REPORTS.glob('chow21-*.log'))
extras.update({'book/coverage/checks/root_prepare_pages21_config_v1.py','reports/full-coverage/pages21-config-preparation-v1.json','reports/full-coverage/pages21-config-previous-original-v1.yml','reports/full-coverage/pages21-config-execution-v1.json','reports/full-coverage/pages21-config-execution-v1.log','reports/full-coverage/publication-checks/ledger-checkpoint-21.json'})
extra_hashes={name:copy(name) for name in sorted(extras)}
config_peer=read(ROOT/'book/coverage/checks/pages21-config-independent-foundations-review-v1.json')
assert 'passed' in config_peer['status']
assert config_peer['config_sha256']==sha(PUBLICATION/'_config.yml')
excluded=[line[4:] for line in (PUBLICATION/'_config.yml').read_text().splitlines() if line.startswith('  - ')]
assert len(set(excluded))==len(excluded) and 'reports/full-coverage/checkpoint-21' in excluded
included=sum(p.stat().st_size for p in PUBLICATION.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUBLICATION).parts and not any(p.relative_to(PUBLICATION).as_posix()==x or p.relative_to(PUBLICATION).as_posix().startswith(x+'/') for x in excluded))
assert included<900_000_000
names.add('_config.yml')
extra_path=REPORTS/'publication-extra21-files.json';assert not extra_path.exists()
extra_path.write_text(json.dumps(dict(status='actual_postfreeze_execution_evidence_copied_exactly',created_at_utc=datetime.now(timezone.utc).isoformat(),paths_sha256=extra_hashes,coverage_complete=False),indent=2)+'\n')
extra_name=str(extra_path.relative_to(ROOT));copy(extra_name)
names.update(extras);names.update((extra_name,'book/coverage/progress.json'))
expected=dict(manifest['frozen_inputs_sha256'])
for name,digest in list(expected.items()):
    assert sha(SNAPSHOT/name)==digest,name
    if name.startswith('reports/full-coverage/source-history/'):
        expected['reports/full-coverage/checkpoint-21/'+name]=digest
expected.pop('book/coverage/progress.json')
progress=read(PUBLICATION/'book/coverage/progress.json');original=read(SNAPSHOT/'book/coverage/progress.json')
changed={'verified_checkpoint','current_frozen_audit','publication_status','current_documented_material_corrections','inventory_sha256','current_published_ledger_candidate'}
assert {k:v for k,v in progress.items() if k not in changed}=={k:v for k,v in original.items() if k not in changed}
assert progress['verified_checkpoint']['proof_files']==1089 and progress['verified_checkpoint']['theorems']==audit['theorem_count']
assert progress['verified_checkpoint']['status']=='passed' and progress['verified_checkpoint']['coverage_complete'] is False
assert progress['current_documented_material_corrections']==48
assert progress['inventory_sha256']==sha(SNAPSHOT/'book/coverage/inventory.json')
for name in sorted(names):
    target=PUBLICATION/name;assert target.is_file() and not target.is_symlink(),name
    if name in expected: assert sha(target)==expected[name],name
    elif name in {'book/coverage/progress.json','_config.yml'}: expected[name]=sha(target)
    else:
        assert sha(target)==sha(ROOT/name),name
        expected[name]=sha(target)
for argv in (['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],['git','ls-files','--others','--exclude-standard','-z']):
    dirty=subprocess.run(argv,cwd=PUBLICATION,capture_output=True,check=True).stdout
    assert {x.decode() for x in dirty.split(b'\0') if x}<=names
record=REPORTS/'publication-checkpoint21-prestage-integrity.json';assert not record.exists()
record.write_text(json.dumps(dict(status='passed_exact_frozen_and_explicit_actual_evidence',checked_at_utc=datetime.now(timezone.utc).isoformat(),snapshot=str(SNAPSHOT.relative_to(ROOT)),manifest_sha256=sha(REPORTS/'checkpoint-21-manifest.json'),selection_sha256=sha(REPORTS/'checkpoint-21-selection.json'),baseline20_proofs_byte_exact=1068,published_file_budget_bytes=included,coverage_complete=False,paths_sha256=expected),indent=2)+'\n')
record_name=str(record.relative_to(ROOT));copy(record_name);names.add(record_name)
whitelist=REPORTS/'publication-checkpoint21-staging-whitelist.json';assert not whitelist.exists()
whitelist.write_text(json.dumps(sorted(names),indent=2)+'\n')
pathspec=REPORTS/'publication-checkpoint21-stage-pathspec.nul';assert not pathspec.exists()
pathspec.write_bytes(b''.join(name.encode()+b'\0' for name in sorted(names)))
command=['git','add','-f','--pathspec-from-file='+str(pathspec),'--pathspec-file-nul']
r=subprocess.run(command,cwd=PUBLICATION,capture_output=True)
staged=subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUBLICATION,capture_output=True,check=True)
staged_names={x.decode() for x in staged.stdout.split(b'\0') if x}
result=REPORTS/'publication-checkpoint21-staging-execution.json';assert not result.exists()
result.write_text(json.dumps(dict(status='passed_explicit_whitelist_staged' if r.returncode==0 else 'failed',actual_exit_code=r.returncode,actual_command=command,actual_workdir=str(PUBLICATION),started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-tick,command_stdout=r.stdout.decode(),command_stderr=r.stderr.decode(),checked_paths=len(names),staged_paths=len(staged_names),integrity_record=record_name,integrity_record_sha256=sha(record)),indent=2)+'\n')
assert r.returncode==0 and staged_names and staged_names<=names
print(json.dumps(dict(status='passed',checked_paths=len(names),staged_paths=len(staged_names),elapsed_seconds=time.monotonic()-tick)))
