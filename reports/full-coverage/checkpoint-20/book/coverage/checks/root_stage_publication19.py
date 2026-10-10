"""Validate every prepared publication byte and stage only the explicit whitelist."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
SNAPSHOT = REPORTS / 'checkpoint-19'
PUBLICATION = ROOT / 'reports/book/publication-repo'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):
    return json.loads(path.read_text())
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
manifest = read(REPORTS / 'checkpoint-19-manifest.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
audit = read(REPORTS / 'lean-checkpoint-19/verification.json')
assert audit['status'] == 'passed' and audit['proof_file_count'] == 1055 and audit['theorem_count'] == 8563
assert all(c['exit_code'] == 0 for c in audit['checks'])
expected = dict(manifest['frozen_inputs_sha256'])
for name, digest in manifest['frozen_inputs_sha256'].items():
    assert sha(SNAPSHOT / name) == digest
    if name.startswith('reports/full-coverage/source-history/'):
        expected['reports/full-coverage/checkpoint-19/' + name] = digest
expected.pop('book/coverage/progress.json')
paths = set(read(REPORTS / 'publication-checkpoint19-staging-whitelist-v2.json'))
for name in sorted(paths):
    path = PUBLICATION / name
    assert path.is_file() and not path.is_symlink(), name
    if name == 'book/coverage/progress.json':
        progress = read(path)
        original = read(SNAPSHOT / name)
        changed = {'verified_checkpoint', 'current_frozen_audit', 'publication_status', 'current_documented_material_corrections', 'inventory_sha256', 'current_published_ledger_candidate'}
        assert {k: v for k, v in progress.items() if k not in changed} == {k: v for k, v in original.items() if k not in changed}
        assert progress['verified_checkpoint']['status'] == 'passed' and not progress['verified_checkpoint']['coverage_complete']
        assert progress['verified_checkpoint']['proof_files'] == 1055 and progress['verified_checkpoint']['theorems'] == 8563
        assert progress['current_documented_material_corrections'] == 44
        assert progress['inventory_sha256'] == sha(SNAPSHOT / 'book/coverage/inventory.json')
        expected[name] = sha(path)
    elif name not in expected:
        source = ROOT / name
        assert source.is_file(), name
        expected[name] = sha(source)
    assert sha(path) == expected[name], name
assert paths == set(expected), (len(paths), len(expected))
assert all('/CompletePolicyFOCOPS' not in name for name in paths)
prior = read(REPORTS / 'checkpoint-18-manifest.json')
for name, metadata in prior['proof_files'].items():
    digest = metadata['sha256'] if isinstance(metadata, dict) else metadata
    assert sha(PUBLICATION / name) == digest
extra = ('reports/full-coverage/prepare-publication19-extra-execution-v1.json', 'reports/full-coverage/prepare-publication19-extra-execution-v1.log', str(Path(__file__).relative_to(ROOT)))
for name in extra:
    source, target = ROOT / name, PUBLICATION / name
    assert source.is_file() and not target.exists()
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert sha(source) == sha(target)
    paths.add(name)
    expected[name] = sha(source)
dirty = subprocess.run(['git', 'diff', '--name-only', '-z'], cwd=PUBLICATION, capture_output=True, check=True).stdout
untracked = subprocess.run(['git', 'ls-files', '--others', '--exclude-standard', '-z'], cwd=PUBLICATION, capture_output=True, check=True).stdout
actual_paths = {x.decode() for x in (dirty + untracked).split(b'\0') if x}
assert actual_paths <= paths, sorted(actual_paths - paths)
assert not subprocess.run(['git', 'diff', '--cached', '--name-only'], cwd=PUBLICATION, capture_output=True, check=True).stdout
record_name = 'reports/full-coverage/publication-checkpoint19-prestage-integrity.json'
record = ROOT / record_name
assert not record.exists()
record.write_text(json.dumps(dict(status='passed_exact_frozen_and_explicit_execution_evidence', checked_at_utc=datetime.now(timezone.utc).isoformat(), snapshot='reports/full-coverage/checkpoint-19', manifest_sha256=sha(REPORTS / 'checkpoint-19-manifest.json'), selection_sha256=sha(REPORTS / 'checkpoint-19-selection.json'), frozen_input_count=len(manifest['frozen_inputs_sha256']), baseline18_proofs_byte_exact=len(prior['proof_files']), coverage_complete=False, paths_sha256=expected), indent=2) + '\n')
shutil.copyfile(record, PUBLICATION / record_name)
paths.add(record_name)
pathspec = REPORTS / 'publication-checkpoint19-stage-pathspec.nul'
assert not pathspec.exists()
pathspec.write_bytes(b''.join(name.encode() + b'\0' for name in sorted(paths)))
command = ['git', 'add', '--pathspec-from-file=' + str(pathspec), '--pathspec-file-nul']
actual = subprocess.run(command, cwd=PUBLICATION, capture_output=True)
staged = subprocess.run(['git', 'diff', '--cached', '--name-only', '-z'], cwd=PUBLICATION, capture_output=True, check=True)
staged_names = {x.decode() for x in staged.stdout.split(b'\0') if x}
assert actual.returncode == 0, actual.stderr.decode()
assert staged_names <= paths and staged_names, sorted(staged_names - paths)
result = REPORTS / 'publication-checkpoint19-staging-execution.json'
assert not result.exists()
result.write_text(json.dumps(dict(status='passed_explicit_whitelist_staged', actual_exit_code=actual.returncode, actual_command=command, actual_workdir=str(PUBLICATION), started_at_utc=started, finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-tick, command_stdout=actual.stdout.decode(), command_stderr=actual.stderr.decode(), checked_paths=len(paths), staged_paths=len(staged_names), integrity_record=record_name, integrity_record_sha256=sha(record)), indent=2) + '\n')
print(json.dumps(dict(status='passed', checked_paths=len(paths), staged_paths=len(staged_names), elapsed_seconds=time.monotonic()-tick)))
