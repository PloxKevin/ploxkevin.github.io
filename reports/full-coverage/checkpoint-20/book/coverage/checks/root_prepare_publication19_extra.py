"""Copy an explicit list of actual checkpoint19 execution evidence after freezing."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
PUBLICATION = ROOT / 'reports/book/publication-repo'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):
    return json.loads(path.read_text())

assert read(REPORTS / 'prepare-publication19-execution.json')['actual_exit_code'] == 0
assert read(REPORTS / 'verify-checkpoint19-resume-execution.json')['actual_exit_code'] == 0
assert read(REPORTS / 'lean-checkpoint-19/verification-original.json')['status'] == 'passed'
assert read(REPORTS / 'parallel-kernel19-wrapper.json')['actual_exit_code'] == 0
names = set(read(REPORTS / 'checkpoint19-extra-publication-paths-draft.json'))
for name in (
    'freeze-checkpoint19-execution.json', 'freeze-checkpoint19-execution.log',
    'verify-checkpoint19-execution.json', 'verify-checkpoint19-execution.log',
    'verify-checkpoint19-resume-execution.json', 'verify-checkpoint19-resume-execution.log',
    'parallel-kernel19-execution.json', 'parallel-kernel19-execution.log',
    'parallel-kernel19-wrapper.json', 'serial-kernel19-interruption.json',
    'serial-kernel19-preserved-evidence.json', 'checkpoint19-cache-preparation.json',
    'prepare-publication19-execution.json', 'prepare-publication19-execution.log'):
    names.add('reports/full-coverage/' + name)
for directory in (
    REPORTS / 'checkpoint-19/reports/lean-verification-serial-interrupted',
    REPORTS / 'checkpoint-19/reports/lean-verification/kernel-parallel19',
    ROOT / 'book/coverage/checks/root-future19-peer-confirmations'):
    for path in directory.rglob('*'):
        if path.is_file():
            assert path.suffix in {'.json', '.log', '.txt', '.py'}, path
            names.add(str(path.relative_to(ROOT)))
for name in ('book/coverage/checks/root_parallel_kernel19.py', 'book/coverage/checks/root_prepare_publication19_extra.py'):
    names.add(name)
paths = []
for name in sorted(names):
    source = ROOT / name
    assert source.is_file() and not source.is_symlink(), name
    assert source.stat().st_size < 100_000_000, name
    target = PUBLICATION / name
    target.parent.mkdir(parents=True, exist_ok=True)
    expected = sha(source)
    if target.exists():
        assert sha(target) == expected, ('different existing extra evidence', name)
    else:
        shutil.copyfile(source, target)
    assert sha(target) == sha(source) == expected
    paths.append(dict(path=name, sha256=expected, bytes=source.stat().st_size))
output = REPORTS / 'publication-extra19-files.json'
assert not output.exists()
output.write_text(json.dumps(dict(status='actual_postfreeze_execution_evidence_copied_exactly', prepared_at_utc=datetime.now(timezone.utc).isoformat(), paths=paths, scope='Historical failures, actual build/kernel/resume commands, independent mechanical peers and original browser artifacts; no future20 proof or source47 publication.'), indent=2) + '\n')
target = PUBLICATION / output.relative_to(ROOT)
shutil.copyfile(output, target)
base = read(REPORTS / 'publication-prepared-19-files.json')
whitelist = sorted(set(base) | names | {str(output.relative_to(ROOT)), 'book/coverage/progress.json'})
final = REPORTS / 'publication-checkpoint19-staging-whitelist.json'
assert not final.exists()
final.write_text(json.dumps(whitelist, indent=2) + '\n')
print(json.dumps(dict(status='passed', extra_paths=len(paths), total_staging_paths=len(whitelist), max_extra_bytes=max(p['bytes'] for p in paths), whitelist=str(final.relative_to(ROOT)))))
