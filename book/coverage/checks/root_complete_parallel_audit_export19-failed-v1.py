"""Preserve nested actual kernel logs required by the relocated checkpoint19 audit."""
from pathlib import Path
import hashlib
import json
import shutil
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
SNAPSHOT = REPORTS / 'checkpoint-19'
OUT = REPORTS / 'lean-checkpoint-19'
PUBLICATION = ROOT / 'reports/book/publication-repo'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
original = OUT / 'verification-original.json'
relocated = OUT / 'verification.json'
before = {str(path.relative_to(ROOT)): sha(path) for path in (original, relocated)}
a, b = json.loads(original.read_text()), json.loads(relocated.read_text())
assert a['status'] == b['status'] == 'passed'
assert len(a['checks']) == len(b['checks'])
copied = []
for old, new in zip(a['checks'], b['checks']):
    if old['output_file'].startswith('reports/lean-verification/kernel-parallel19/'):
        source = SNAPSHOT / old['output_file']
        destination = ROOT / new['output_file']
        assert destination.is_relative_to(OUT)
        for raw in (source, source.with_suffix('.json')):
            assert raw.is_file()
            target = destination.with_suffix(raw.suffix)
            assert not target.exists(), target
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(raw, target)
            assert sha(raw) == sha(target)
            copied.append(dict(path=str(target.relative_to(ROOT)), sha256=sha(target), original=str(raw.relative_to(ROOT))))
    log = ROOT / new['output_file']
    assert log.is_file(), new['output_file']
    if 'log_sha256' in new:
        assert sha(log) == new['log_sha256'], new['output_file']
assert len(copied) == 928
assert before == {str(path.relative_to(ROOT)): sha(path) for path in (original, relocated)}
for row in copied:
    source = ROOT / row['path']
    target = PUBLICATION / row['path']
    assert not target.exists()
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert sha(target) == row['sha256']
record = REPORTS / 'nested-kernel19-export-completion.json'
assert not record.exists()
record.write_text(json.dumps(dict(status='passed_all_current_audit_output_paths_preserved_exactly', completed_at_utc=datetime.now(timezone.utc).isoformat(), prior_flat_export_limitation='The original exporter copied top-level files only. Parallel kernel logs reside in a nested directory; this completion copies their exact original bytes to the existing report relocation paths.', original_audit_and_relocated_report_sha256_unchanged=before, files=copied, checked_command_output_paths=len(b['checks'])), indent=2) + '\n')
shutil.copyfile(record, PUBLICATION / record.relative_to(ROOT))
helper = Path(__file__)
shutil.copyfile(helper, PUBLICATION / helper.relative_to(ROOT))
whitelist = REPORTS / 'publication-checkpoint19-staging-whitelist.json'
paths = set(json.loads(whitelist.read_text()))
paths.update(row['path'] for row in copied)
paths.update((str(record.relative_to(ROOT)), str(helper.relative_to(ROOT))))
final = REPORTS / 'publication-checkpoint19-staging-whitelist-v2.json'
assert not final.exists()
final.write_text(json.dumps(sorted(paths), indent=2) + '\n')
print(json.dumps(dict(status='passed', exact_nested_files=len(copied), all_command_outputs=len(b['checks']), staging_paths=len(paths))))
