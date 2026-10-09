#!/usr/bin/env python3
"""Export an actually passed frozen audit without changing execution provenance."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--snapshot', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
snapshot = (ROOT / args.snapshot).resolve()
output = (ROOT / args.output).resolve()
if not output.is_relative_to(ROOT / 'reports/full-coverage') or output.exists():
    raise ValueError('Use a new output directory within reports/full-coverage.')
original_dir = snapshot / 'reports/lean-verification'
report_path = original_dir / 'verification.json'
report = json.loads(report_path.read_text())
if report.get('status') != 'passed' or any(c['exit_code'] != 0 for c in report['checks']):
    raise ValueError('No actual passing aggregate audit.')
manifest_path = snapshot.parent / (snapshot.name + '-manifest.json')
manifest = json.loads(manifest_path.read_text())
if set(report['proof_sha256']) != set(manifest['proof_files']):
    raise ValueError('Audited proof selection differs from the frozen selection.')
for field in ['source_sha256', 'proof_sha256', 'project_sha256']:
    for name, expected in report[field].items():
        if sha(snapshot / name) != expected:
            raise ValueError('Frozen audited input changed: ' + name)
output.mkdir()
for path in original_dir.iterdir():
    if path.is_file():
        shutil.copyfile(path, output / path.name)
(output / 'verification.json').rename(output / 'verification-original.json')
old_prefix = 'reports/lean-verification/'
new_prefix = str(output.relative_to(ROOT)) + '/'


def relocate(value):
    if isinstance(value, list):
        return [relocate(item) for item in value]
    if isinstance(value, dict):
        return {key: (item.replace(old_prefix, new_prefix, 1)
                      if key in {'output_file', 'report'} and isinstance(item, str)
                      and item.startswith(old_prefix) else relocate(item))
                for key, item in value.items()}
    return value


relocated = relocate(report)
relocated['audit_origin'] = {
    'original_report': str((output / 'verification-original.json').relative_to(ROOT)),
    'original_report_sha256': sha(output / 'verification-original.json'),
    'actual_workdir': str(snapshot / 'verification/lean'),
    'relocation': 'Only report/output locations relocated; source hashes and original execution provenance retained.'}
(output / 'verification.json').write_text(json.dumps(relocated, indent=2) + '\n')
progress = output / 'kernel-progress.json'
if progress.exists():
    progress.write_text(json.dumps(relocate(json.loads(progress.read_text())), indent=2) + '\n')
manifest['status'] = 'formal_verification_passed_partial_coverage'
manifest['successful_verification'] = {
    'proof_file_count': report['proof_file_count'], 'theorem_count': report['theorem_count'],
    'all_check_exit_codes': 0,
    'report': str((output / 'verification-original.json').relative_to(ROOT)),
    'report_sha256': sha(output / 'verification-original.json')}
manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
ledger_files = {str(p.relative_to(snapshot)): sha(p)
                for p in (snapshot / 'book/coverage').rglob('*') if p.is_file()}
ledger_manifest = {
    'status': 'ledger_integrity_passed_mathematical_coverage_incomplete',
    'files': ledger_files, 'coverage_complete': False,
    'scope': 'Exact source-frozen partial ledgers; no unfinished claim is promoted by the formal audit.'}
(snapshot.parent / (snapshot.name + '-ledger-manifest.json')).write_text(
    json.dumps(ledger_manifest, indent=2) + '\n')
print(f"Exported {report['theorem_count']} theorems in {report['proof_file_count']} files.")
