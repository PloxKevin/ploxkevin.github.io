#!/usr/bin/env python3
"""Copy exact frozen inputs and actual audit evidence to the isolated publication repo.

This prepares an explicit staging whitelist; it does not commit or publish.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('checkpoint', type=int)
args = parser.parse_args()
n = args.checkpoint
reports = ROOT / 'reports/full-coverage'
snapshot = reports / f'checkpoint-{n}'
publication = ROOT / 'reports/book/publication-repo'
manifest = json.loads((reports / f'checkpoint-{n}-manifest.json').read_text())
audit_path = reports / f'lean-checkpoint-{n}/verification.json'
audit = json.loads(audit_path.read_text())
if audit['status'] != 'passed' or manifest['status'] != 'formal_verification_passed_partial_coverage':
    raise ValueError('Actual aggregate/kernel/axiom audit is required before preparation.')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


copied = set()


def copy(source, name):
    target = publication / name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    if sha(source) != sha(target):
        raise ValueError('Copy changed bytes: ' + name)
    copied.add(name)


for name, expected in manifest['frozen_inputs_sha256'].items():
    source = snapshot / name
    if sha(source) != expected:
        raise ValueError('Frozen input changed: ' + name)
    copy(source, name)
    if name.startswith('reports/full-coverage/source-history/'):
        copy(source, f'reports/full-coverage/checkpoint-{n}/' + name)

external = [reports / 'README.md', reports / f'integration-{n}.json',
            reports / f'checkpoint-{n}-manifest.json', reports / f'checkpoint-{n}-selection.json',
            reports / f'checkpoint-{n}-ledger-manifest.json', reports / f'browser-checkpoint-{n}.json',
            reports / f'browser-corrections-{n}-inputs.json', reports / f'browser-corrections-{n}.json',
            reports / f'browser-corrections-{n}.log']
external += sorted((reports / f'lean-checkpoint-{n}').glob('*'))
external += sorted((reports / f'browser-artifacts-{n}').glob('*'))
for source in external:
    if source.is_file():
        copy(source, str(source.relative_to(ROOT)))

progress_path = publication / 'book/coverage/progress.json'
progress = json.loads(progress_path.read_text())
progress['verified_checkpoint'] = {
    'proof_files': len(manifest['proof_files']), 'theorems': audit['theorem_count'],
    'status': 'passed', 'coverage_complete': False,
    'report': str(audit_path.relative_to(ROOT)),
    'actual_audit_workdir': str(snapshot / 'verification/lean')}
progress['current_frozen_audit'] = {
    'snapshot': str(snapshot.relative_to(ROOT)), 'proof_files': len(manifest['proof_files']),
    'status': 'passed_actual_build_kernel_and_axiom_audit'}
progress['publication_status'] = f'prepared_source_exact_checkpoint_{n}_awaiting_delivery'
progress['current_documented_material_corrections'] = len(json.loads(
    (snapshot / 'book/coverage/material-corrections.json').read_text())['corrections'])
progress['inventory_sha256'] = sha(snapshot / 'book/coverage/inventory.json')
progress['current_published_ledger_candidate'] = f'reports/full-coverage/publication-checks/ledger-checkpoint-{n}.json'
progress_path.write_text(json.dumps(progress, indent=2) + '\n')

(reports / f'publication-prepared-{n}-files.json').write_text(json.dumps(sorted(copied), indent=2) + '\n')
print(f'Prepared {len(copied)} exact frozen input/evidence paths; publication progress records actual audit and pending delivery.')
