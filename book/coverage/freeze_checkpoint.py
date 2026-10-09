#!/usr/bin/env python3
"""Freeze an explicitly selected, source-fingerprinted partial Lean checkpoint.

This prepares inputs. A checkpoint is verified only after verify.py finishes.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--selection', type=Path, required=True)
parser.add_argument('--snapshot', type=Path, required=True)
args = parser.parse_args()
selection_path = (ROOT / args.selection).resolve()
snapshot = (ROOT / args.snapshot).resolve()
if not snapshot.is_relative_to(ROOT / 'reports/full-coverage') or snapshot.exists():
    raise ValueError('Use a new snapshot directory inside reports/full-coverage.')
selection = json.loads(selection_path.read_text())
selected = selection['proof_files']
declarations = set()
for name, record in selected.items():
    source = ROOT / name
    if sha(source) != record['sha256']:
        raise ValueError('Selected source changed: ' + name)
    text = source.read_text()
    namespaces = re.findall(r'^namespace\s+(\S+)', text, re.M)
    if len(namespaces) != 1:
        raise ValueError('Expected one namespace: ' + name)
    declarations.update(namespaces[0] + '.' + n for n in re.findall(
        r'^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([^\s({:]+)', text, re.M))
    for dep in re.findall(r'^import\s+(SafeLearning\.\S+)', text, re.M):
        dependency = 'verification/lean/' + dep.replace('.', '/') + '.lean'
        if dependency not in selected:
            raise ValueError('Missing selected dependency: ' + dependency)
    for evidence, expected in record.get('evidence_sha256', {}).items():
        if sha(ROOT / evidence) != expected:
            raise ValueError('Selected evidence changed: ' + evidence)

files = list(selected)
files += [str(p.relative_to(ROOT)) for p in (ROOT / 'SafeLearning').iterdir()
          if p.suffix in {'.html', '.css', '.js'}]
files += ['verification/lean/' + name for name in
          ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verify.py']]
files += [str(p.relative_to(ROOT)) for p in (ROOT / 'book/coverage').rglob('*')
          if p.is_file() and p.suffix in {'.py', '.json', '.md', '.log'}
          and '__pycache__' not in p.parts]
files += ['book/inventory_claims.py', 'book/validate.py']
files = sorted(set(files))
initial_hashes = {name: sha(ROOT / name) for name in files}
for name in files:
    target = snapshot / name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / name, target)
    if sha(target) != initial_hashes[name]:
        raise ValueError('Input changed while copying: ' + name)

excluded_metadata = {}
for domain in ['foundations', 'applied', 'modules', 'core']:
    path = snapshot / f'book/coverage/{domain}.json'
    ledger = json.loads(path.read_text())
    for claim in ledger.get('material_claims', []) + [c for e in ledger['exercises'] for c in e['claims']]:
        missing = set(claim['lean_declarations']) - declarations
        if missing:
            raise ValueError(f'{domain}: selected files omit claim references {missing}')
    listed = ledger.get('proof_files', {})
    excluded_metadata[domain] = sorted(set(listed) - set(selected))
    if isinstance(listed, list):
        ledger['proof_files'] = [name for name in listed if name in selected]
    else:
        ledger['proof_files'] = {name: value for name, value in listed.items() if name in selected}
    if 'proof_sha256' in ledger:
        ledger['proof_sha256'] = {name: value for name, value in ledger['proof_sha256'].items()
                                  if name in selected}
    if excluded_metadata[domain]:
        path.write_text(json.dumps(ledger, indent=2) + '\n')

project = snapshot / 'verification/lean'
aggregator = '\n'.join('import SafeLearning.' + Path(name).stem for name in sorted(selected)) + '\n'
(project / 'SafeLearning.lean').write_text(aggregator)
(project / '.lake').mkdir()
(project / '.lake/packages').symlink_to(ROOT / 'verification/lean/.lake/packages', target_is_directory=True)
if initial_hashes != {name: sha(ROOT / name) for name in files}:
    raise ValueError('Working inputs changed during freezing; discard this snapshot and retry.')
frozen = {str(p.relative_to(snapshot)): sha(p) for p in snapshot.rglob('*')
          if p.is_file() and '.lake' not in p.relative_to(snapshot).parts}
manifest = {
    'status': 'frozen_inputs_not_yet_aggregate_verified',
    'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'snapshot': str(snapshot.relative_to(ROOT)),
    'selection': str(selection_path.relative_to(ROOT)),
    'selection_sha256': sha(selection_path),
    'proof_files': selected,
    'working_inputs_sha256': initial_hashes,
    'frozen_inputs_sha256': frozen,
    'excluded_unreferenced_ledger_metadata': excluded_metadata,
    'excluded_working_proof_files': sorted(str(p.relative_to(ROOT)) for p in
        (ROOT / 'verification/lean/SafeLearning').glob('*.lean')
        if str(p.relative_to(ROOT)) not in selected),
    'coverage_complete': False,
    'limits': ['Explicit partial proof selection; all book exercises and material units remain inventoried.',
               'Actual aggregate compilation, kernel replay and axiom audit are still required.']
}
(snapshot.parent / (snapshot.name + '-manifest.json')).write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Frozen {len(selected)} proof files and {len(frozen)} input files at {snapshot}.')
