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
from lean_names import declarations as source_declarations

ROOT = Path(__file__).resolve().parents[2]

# This checkpoint-specific repair admits only four already selected archive bytes.
# Olean archives are historical compiler evidence, never selected proof sources.
CHECKPOINT25_SELECTION = 'reports/full-coverage/checkpoint-25-selection.json'
CHECKPOINT25_SELECTION_SHA256 = '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'
CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS = {'book/coverage/checks/applied-future25/source52/original-independent-canonical-candidate-peer/CompleteAppliedGaussianMixtureCDFNumbers24.olean': 'd5df772f9a1787a6959ad42e13c23a5b36ab7bd0e8a12da39f580a918edea9e5', 'book/coverage/checks/applied-future25/source52/original-independent-canonical-candidate-peer/CompleteAppliedGaussianMixtureLaw24.olean': 'bbae6e327f3a34181f09a4299749a925b6b0f8e678cefe052eb072ec33be6a48', 'book/coverage/checks/applied-future25/source52/original-independent-canonical-candidate-peer/CompleteAppliedGaussianSmallTail24.olean': 'bff986ff9bfa79de97efb40e3d819e52e42f3239d269659e86b9ade0d3d11ac3', 'book/coverage/checks/future25-core/closed-checkpoint24-delivery-originals-v1/original-root/reports/full-coverage/pages24-config-previous-original-v1.yml': '278d5b40954704026471c5589d8869af8b9a5e5111c5cb070a28e35876ab09e3'}


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
if (str(args.selection) != CHECKPOINT25_SELECTION
        or sha(selection_path) != CHECKPOINT25_SELECTION_SHA256):
    raise ValueError('Use the exact reviewed checkpoint25 selection bytes.')
selection = json.loads(selection_path.read_text())
for name, digest in CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS.items():
    if selection.get('extra_frozen_inputs', {}).get(name, {}).get('sha256') != digest:
        raise ValueError('Checkpoint25 exact archive exception differs: ' + name)
selected = selection['proof_files']
declarations = set()
selected_evidence_inputs = []
for name, record in selected.items():
    source = ROOT / name
    if sha(source) != record['sha256']:
        raise ValueError('Selected source changed: ' + name)
    text = source.read_text()
    declarations.update(record['name'] for record in source_declarations(text))
    for dep in re.findall(r'^import\s+(SafeLearning\.\S+)', text, re.M):
        dependency = 'verification/lean/' + dep.replace('.', '/') + '.lean'
        if dependency not in selected:
            raise ValueError('Missing selected dependency: ' + dependency)
    for evidence, expected in record.get('evidence_sha256', {}).items():
        if (Path(evidence).is_absolute() or '..' in Path(evidence).parts
                or str(Path(evidence)) != evidence
                or not (ROOT / evidence).resolve().is_relative_to(ROOT.resolve())):
            raise ValueError('Selected evidence escapes the checkout: ' + evidence)
        if sha(ROOT / evidence) != expected:
            raise ValueError('Selected evidence changed: ' + evidence)
        selected_evidence_inputs.append(evidence)

files = list(selected) + selected_evidence_inputs
for record in selected.values():
    revision = record.get('deliberate_source_revision')
    if not revision:
        continue
    history_name = revision['preserved_history']
    history_path = ROOT / history_name
    if not history_path.resolve().is_relative_to(ROOT / 'reports/full-coverage/source-history'):
        raise ValueError('Historical revision evidence must stay inside source-history.')
    if sha(history_path) != revision['preserved_history_sha256']:
        raise ValueError('Historical revision provenance changed: ' + history_name)
    history = json.loads(history_path.read_text())
    files.append(history_name)
    for preserved in history['preserved_files']:
        path = ROOT / preserved['preserved']
        if not path.resolve().is_relative_to(history_path.parent.resolve()):
            raise ValueError('Historical preserved file escapes its provenance directory.')
        if sha(path) != preserved['sha256']:
            raise ValueError('Historical preserved bytes changed: ' + preserved['preserved'])
        files.append(preserved['preserved'])
files += [str(p.relative_to(ROOT)) for p in (ROOT / 'SafeLearning').iterdir()
          if p.suffix in {'.html', '.css', '.js'}]
files += ['verification/lean/' + name for name in
          ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verify.py']]
files += [str(p.relative_to(ROOT)) for p in (ROOT / 'book/coverage').rglob('*')
          # Archived Lean trials and reviewed JavaScript are evidence inputs.
          # Only selected verification/lean sources enter the proof aggregator.
          if p.is_file() and p.suffix in {'.py', '.json', '.md', '.log', '.html', '.lean', '.js'}
          and '__pycache__' not in p.parts]
for metadata in (ROOT / 'book/coverage').rglob('*.json'):
    files += re.findall(r'"(reports/full-coverage/inventory[^"\n]+\.json)"',
                        metadata.read_text())
files += ['book/inventory_claims.py', 'book/validate.py']
# Freeze the exact browser runner and shared checks used by reader evidence.
files += ['qa/learning_review.mjs', 'qa/book_browser_checks.mjs']
# Located excerpts and exact replay harnesses are opt-in audit inputs. Keep
# full external-paper references outside this reproducibility claim.
for name, record in selection.get('extra_frozen_inputs', {}).items():
    path = (ROOT / name).resolve()
    if (Path(name).is_absolute() or '..' in Path(name).parts
            or str(Path(name)) != name
            or not any(path.is_relative_to(base.resolve()) for base in
            (ROOT / 'book/coverage', ROOT / 'reports/full-coverage/source-history'))):
        raise ValueError('Explicit audit input escapes the allowed provenance roots: ' + name)
    if (record.get('scope') != 'immutable_audit_or_local_source_evidence'
            or (path.suffix not in {'.py', '.json', '.md', '.log', '.html', '.lean', '.js', '.cjs', '.txt'}
                and CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS.get(name) != record['sha256'])
            or sha(path) != record['sha256']):
        raise ValueError('Invalid or changed explicit audit input: ' + name)
    files.append(name)
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
