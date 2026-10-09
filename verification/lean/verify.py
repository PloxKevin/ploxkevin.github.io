#!/usr/bin/env python3
"""Build, replay, audit axioms and fingerprint the source-linked Lean proofs.

Run from any directory: python3 verification/lean/verify.py
Dependencies are pinned by lean-toolchain and lake-manifest.json.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import subprocess
import time

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=ROOT / 'reports/lean-verification',
                    help='Report directory; use a separate directory for a new source revision.')
parser.add_argument('--resume-kernel', action='store_true',
                    help='Reuse completed per-module kernel checks only when all input and log hashes match.')
args = parser.parse_args()
OUT = args.output.resolve()
if not OUT.is_relative_to(ROOT):
    raise ValueError('Reports must stay within the repository.')
OUT.mkdir(parents=True, exist_ok=True)


def run(args, filename):
    start = time.monotonic()
    # Keep evidence while long kernel replay is running, including interrupted
    # attempts. A successful report still requires the actual returned exit code.
    with (OUT / filename).open('w') as logfile:
        result = subprocess.run(args, cwd=PROJECT, text=True, stdout=logfile,
                                stderr=subprocess.STDOUT, check=False)
    record = {'command': args, 'exit_code': result.returncode,
              'elapsed_seconds': round(time.monotonic() - start, 3),
              'output_file': str((OUT / filename).relative_to(ROOT))}
    if result.returncode:
        tail = (OUT / filename).read_text()[-5000:]
        raise RuntimeError(f'{args} failed; see {OUT / filename}\n{tail}')
    return record


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


proof_files = sorted((PROJECT / 'SafeLearning').glob('*.lean'))
proof_files = [p for p in proof_files if p.name != 'Smoke.lean']
site_files = sorted(p for p in (ROOT / 'SafeLearning').iterdir()
                    if p.suffix in {'.html', '.js', '.css'})
project_files = [PROJECT / name for name in
                 ['SafeLearning.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verify.py']]
initial_hashes = {str(p.relative_to(ROOT)): sha(p)
                  for p in proof_files + site_files + project_files}
declarations = []
for p in proof_files:
    source = p.read_text()
    # These files use one top-level namespace each. Reject ambiguous changes.
    namespaces = re.findall(r'^namespace\s+(\S+)', source, re.M)
    if len(namespaces) != 1:
        raise RuntimeError(f'Expected one namespace in {p}')
    bare = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    bare = re.sub(r'--[^\n]*', '', bare)
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab)\b|'
                           r'ofReduceBool|sorryAx', bare)
    if forbidden:
        raise RuntimeError(f'Forbidden proof escape in {p}: {forbidden}')
    for m in re.finditer(r'^(?:theorem|lemma)\s+([^\s({:]+)', bare, re.M):
        declarations.append({'name': namespaces[0] + '.' + m.group(1),
                             'file': str(p.relative_to(ROOT))})

checks = []
checks.append(run(['lean', '--version'], 'lean-version.txt'))
manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
dependencies = []
for package in manifest['packages']:
    if package.get('type') != 'git':
        raise RuntimeError(f'Unrecognized dependency type: {package["name"]}')
    checkout = PROJECT / manifest['packagesDir'] / package['name']
    revision = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                       text=True).strip()
    if revision != package['rev']:
        raise RuntimeError(f'Dependency revision mismatch: {package["name"]}')
    dependencies.append({'name': package['name'], 'revision': revision})
checks.append(run(['lake', 'build'], 'build.log'))
# leanchecker starts one task per target module. Explicit single-module targets
# keep the same replay coverage while avoiding dozens of simultaneous copies of
# the imported Mathlib environment. Save each actual exit so interrupted runs
# can resume without treating an unfinished command as a pass.
kernel_progress_path = OUT / 'kernel-progress.json'
kernel_identity = {'input_sha256': initial_hashes, 'dependency_revisions': dependencies,
                   'lean_version': (OUT / 'lean-version.txt').read_text().strip()}
kernel_progress = {'identity': kernel_identity, 'checks': {}}
if args.resume_kernel and kernel_progress_path.exists():
    previous = json.loads(kernel_progress_path.read_text())
    if previous.get('identity') != kernel_identity:
        raise RuntimeError('Cannot resume kernel replay: source or dependency identity changed.')
    kernel_progress = previous
modules = ['SafeLearning.' + p.stem for p in proof_files]
aggregator_lines = [line.strip() for line in (PROJECT / 'SafeLearning.lean').read_text().splitlines()
                    if line.strip()]
if sorted(aggregator_lines) != sorted('import ' + module for module in modules):
    raise RuntimeError('Aggregator must import every audited proof module exactly once and contain no declarations.')
for module in modules:
    filename = 'kernel-' + module.replace('.', '-') + '.log'
    saved = kernel_progress['checks'].get(module)
    if saved is not None:
        logfile = ROOT / saved['output_file']
        if saved.get('exit_code') != 0 or not logfile.exists() or sha(logfile) != saved.get('log_sha256'):
            raise RuntimeError(f'Invalid saved kernel evidence for {module}')
        checks.append(saved)
        continue
    record = run(['lake', 'env', 'leanchecker', '-v', module], filename)
    record.update(module=module, log_sha256=sha(OUT / filename))
    kernel_progress['checks'][module] = record
    kernel_progress_path.write_text(json.dumps(kernel_progress, indent=2) + '\n')
    checks.append(record)
    print(f'Kernel replay passed: {module}', flush=True)

axiom_source = PROJECT / 'AxiomAudit.lean'
axiom_source.write_text('import SafeLearning\n\n' + '\n'.join(
    '#print axioms ' + d['name'] for d in declarations) + '\n')
checks.append(run(['lake', 'env', 'lean', str(axiom_source)], 'axioms.log'))
axiom_output = (OUT / 'axioms.log').read_text()
axioms = {}
for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_output):
    axioms[name] = [x.strip() for x in deps.split(',') if x.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", axiom_output):
    axioms[name] = []
expected = {d['name'] for d in declarations}
if set(axioms) != expected:
    raise RuntimeError(f'Axiom output mismatch: missing {expected-set(axioms)}; extra {set(axioms)-expected}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
unexpected = {n: ds for n, ds in axioms.items() if set(ds) - allowed}
if unexpected:
    raise RuntimeError(f'Unexpected axiom dependencies: {unexpected}')

final_hashes = {str(p.relative_to(ROOT)): sha(p)
                for p in proof_files + site_files + project_files}
if initial_hashes != final_hashes:
    raise RuntimeError('Proof, project or site source changed during verification; rerun after edits finish.')
site_hashes = {str(p.relative_to(ROOT)): sha(p) for p in site_files}
proof_hashes = {str(p.relative_to(ROOT)): sha(p) for p in proof_files}
report = {
    'status': 'passed',
    'verified_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': (OUT / 'lean-version.txt').read_text().strip(),
    'mathlib_revision': next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib'),
    'dependency_revisions': dependencies,
    'checks': checks,
    'proof_file_count': len(proof_files),
    'theorem_count': len(declarations),
    'declarations': declarations,
    'axiom_dependencies': axioms,
    'allowed_standard_axioms': sorted(allowed),
    'source_sha256': site_hashes,
    'proof_sha256': proof_hashes,
    'project_sha256': {str(p.relative_to(ROOT)): sha(p) for p in project_files},
    'limits': [
        'Kernel replay uses Lean\u0027s own kernel; it is not an independent theorem prover.',
        'Imported Mathlib declarations remain dependency artifacts; replay here targets course proof modules.',
        'This audit verifies the encoded statements. The coverage ledgers record correspondence and limits for the HTML.',
        'A passing report does not mean every exercise subclaim or cited research theorem is formalized.'
    ]
}
(OUT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'Passed: {len(declarations)} theorems in {len(proof_files)} files; kernel replay and standard-axiom audit.')
