#!/usr/bin/env python3
"""Build, replay, audit axioms and fingerprint the source-linked Lean proofs.

Run from any directory: python3 verification/lean/verify.py
Dependencies are pinned by lean-toolchain and lake-manifest.json.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import time

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parent.parent
OUT = ROOT / 'reports/lean-verification'
OUT.mkdir(parents=True, exist_ok=True)


def run(args, filename):
    start = time.monotonic()
    result = subprocess.run(args, cwd=PROJECT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    (OUT / filename).write_text(result.stdout)
    record = {'command': args, 'exit_code': result.returncode,
              'elapsed_seconds': round(time.monotonic() - start, 3),
              'output_file': str((OUT / filename).relative_to(ROOT))}
    if result.returncode:
        raise RuntimeError(f'{args} failed; see {OUT / filename}\n{result.stdout[-5000:]}')
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
checks.append(run(['lake', 'build'], 'build.log'))
checks.append(run(['lake', 'env', 'leanchecker', '-v', 'SafeLearning'], 'kernel-replay.log'))

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
manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
report = {
    'status': 'passed',
    'verified_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean_version': (OUT / 'lean-version.txt').read_text().strip(),
    'mathlib_revision': next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib'),
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
