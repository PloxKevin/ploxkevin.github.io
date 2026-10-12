"""Export genuine runtime30 audit bytes with explicit original execution paths."""
from pathlib import Path
import argparse, hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[2]
RUNTIME = ROOT / 'reports/full-coverage/runtime-checkpoint-30-final-css-v1'
ORIGINAL = RUNTIME / 'reports/lean-verification'
OUT = ROOT / 'reports/full-coverage/lean-checkpoint-30-final-css-v1'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--actual-report-sha256', required=True)
args = parser.parse_args()
REPORT_SHA = args.actual_report_sha256
SELECTION_SHA = '21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


assert not OUT.exists() and not OUT.is_symlink()
assert OUT.resolve().is_relative_to(ROOT)
assert all(not p.is_symlink() for p in OUT.parents if p.is_relative_to(ROOT))
report = ORIGINAL / 'verification.json'
assert sha(report) == REPORT_SHA
d = json.loads(report.read_bytes())
assert d['status'] == 'passed' and d['proof_file_count'] == len(d['proof_sha256']) == 1242
assert d['theorem_count'] == len(d['declarations']) == len(d['axiom_dependencies']) == 11080
assert len(d['checks']) == 1245 and all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in d['checks'])
assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in d['checks']) == 0
assert sum(bool(c.get('reused_from')) for c in d['checks']) == 1242
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(d['allowed_standard_axioms']) == allowed
assert all(set(a) <= allowed for a in d['axiom_dependencies'].values())
selection_path = ROOT / 'reports/full-coverage/checkpoint-30-selection.json'
assert sha(selection_path) == SELECTION_SHA
selection = json.loads(selection_path.read_bytes())
assert d['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
for field in ['source_sha256', 'proof_sha256', 'project_sha256']:
    for n, h in d[field].items():
        assert sha(RUNTIME / n) == h
        if n != 'verification/lean/SafeLearning.lean':
            assert sha(ROOT / n) == h
native_path = ROOT / 'reports/full-coverage/verify-runtime-checkpoint30-final-css-execution-v1.json'
native = json.loads(native_path.read_bytes())
assert native['status'] == 'passed' and native['actual_exit_code'] == 0
assert native['actual_command'] == ['python3', 'reports/full-coverage/runtime-checkpoint-30-final-css-v1/verification/lean/verify.py', '--reuse-kernel-from', str(ROOT / 'reports/full-coverage/runtime-checkpoint-30')]
assert native['actual_workdir'] == str(ROOT)
assert sha(ROOT / native['log']) == native['log_sha256']
assert native['helper_sha256_before'] == native['helper_sha256_after'] == {'reports/full-coverage/runtime-checkpoint-30-final-css-v1/verification/lean/verify.py': sha(RUNTIME / 'verification/lean/verify.py')}
files = sorted(p for p in ORIGINAL.rglob('*') if p.is_file())
assert all(not p.is_symlink() and '.lake' not in p.relative_to(ORIGINAL).parts for p in files)
initial = {str(p.relative_to(ORIGINAL)): sha(p) for p in files}
OUT.mkdir()
for p in files:
    target = OUT / p.relative_to(ORIGINAL)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, target)
    assert sha(target) == initial[str(p.relative_to(ORIGINAL))]
(OUT / 'verification.json').rename(OUT / 'verification-original.json')
assert sha(OUT / 'verification-original.json') == REPORT_SHA
old_prefix = 'reports/lean-verification/'
new_prefix = 'reports/full-coverage/lean-checkpoint-30-final-css-v1/'


def relocate(c):
    if isinstance(c.get('output_file'), str) and c['output_file'].startswith(old_prefix):
        c['output_file'] = c['output_file'].replace(old_prefix, new_prefix, 1)
    reused = c.get('reused_from')
    if isinstance(reused, dict) and isinstance(reused.get('report'), str) and reused['report'].startswith(old_prefix):
        reused['report'] = reused['report'].replace(old_prefix, new_prefix, 1)


copy = json.loads(json.dumps(d))
for c in copy['checks']:
    relocate(c)
copy['audit_origin'] = {'original_report': 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json',
                        'original_report_sha256': REPORT_SHA, 'actual_workdir': str(RUNTIME / 'verification/lean'),
                        'actual_Root_execution': {'file': str(native_path.relative_to(ROOT)), 'sha256': sha(native_path)},
                        'source_only_runtime_preparation': 'reports/full-coverage/checkpoint30-runtime-final-css-preparation-v1.json',
                        'scope': 'Only report/output locations relocated. Every command, original_check, cwd, time and source identity remains genuine. The runtime and future source-only snapshot have distinct paths; no frozen-snapshot execution is invented.'}
(OUT / 'verification.json').write_text(json.dumps(copy, indent=2) + '\n')
progress = OUT / 'kernel-progress.json'
if progress.exists():
    pd = json.loads(progress.read_bytes())
    for c in pd['checks'].values():
        relocate(c)
    progress.write_text(json.dumps(pd, indent=2) + '\n')
assert initial == {str(p.relative_to(ORIGINAL)): sha(p) for p in files}
print(json.dumps({'status': 'actual_runtime30_audit_exported_original_provenance_preserved',
                  'proof_files': 1242, 'public_theorems': 11080,
                  'original_report': 'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json',
                  'original_sha256': REPORT_SHA, 'coverage_complete': False}))
