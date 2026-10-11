"""Build two already selected imports without changing protected26 sources."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, subprocess, sys, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
RUNNER = Path('/tmp/root_tmp_lean27_runner_v2.py')
EXPECTED = 'a4215c69ad35c4df0ed77bc9fc35a348e9e29b865724aac2bb45dde958a82db4'
RECORD = Path('/tmp/root-working27-existing-imports-cache-build-actual-v1.json')
LOG = RECORD.with_suffix('.log')
assert not RECORD.exists() and not LOG.exists()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(RUNNER) == EXPECTED
tree = ast.parse(RUNNER.read_text())
nodes = []
for node in tree.body:
    if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id == 'before' for target in node.targets):
        break
    nodes.append(node)
assert isinstance(nodes[-1], ast.Expr) and ast.unparse(nodes[-1]) == 'guard()'
namespace = {'__file__': str(RUNNER), '__name__': 'existing_selected_import_cache_guard'}
original_args = sys.argv
sys.argv = [str(RUNNER), '/tmp/CompleteCoreMPCLocalBootstrap27-draft-v4.lean', '/tmp/unused-working27-cache-guard-placeholder-v1.json']
try:
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(RUNNER), 'exec'), namespace)
finally:
    sys.argv = original_args
guard = namespace['guard']
selection = namespace['selection']
targets = ['SafeLearning.CompleteModulesValues', 'SafeLearning.CompleteFoundationsGraphViability']
for target in targets:
    source = 'verification/lean/' + target.replace('.', '/') + '.lean'
    assert source in selection['proof_files']
    assert sha(ROOT / source) == selection['proof_files'][source]['sha256']
helper_before = sha(Path(__file__))
command = ['lake', 'build'] + targets
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with LOG.open('xb') as stream:
    actual = subprocess.run(command, cwd=ROOT / 'verification/lean', stdout=stream, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc).isoformat()
errors = []
try:
    guard()
    assert sha(Path(__file__)) == helper_before
except Exception as error:
    errors.append(str(error))
passed = actual.returncode == 0 and not errors
out = {
    'status': 'passed_existing_selected_import_cache_build' if passed else 'failed_existing_selected_import_cache_build',
    'actual_exit_code': actual.returncode, 'actual_runner_exit_code': 0 if passed else 1,
    'actual_command': command, 'actual_workdir': str(ROOT / 'verification/lean'),
    'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': time.monotonic() - tick,
    'actual_runner': {'file': str(Path(__file__)), 'sha256': helper_before},
    'protected_guard_runner': {'file': str(RUNNER), 'sha256': EXPECTED},
    'actual_installed26_selection': {'file': 'reports/full-coverage/checkpoint-26-selection.json', 'sha256': sha(ROOT / 'reports/full-coverage/checkpoint-26-selection.json')},
    'selected_existing_module_sources': {target: selection['proof_files']['verification/lean/' + target.replace('.', '/') + '.lean']['sha256'] for target in targets},
    'raw_log': str(LOG), 'raw_log_sha256': sha(LOG), 'protection_errors': errors,
    'unchanged_selected26_sources': 1167, 'unchanged_current53_assets': 31, 'unchanged_installed26_live_owners': 5,
    'new_canonical_proof_sources_or_coverage_claimed': False,
    'scope': 'A real named Lake build of two already selected sources to populate working artifacts. No new proof installation, mathematical review or aggregate result is inferred.',
}
with RECORD.open('x') as stream: stream.write(json.dumps(out, indent=2) + '\n')
print(json.dumps(out))
raise SystemExit(0 if passed else 1)
