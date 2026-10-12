"""Keep the first draft and correct its derived proof-file bookkeeping."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'book/coverage/checks/recovery32-core/polygonal14-component-v1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {'file': path.relative_to(ROOT).as_posix(), 'sha256': sha(path), 'bytes': path.stat().st_size}


def new_json(path, value):
    with path.open('x') as output:
        output.write(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


readiness_path = BASE / 'polygonal14-readiness-v1.json'
prior = json.loads(readiness_path.read_bytes())
assert prior['status'] == 'passed_exact_reviewed_polygonal14_canonical_pair_component_candidate32'
assert prior['errors'] == []
for name, digest in prior['protected_inputs_sha256'].items():
    path = Path(name) if Path(name).is_absolute() else ROOT / name
    assert sha(path) == digest, name
source = ROOT / prior['canonical_source']['file']
assert sha(source) == prior['canonical_source']['sha256']
draft_path = ROOT / prior['candidate']['file']
assert sha(draft_path) == prior['candidate']['sha256']
candidate = json.loads(draft_path.read_bytes())
assert candidate['counts']['proof_files'] == 187 and len(candidate['proof_files']) == 188
candidate['counts']['proof_files'] = len(candidate['proof_files'])
candidate_path = BASE / 'core-candidate-v2.json'
new_json(candidate_path, candidate)

original_path = ROOT / prior['exact_original_byte_aliases']['book/coverage/core.json']['file']
original = json.loads(original_path.read_bytes())
inverse = copy.deepcopy(candidate)
del inverse['future32_actual_polygonal_component_binding']
del inverse['proof_files'][prior['canonical_source']['file']]
inverse['counts']['proof_files'] = original['counts']['proof_files']
exercise = next(row for row in inverse['exercises'] if row['inventory_key'] == 'barriers.html::exercise-16')
added = exercise['claims'].pop()
assert added['id'] == 'barriers.html::exercise-16::actual-polygonal-global-bound-component32'
assert inverse == original

isolated = BASE / 'isolated-ledger-root-v2'
coverage = isolated / 'book/coverage'
coverage.mkdir(parents=True)
for name in ['validate.py', 'lean_names.py']:
    with (coverage / name).open('xb') as output:
        output.write((ROOT / 'book/coverage' / name).read_bytes())
for name in ['inventory.json', 'foundations.json', 'applied.json', 'modules.json']:
    (coverage / name).symlink_to(ROOT / 'book/coverage' / name)
(coverage / 'core.json').symlink_to(candidate_path)
(isolated / 'SafeLearning').symlink_to(ROOT / 'SafeLearning', target_is_directory=True)
(isolated / 'verification').mkdir()
(isolated / 'verification/lean').symlink_to(ROOT / 'verification/lean', target_is_directory=True)
report_path = BASE / 'ledger-candidate-integrity-v2.json'
log = BASE / 'ledger-candidate-validation-v2.log'
command = ['python3', str(coverage / 'validate.py'), '--output', str(report_path)]
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with log.open('xb') as output:
    result = subprocess.run(command, cwd=isolated, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'), stdout=output, stderr=subprocess.STDOUT)
native = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
          'actual_command': command, 'actual_workdir': str(isolated), 'started_at_utc': started,
          'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
          'candidate': ref(candidate_path), 'helper': ref(coverage / 'validate.py'), 'log': ref(log), 'report': ref(report_path)}
native_path = BASE / 'ledger-candidate-validation-actual-v2.json'
new_json(native_path, native)
report = json.loads(report_path.read_bytes())
assert result.returncode == 0 and report['integrity_status'] == 'passed' and report['errors'] == []
assert report['mathematical_coverage_complete'] is False
assert report['counts']['statuses']['exercise:complete_math'] == 536
assert report['counts']['statuses']['exercise:partial'] == 8 and report['counts']['statuses']['exercise:pending'] == 12
assert report['counts']['material_review_statuses'] == {'reviewed': 4835, 'pending': 7939}
for name, digest in prior['protected_inputs_sha256'].items():
    path = Path(name) if Path(name).is_absolute() else ROOT / name
    assert sha(path) == digest, name
assert sha(source) == prior['canonical_source']['sha256']
final = {'status': 'passed_exact_reviewed_polygonal14_canonical_pair_component_candidate32',
         'errors': [], 'finalized_at_utc': datetime.now(timezone.utc).isoformat(),
         'first_draft_preserved': ref(draft_path), 'first_readiness': ref(readiness_path),
         'candidate': ref(candidate_path), 'candidate_integrity': ref(report_path),
         'candidate_validation': ref(native_path), 'canonical_source': prior['canonical_source'],
         'actual_paired_records': prior['actual_paired_records'], 'original_math_peer': prior['original_math_peer'],
         'exact_original_byte_aliases': prior['exact_original_byte_aliases'],
         'protected_inputs_sha256': prior['protected_inputs_sha256'],
         'candidate_proof_file_count': 188, 'public_theorem_count': 14, 'public_name_count': 16,
         'actual_compiler_command_count': 2,
         'exact_inverse_to_original_core_ledger': True,
         'whole_exercise_and_material_status_unchanged': True,
         'aggregate_kernel_axiom_owner_installation_or_publication_claimed': False,
         'coverage_complete': False}
final_path = BASE / 'polygonal14-readiness-v2.json'
new_json(final_path, final)
print(json.dumps({'status': final['status'], 'candidate': ref(candidate_path), 'readiness': ref(final_path),
                  'exact_inverse_to_original_core_ledger': True, 'coverage_complete': False}))
