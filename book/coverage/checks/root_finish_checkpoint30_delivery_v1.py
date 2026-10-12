"""Close checkpoint 30 delivery using actual recorded content and metadata checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
CONTENT = 'ae9e78658094db31d456b9dec509cc7a92b7f386'
METADATA = '676db1f7d13ddbf65c2f0253d1fab79c44948a7e'
OUT = ROOT / 'reports/full-coverage/publication30-finish-root-v1.json'

def read(name):
    return json.loads((ROOT / name).read_text())

def ref(name):
    path = ROOT / name
    assert path.is_file() and not path.is_symlink()
    return {'file': name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size}

def native(name):
    data = read(name)
    assert data['status'] == 'passed' and data['actual_exit_code'] == 0
    assert data['helper_sha256_before'] == data['helper_sha256_after']
    assert ref(data['log'])['sha256'] == data['log_sha256']
    return [ref(name), ref(data['log'])]

assert not OUT.exists()
manifest = read('reports/full-coverage/checkpoint-30-manifest.json')
assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets) == 31 and manifest['coverage_complete'] is False
evidence = [ref('reports/full-coverage/checkpoint-30-manifest.json')]
for commit, attempt, actual in [
    (CONTENT, 2, 'reports/full-coverage/live30-content-confirmation-execution-v2.json'),
    (METADATA, 3, 'reports/full-coverage/live30-metadata-confirmation-execution-v1.json'),
]:
    live_name = f'reports/full-coverage/live-checkpoint-30-attempt{attempt}.json'
    pages_name = f'reports/full-coverage/pages-checkpoint-30-attempt{attempt}.json'
    live, pages = read(live_name), read(pages_name)
    assert live['status'] == 'passed_all31_asset_sha256'
    assert live['commit'] == live['remote_main'] == pages['commit'] == pages['expected_commit'] == commit
    assert pages['status'] == 'passed' and pages['build_status'] == 'built' and pages['exit_code'] == 0
    assert len(live['assets']) == 31
    assert {a['source']: a['expected_sha256'] for a in live['assets']} == assets
    assert all(a['http_status'] == 200 and a['matches'] is True and a['actual_sha256'] == a['expected_sha256'] for a in live['assets'])
    execution = read(actual)
    assert execution['actual_command'] == ['python3', 'book/coverage/verify_live19.py', '30', commit, '--attempt', str(attempt)]
    assert ref(pages['log'])['sha256'] == pages['log_sha256']
    evidence.extend([ref(live_name), ref(pages_name), ref(pages['log']), *native(actual)])

for name, run in [('pages30-content-jobs-observation-execution-v1', 38256238615), ('pages30-metadata-jobs-observation-execution-v2', 38257568418)]:
    filename = f'reports/full-coverage/{name}.json'
    execution = read(filename)
    assert execution['actual_command'][2] == f'repos/PloxKevin/ploxkevin.github.io/actions/runs/{run}/jobs'
    jobs = json.loads((ROOT / execution['log']).read_bytes())
    assert jobs['total_count'] == len(jobs['jobs']) == 3
    assert {job['name'] for job in jobs['jobs']} == {'build', 'deploy', 'report-build-status'}
    assert all(job['status'] == 'completed' and job['conclusion'] == 'success' for job in jobs['jobs'])
    evidence.extend(native(filename))

for name in ['commit-publication30-execution-v1', 'push-publication30-execution-v1', 'commit-delivery30-metadata-execution-v1', 'push-delivery30-metadata-execution-v1']:
    evidence.extend(native(f'reports/full-coverage/{name}.json'))
commands = [(['git', 'rev-parse', 'HEAD'], METADATA), (['git', 'ls-remote', 'origin', 'refs/heads/main'], METADATA + '\trefs/heads/main'), (['git', 'status', '--porcelain=v1'], '')]
observations = []
for command, expected in commands:
    result = subprocess.run(command, cwd=PUB, capture_output=True, text=True)
    assert result.returncode == 0 and result.stdout.strip() == expected
    observations.append({'command': command, 'actual_workdir': str(PUB), 'exit_code': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr})

record = {'status': 'passed_actual_checkpoint30_content_and_metadata_push_Pages_all31_delivery',
    'content_commit': CONTENT, 'metadata_commit': METADATA, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'actual_publication_observations': observations, 'evidence': evidence, 'helper': ref(str(Path(__file__).relative_to(ROOT))),
    'coverage_complete': False, 'proof_files': 1242, 'public_theorems': 11080,
    'scope': 'Closes actual checkpoint30 delivery only. Historical pending fields describe their original recording times. No new mathematical coverage or unexecuted audit is inferred.'}
with OUT.open('x') as output:
    output.write(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': record['status'], 'record': ref(str(OUT.relative_to(ROOT))), 'content_commit': CONTENT, 'metadata_commit': METADATA, 'coverage_complete': False}))
