"""Close actual checkpoint33 metadata delivery without asserting full coverage."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[4]
PUB = ROOT / 'reports/book/publication-repo'
PREFIX = 'reports/full-coverage/'
CONTENT = json.loads((ROOT / 'reports/full-coverage/publication33-commit-v1.json').read_bytes())['commit']
METADATA = json.loads((ROOT / 'reports/full-coverage/publication33-metadata-commit-v1.json').read_bytes())['commit']
OUT = PREFIX + 'publication33-finish-v1.json'
HISTORY = PREFIX + 'source-history/checkpoint33-before-metadata-closure-v1'


def read(n):
    return json.loads((ROOT / n).read_bytes())


def ref(n):
    p = ROOT / n
    assert p.is_file() and not p.is_symlink()
    return dict(file=n, sha256=hashlib.sha256(p.read_bytes()).hexdigest())


assert not (ROOT / OUT).exists() and not (ROOT / HISTORY).exists()
content_name = PREFIX + 'publication33-content-delivery-v1.json'
assert read(content_name)['status'] == 'passed_actual_checkpoint33_content_push_Pages_and_all31_live_hashes'
assert read(content_name)['content_commit'] == CONTENT
evidence = [ref(content_name)]
for mode, command in [('commit', ['git', 'commit', '--quiet', '-m', 'Record checkpoint 33 successful Pages delivery and continuation notes']), ('push', ['git', 'push', 'origin', 'main'])]:
    n = PREFIX + f'publication33-metadata-{mode}-v1.json'
    d = read(n)
    assert d['status'] == 'passed' and d['actual_exit_code'] == 0 and d['commit'] == METADATA
    assert d['actual_command'] == command and d['actual_workdir'] == str(PUB)
    assert ref(d['raw_log'])['sha256'] == d['raw_log_sha256']
    original = d['actual_command_receipt']
    assert ref(original['file'])['sha256'] == original['sha256']
    assert all(d[k] == v for k, v in read(original['file']).items())
    evidence += [ref(n), ref(d['raw_log']), original]
manifest = read(PREFIX + 'checkpoint-33-manifest.json')
assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
live_name = PREFIX + 'live-checkpoint-33-attempt2.json'
pages_name = PREFIX + 'pages-checkpoint-33-attempt2.json'
live, pages = read(live_name), read(pages_name)
assert live['status'] == 'passed_all31_asset_sha256' and live['commit'] == live['remote_main'] == METADATA
assert len(live['assets']) == len(assets) == 31
assert {a['source']: a['expected_sha256'] for a in live['assets']} == assets
assert all(a['matches'] is True and a['http_status'] == 200 and a['actual_sha256'] == a['expected_sha256'] for a in live['assets'])
assert pages['status'] == 'passed' and pages['build_status'] == 'built' and pages['exit_code'] == 0
assert pages['commit'] == pages['expected_commit'] == METADATA
assert ref(pages['log'])['sha256'] == pages['log_sha256']
evidence += [ref(live_name), ref(pages_name), ref(pages['log'])]
native_names = ['live33-metadata-execution-v1', 'pages33-metadata-jobs-execution-v1', 'commit-metadata33-execution-v1', 'push-metadata33-execution-v1']
for stem in native_names:
    n = PREFIX + stem + '.json'
    d = read(n)
    assert d['status'] == 'passed' and d['actual_exit_code'] == 0 and d['actual_workdir'] == str(ROOT)
    assert d['helper_sha256_before'] == d['helper_sha256_after']
    assert all(ref(h)['sha256'] == digest for h, digest in d['helper_sha256_before'].items())
    assert ref(d['log'])['sha256'] == d['log_sha256']
    evidence += [ref(n), ref(d['log'])]
assert read(PREFIX + native_names[0] + '.json')['actual_command'] == ['python3', 'book/coverage/verify_live19.py', '33', METADATA, '--attempt', '2']
jobs_native = read(PREFIX + native_names[1] + '.json')
assert len(jobs_native['actual_command']) == 3 and jobs_native['actual_command'][:2] == ['gh', 'api']
assert __import__('re').fullmatch(r'repos/PloxKevin/ploxkevin\.github\.io/actions/runs/\d+/jobs', jobs_native['actual_command'][2])
jobs = read(jobs_native['log'])
assert jobs['total_count'] == len(jobs['jobs']) == 3
assert all(j['head_sha'] == METADATA and j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs'])
observations = []
for command, expected in [(['git', 'rev-parse', 'HEAD'], METADATA), (['git', 'ls-remote', 'origin', 'refs/heads/main'], METADATA + '\trefs/heads/main'), (['git', 'status', '--porcelain=v1', '--untracked-files=all'], '')]:
    r = subprocess.run(command, cwd=PUB, capture_output=True, text=True)
    assert r.returncode == 0 and r.stdout.strip() == expected
    observations.append(dict(command=command, actual_workdir=str(PUB), actual_exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr))
record = dict(status='passed_actual_checkpoint33_content_and_metadata_push_Pages_all31_delivery',
              content_commit=CONTENT, metadata_commit=METADATA, checked_at_utc=datetime.now(timezone.utc).isoformat(),
              evidence=evidence, actual_publication_observations=observations,
              proof_files=1261, public_theorems=11345, coverage_complete=False,
              scope='Closes delivery only. Mathematical coverage remains 536 complete, 8 partial and 12 pending exercises, and 7923 pending material units.')
with (ROOT / OUT).open('x') as f:
    f.write(json.dumps(record, indent=2) + '\n')
n = 'book/coverage/progress.json'
p = ROOT / HISTORY / n
p.parent.mkdir(parents=True)
shutil.copyfile(ROOT / n, p)
d = read(n)
assert d['verified_checkpoint']['checkpoint'] == 33 and d['verified_checkpoint']['status'] == 'passed'
d['last_published_commit'] = METADATA
d['last_published_metadata_commit'] = METADATA
d['publication_status'] = 'checkpoint33_content_and_metadata_Pages_and_all31_live_confirmed'
d['live_delivery_status'] = 'passed_content_and_metadata_Pages_and_all31_asset_hashes'
d['live_delivery_evidence'].update(metadata_commit=METADATA, metadata_push_and_metadata_live_check_pending=False,
                                  actual_delivery_closure=ref(OUT), actual_metadata_all31_live=ref(live_name))
(ROOT / n).write_text(json.dumps(d, indent=2) + '\n')
print(json.dumps(dict(status=record['status'], metadata_commit=METADATA, record=ref(OUT))))
