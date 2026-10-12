"""Close the interrupted checkpoint31 delivery from actual execution receipts."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
REPORTS = 'reports/full-coverage/'


def read(n):
    return json.loads((ROOT / n).read_bytes())


def ref(n):
    p = ROOT / n
    assert p.is_file() and not p.is_symlink()
    return dict(file=n, sha256=hashlib.sha256(p.read_bytes()).hexdigest())


def native(n):
    d = read(n)
    assert d['status'] == 'passed' and d['actual_exit_code'] == 0
    assert d['helper_sha256_before'] == d['helper_sha256_after']
    assert d['actual_workdir'] == str(ROOT)
    assert all(ref(h)['sha256'] == digest for h, digest in d['helper_sha256_before'].items())
    assert ref(d['log'])['sha256'] == d['log_sha256']
    return [ref(n), ref(d['log'])]


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--metadata-attempt', required=True, type=int)
ap.add_argument('--metadata-native', required=True)
ap.add_argument('--metadata-jobs-native', required=True)
args = ap.parse_args()
out = REPORTS + 'publication31-finish-recovery-v1.json'
history = ROOT / (REPORTS + 'source-history/checkpoint31-before-recovery-closure-v1')
assert not (ROOT / out).exists() and not history.exists()
content = read(REPORTS + 'publication31-content-commit-v1.json')['commit']
metadata = read(REPORTS + 'publication31-metadata-commit-v1.json')['commit']
manifest_name = REPORTS + 'checkpoint-31-manifest.json'
manifest = read(manifest_name)
assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets) == 31 and manifest['coverage_complete'] is False
evidence = [ref(manifest_name)]
for commit, attempt, actual in [
    (content, 2, REPORTS + 'live31-content-confirmation-execution-v2.json'),
    (metadata, args.metadata_attempt, args.metadata_native),
]:
    ln = REPORTS + f'live-checkpoint-31-attempt{attempt}.json'
    pn = REPORTS + f'pages-checkpoint-31-attempt{attempt}.json'
    live, pages = read(ln), read(pn)
    assert live['status'] == 'passed_all31_asset_sha256'
    assert live['commit'] == live['remote_main'] == pages['commit'] == pages['expected_commit'] == commit
    assert pages['status'] == 'passed' and pages['build_status'] == 'built' and pages['exit_code'] == 0
    assert len(live['assets']) == 31
    assert {a['source']: a['expected_sha256'] for a in live['assets']} == assets
    assert all(a['http_status'] == 200 and a['matches'] is True and a['actual_sha256'] == a['expected_sha256'] for a in live['assets'])
    assert read(actual)['actual_command'] == ['python3', 'book/coverage/verify_live19.py', '31', commit, '--attempt', str(attempt)]
    assert ref(pages['log'])['sha256'] == pages['log_sha256']
    evidence += [ref(ln), ref(pn), ref(pages['log']), *native(actual)]
for commit, n in [(content, REPORTS + 'pages31-content-jobs-observation-execution-v1.json'), (metadata, args.metadata_jobs_native)]:
    execution = read(n)
    jobs = read(execution['log'])
    assert execution['actual_command'][:2] == ['gh', 'api'] and execution['actual_command'][2].endswith('/jobs')
    assert jobs['total_count'] == len(jobs['jobs']) == 3
    assert {j['name'] for j in jobs['jobs']} == {'build', 'deploy', 'report-build-status'}
    assert all(j['head_sha'] == commit and j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs'])
    evidence += native(n)
for stem in ['commit-publication31-execution-v1', 'push-publication31-execution-v1', 'prepare-delivery31-metadata-execution-v1', 'commit-delivery31-metadata-execution-v1', 'push-delivery31-metadata-execution-v1']:
    d = read(REPORTS + stem + '.json')
    if stem == 'prepare-delivery31-metadata-execution-v1':
        assert d['actual_command'][:2] == ['python3', 'book/coverage/checks/root_prepare_delivery31_metadata_v4.py']
    else:
        helper = 'book/coverage/checks/root_commit_push_publication31_v3.py' if '-publication31-' in stem else 'book/coverage/checks/root_commit_push_delivery31_metadata_v3.py'
        assert d['actual_command'] == ['python3', helper, 'commit' if stem.startswith('commit-') else 'push']
    evidence += native(REPORTS + stem + '.json')
observations = []
for command, expected in [(['git', 'rev-parse', 'HEAD'], metadata), (['git', 'ls-remote', 'origin', 'refs/heads/main'], metadata + '\trefs/heads/main'), (['git', 'status', '--porcelain=v1'], '')]:
    r = subprocess.run(command, cwd=PUB, capture_output=True, text=True)
    assert r.returncode == 0 and r.stdout.strip() == expected
    observations.append(dict(command=command, actual_workdir=str(PUB), exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr))
record = dict(status='passed_actual_checkpoint31_content_and_metadata_push_Pages_all31_delivery',
              content_commit=content, metadata_commit=metadata, checked_at_utc=datetime.now(timezone.utc).isoformat(),
              actual_publication_observations=observations, evidence=evidence,
              helper=ref(str(Path(__file__).relative_to(ROOT))), coverage_complete=False,
              proof_files=1248, public_theorems=11184,
              scope='Delivery closure only; earlier failed attempts and historical pending fields are preserved. Mathematical coverage remains unfinished.')
with (ROOT / out).open('x') as f:
    f.write(json.dumps(record, indent=2) + '\n')
originals = {}
for n in ['book/coverage/progress.json', 'reports/full-coverage/README.md']:
    p = history / n
    p.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / n, p)
    originals[n] = ref(p.relative_to(ROOT).as_posix())
progress = read('book/coverage/progress.json')
progress['publication_status'] = 'checkpoint31_content_and_metadata_Pages_and_all31_live_confirmed'
progress['live_delivery_status'] = 'passed_content_and_metadata_Pages_and_all31_asset_hashes'
progress['last_published_commit'] = metadata
progress['last_published_metadata_commit'] = metadata
progress['live_delivery_evidence']['metadata_push_and_metadata_live_check_pending'] = False
progress['live_delivery_evidence']['metadata_commit'] = metadata
progress['live_delivery_evidence']['actual_delivery_closure'] = ref(out)
progress['live_delivery_evidence']['actual_metadata_all31_live'] = ref(REPORTS + f'live-checkpoint-31-attempt{args.metadata_attempt}.json')
(ROOT / 'book/coverage/progress.json').write_text(json.dumps(progress, indent=2) + '\n')
p = ROOT / 'reports/full-coverage/README.md'
text = p.read_text()
old = 'The delivery metadata commit is pending;\nfull mathematical coverage remains unfinished.'
assert text.count(old) == 1
p.write_text(text.replace(old, f'The metadata commit `{metadata[:8]}` is also\n[fully confirmed](publication31-finish-recovery-v1.json), including successful\nPages jobs and all 31 live asset hashes. Full mathematical coverage remains unfinished.'))
with (history / 'preserved-originals.json').open('x') as f:
    f.write(json.dumps(originals, indent=2) + '\n')
print(json.dumps(dict(status=record['status'], content_commit=content, metadata_commit=metadata, closure=ref(out))))
