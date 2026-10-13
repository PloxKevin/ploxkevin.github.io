"""Record actual checkpoint34 content delivery; later metadata delivery is separate."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[4]
PUB = ROOT / 'reports/book/publication-repo'
CONTENT = json.loads((ROOT / 'reports/full-coverage/publication34-commit-v1.json').read_bytes())['commit']
BASELINE = '33d83fcfa94ea6425a9b0903507c166a80f97744'
REPORTS = 'reports/full-coverage/'
OUT = REPORTS + 'publication34-content-delivery-v1.json'
HISTORY = REPORTS + 'source-history/checkpoint34-before-content-delivery-v1'


def path(name):
    assert isinstance(name, str) and name and Path(name).as_posix() == name
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    result = ROOT / name
    assert result.resolve().is_relative_to(ROOT) and not result.is_symlink()
    return result


def sha(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def ref(name):
    return {'file': name, 'sha256': sha(path(name))}


def read(name):
    return json.loads(path(name).read_bytes())


def native(name):
    record = read(name)
    assert record['status'] == 'passed' and type(record['actual_exit_code']) is int and record['actual_exit_code'] == 0
    assert record['actual_workdir'] == str(ROOT)
    assert record['helper_sha256_before'] == record['helper_sha256_after']
    assert all(sha(path(helper)) == digest for helper, digest in record['helper_sha256_before'].items())
    assert sha(path(record['log'])) == record['log_sha256']
    return record


def publication_receipt(name, command):
    record = read(name)
    assert record['status'] == 'passed' and type(record['actual_exit_code']) is int and record['actual_exit_code'] == 0
    assert record['actual_command'] == command and record['actual_workdir'] == str(PUB)
    assert record['commit'] == CONTENT and sha(path(record['raw_log'])) == record['raw_log_sha256']
    original = record['actual_command_receipt']
    assert sha(path(original['file'])) == original['sha256']
    immutable = read(original['file'])
    assert all(record[key] == value for key, value in immutable.items())
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True, type=int)
    parser.add_argument('--live-native', required=True)
    parser.add_argument('--jobs-native', required=True)
    args = parser.parse_args()
    assert args.attempt > 0 and not path(OUT).exists() and not path(HISTORY).exists()
    commit_name = REPORTS + 'publication34-commit-v1.json'
    push_name = REPORTS + 'publication34-push-v1.json'
    commit = publication_receipt(commit_name, ['git', 'commit', '--quiet', '-m', 'Verify checkpoint 34: 114 Lean proofs, two exercises and seven material mappings'])
    push = publication_receipt(push_name, ['git', 'push', 'origin', 'main'])
    assert commit['parent'] == BASELINE and push['remote_main'] == CONTENT
    assert all(sha(PUB / name) == digest for name, digest in commit['actual_committed_paths_sha256'].items())

    manifest_name = REPORTS + 'checkpoint-34-manifest.json'
    manifest = read(manifest_name)
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
    assets = {name: digest for name, digest in manifest['frozen_inputs_sha256'].items() if name.startswith('SafeLearning/')}
    assert len(assets) == 31
    live_name = REPORTS + f'live-checkpoint-34-attempt{args.attempt}.json'
    pages_name = REPORTS + f'pages-checkpoint-34-attempt{args.attempt}.json'
    live, pages = read(live_name), read(pages_name)
    assert live['status'] == 'passed_all31_asset_sha256' and live['commit'] == live['remote_main'] == CONTENT
    assert len(live['assets']) == 31 and {row['source']: row['expected_sha256'] for row in live['assets']} == assets
    assert all(row['http_status'] == 200 and row['matches'] is True and row['actual_sha256'] == row['expected_sha256'] for row in live['assets'])
    assert pages['status'] == 'passed' and pages['build_status'] == 'built' and pages['exit_code'] == 0
    assert pages['commit'] == pages['expected_commit'] == CONTENT
    assert pages['command'] == ['gh', 'api', 'repos/PloxKevin/ploxkevin.github.io/pages/builds/latest']
    assert pages['actual_workdir'] == str(PUB) and sha(path(pages['log'])) == pages['log_sha256']
    actual_live = native(args.live_native)
    normalized = [part for part in actual_live['actual_command'] if part != '-B']
    assert normalized == ['python3', 'book/coverage/verify_live19.py', '34', CONTENT, '--attempt', str(args.attempt)]
    actual_jobs = native(args.jobs_native)
    jobs_command = actual_jobs['actual_command']
    assert jobs_command[:2] == ['gh', 'api'] and len(jobs_command) == 3
    assert re.fullmatch(r'repos/PloxKevin/ploxkevin\.github\.io/actions/runs/\d+/jobs', jobs_command[2])
    jobs = read(actual_jobs['log'])
    assert jobs['total_count'] == len(jobs['jobs']) == 3
    assert {row['name'] for row in jobs['jobs']} == {'build', 'deploy', 'report-build-status'}
    assert all(row['head_sha'] == CONTENT and row['status'] == 'completed' and row['conclusion'] == 'success' for row in jobs['jobs'])

    observations = []
    for command, expected in [(['git', 'symbolic-ref', '--short', 'HEAD'], 'main'),
                              (['git', 'rev-parse', 'HEAD'], CONTENT),
                              (['git', 'rev-parse', 'HEAD^'], BASELINE),
                              (['git', 'ls-remote', 'origin', 'refs/heads/main'], CONTENT + '\trefs/heads/main'),
                              (['git', 'status', '--porcelain=v1', '--untracked-files=all'], '')]:
        result = subprocess.run(command, cwd=PUB, capture_output=True, text=True)
        assert result.returncode == 0 and result.stdout.strip() == expected
        observations.append({'command': command, 'actual_workdir': str(PUB), 'actual_exit_code': result.returncode,
                             'stdout': result.stdout, 'stderr': result.stderr})
    progress_path, readme_path = path('book/coverage/progress.json'), path('reports/full-coverage/README.md')
    progress = json.loads(progress_path.read_bytes())
    verified = progress['verified_checkpoint']
    assert verified['checkpoint'] == 34 and verified['status'] == 'passed' and verified['coverage_complete'] is False
    assert verified['proof_files'] == 1264 and verified['theorems'] == 11459
    preparation = progress['working_next_checkpoint_preparation']
    assert preparation['exercise_counts'] == {'complete': 538, 'partial': 7, 'pending': 11}
    assert preparation['material_review_units'] == {'reviewed': 4858, 'pending': 7916}
    old_line = 'Checkpoint 34 is verified locally; its GitHub delivery is pending.'
    readme = readme_path.read_text()
    assert readme.count(old_line) == 1
    held = {name: digest for name, digest in manifest['working_inputs_sha256'].items()
            if name.startswith(('SafeLearning/', 'verification/lean/SafeLearning/', 'book/coverage/'))}
    assert all(sha(path(name)) == digest for name, digest in held.items())

    originals = {}
    for name in ['book/coverage/progress.json', 'reports/full-coverage/README.md', 'README.md']:
        target = path(HISTORY + '/' + name)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path(name), target)
        assert sha(target) == sha(path(name))
        originals[name] = ref(target.relative_to(ROOT).as_posix())
    record = {'status': 'passed_actual_checkpoint34_content_push_Pages_and_all31_live_hashes',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'content_commit': CONTENT,
              'actual_content_commit': ref(commit_name), 'actual_content_push': ref(push_name),
              'content_live_check': ref(live_name), 'content_pages_check': ref(pages_name),
              'actual_live_native': ref(args.live_native), 'actual_live_log': ref(actual_live['log']),
              'actual_pages_log': ref(pages['log']), 'actual_jobs_native': ref(args.jobs_native),
              'actual_three_successful_jobs': ref(actual_jobs['log']), 'manifest': ref(manifest_name),
              'actual_publication_observations': observations, 'preserved_original_documents': originals,
              'proof_files': 1264, 'public_theorems': 11459,
              'exercise_counts': preparation['exercise_counts'], 'material_review_units': preparation['material_review_units'],
              'metadata_push_and_metadata_live_check_pending': True, 'coverage_complete': False,
              'helper': ref(Path(__file__).relative_to(ROOT).as_posix()),
              'scope': 'Successful content delivery only. The later delivery-metadata commit, push and fresh live verification remain separate.'}
    with path(OUT).open('x') as output:
        output.write(json.dumps(record, indent=2) + '\n')
    progress['last_published_commit'] = CONTENT
    progress['last_published_content_commit'] = CONTENT
    progress['publication_status'] = 'checkpoint34_content_published_Pages_and_all31_live_verified_metadata_pending'
    progress['live_delivery_status'] = 'passed_checkpoint34_content_Pages_and_all31_asset_hashes_metadata_pending'
    progress['live_delivery_evidence'] = {'previous_checkpoint33': progress['previous_checkpoint33_delivery'],
                                       'content_commit': CONTENT, 'actual_content_delivery': ref(OUT),
                                       'content_live_check': ref(live_name), 'content_pages_check': ref(pages_name),
                                       'actual_live_execution': ref(args.live_native),
                                       'actual_three_successful_jobs': ref(actual_jobs['log']),
                                       'actual_content_push': ref(push_name),
                                       'metadata_push_and_metadata_live_check_pending': True}
    progress['working_next_checkpoint_preparation']['status'] = 'checkpoint34_content_published_full_coverage_objective_unfinished'
    progress_path.write_text(json.dumps(progress, indent=2) + '\n')
    new_line = (f'Checkpoint 34 content is published at `{CONTENT[:8]}`. Its Pages jobs\n'
                f'completed successfully, and the [fresh live check]({Path(live_name).name})\n'
                'verified all 31 asset hashes. The [actual content delivery](publication34-content-delivery-v1.json)\n'
                'preserves the commit, push and served-byte evidence. The later delivery-metadata\n'
                'commit, push and live check remain pending. Full mathematical coverage remains unfinished.')
    readme_path.write_text(readme.replace(old_line, new_line))
    root_readme_path = path('README.md')
    root_readme = root_readme_path.read_text()
    old_root = 'Checkpoint 34 is verified locally and awaits delivery.'
    assert root_readme.count(old_root) == 1
    root_readme_path.write_text(root_readme.replace(old_root, 'Checkpoint 34 is published with all 31 live asset hashes confirmed.'))
    assert all(sha(path(name)) == digest for name, digest in held.items())
    print(json.dumps({'status': record['status'], 'content_commit': CONTENT, 'delivery': ref(OUT),
                      'metadata_delivery_pending': True, 'coverage_complete': False}))


if __name__ == '__main__':
    main()
