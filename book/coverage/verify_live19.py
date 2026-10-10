"""Check all frozen asset bytes and the actual Pages build in a new numbered attempt."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('checkpoint', type=int)
parser.add_argument('commit')
parser.add_argument('--attempt', type=int, required=True)
args = parser.parse_args()
assert args.attempt > 0
reports = ROOT / 'reports/full-coverage'
publication = ROOT / 'reports/book/publication-repo'
live_path = reports / f'live-checkpoint-{args.checkpoint}-attempt{args.attempt}.json'
pages_path = reports / f'pages-checkpoint-{args.checkpoint}-attempt{args.attempt}.json'
pages_log = pages_path.with_suffix('.log')
assert not any(path.exists() for path in (live_path, pages_path, pages_log))
manifest = json.loads((reports / f'checkpoint-{args.checkpoint}-manifest.json').read_text())
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assets = {k: v for k, v in manifest['frozen_inputs_sha256'].items() if k.startswith('SafeLearning/')}
assert len(assets) == 31
stamp = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
remote_command = ['git', 'ls-remote', 'origin', 'refs/heads/main']
remote = subprocess.run(remote_command, cwd=publication, capture_output=True, text=True)
head = remote.stdout.split()[0] if remote.returncode == 0 and remote.stdout.split() else None
def fetch(item):
    name, expected = item
    url = 'https://ploxkevin.github.io/' + name + '?checkpoint=' + args.commit[:12] + '&checked=' + stamp
    record = dict(source=name, url=url, expected_sha256=expected, started_at_utc=datetime.now(timezone.utc).isoformat())
    start = time.monotonic()
    try:
        request = urllib.request.Request(url, headers={'Cache-Control': 'no-cache'})
        with urllib.request.urlopen(request, timeout=30) as response:
            record['http_status'] = response.status
            record['actual_sha256'] = hashlib.sha256(response.read()).hexdigest()
        record['matches'] = record['http_status'] == 200 and record['actual_sha256'] == expected
    except Exception as error:
        record['matches'] = False
        record['error'] = str(error)
    record.update(finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-start)
    return record
with ThreadPoolExecutor(max_workers=8) as pool:
    results = list(pool.map(fetch, sorted(assets.items())))
live_status = 'passed_all31_asset_sha256' if head == args.commit and all(r['matches'] for r in results) else 'delivery_not_yet_verified'
live = dict(commit=args.commit, remote_main=head, checked_at_utc=stamp, status=live_status, assets=results,
    remote_head_check=dict(command=remote_command, actual_workdir=str(publication), exit_code=remote.returncode, output=remote.stdout+remote.stderr),
    finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-tick)
live_path.write_text(json.dumps(live, indent=2) + '\n')
command = ['gh', 'api', 'repos/PloxKevin/ploxkevin.github.io/pages/builds/latest']
started = datetime.now(timezone.utc).isoformat()
start = time.monotonic()
pages = subprocess.run(command, cwd=publication, capture_output=True)
pages_log.write_bytes(pages.stdout+pages.stderr)
try:
    build = json.loads(pages.stdout) if pages.returncode == 0 else {}
except json.JSONDecodeError:
    build = {}
record = dict(status='passed' if pages.returncode == 0 and build.get('status') == 'built' and build.get('commit') == args.commit else 'delivery_not_yet_verified',
    command=command, actual_workdir=str(publication), exit_code=pages.returncode, started_at_utc=started,
    checked_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-start,
    log=str(pages_log.relative_to(ROOT)), log_sha256=hashlib.sha256(pages_log.read_bytes()).hexdigest(),
    build_status=build.get('status'), commit=build.get('commit'), expected_commit=args.commit)
pages_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(dict(live=live_status, matching_assets=sum(x['matches'] for x in results), pages=record['status'], remote_main=head)))
raise SystemExit(0 if live_status == 'passed_all31_asset_sha256' and record['status'] == 'passed' else 1)
