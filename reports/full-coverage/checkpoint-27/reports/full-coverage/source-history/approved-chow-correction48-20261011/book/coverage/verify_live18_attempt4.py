#!/usr/bin/env python3
"""Check every frozen book asset over HTTP and record the actual Pages build response."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('checkpoint', type=int)
parser.add_argument('commit')
args = parser.parse_args()
n = args.checkpoint
reports = ROOT / 'reports/full-coverage'
publication = ROOT / 'reports/book/publication-repo'
manifest = json.loads((reports / f'checkpoint-{n}-manifest.json').read_text())
assets = {k: v for k, v in manifest['frozen_inputs_sha256'].items() if k.startswith('SafeLearning/')}
if len(assets) != 31:
    raise ValueError('Expected all31 frozen book assets.')
remote_command = ['git', 'ls-remote', 'origin', 'refs/heads/main']
remote = subprocess.run(remote_command, cwd=publication, capture_output=True, text=True)
head = remote.stdout.split()[0] if remote.returncode == 0 and remote.stdout.split() else None
stamp = datetime.now(timezone.utc).isoformat()


def fetch(item):
    name, expected = item
    url = 'https://ploxkevin.github.io/' + name + '?checkpoint=' + args.commit[:12] + '&checked=' + stamp
    record = {'source': name, 'url': url, 'expected_sha256': expected}
    try:
        request = urllib.request.Request(url, headers={'Cache-Control': 'no-cache'})
        with urllib.request.urlopen(request, timeout=30) as response:
            record['http_status'] = response.status
            record['actual_sha256'] = hashlib.sha256(response.read()).hexdigest()
        record['matches'] = record['http_status'] == 200 and record['actual_sha256'] == expected
    except Exception as error:
        record['matches'] = False
        record['error'] = str(error)
    return record


with ThreadPoolExecutor(max_workers=8) as pool:
    results = list(pool.map(fetch, sorted(assets.items())))
live = {'commit': args.commit, 'remote_main': head, 'checked_at_utc': stamp,
        'status': 'passed_all31_asset_sha256' if head == args.commit and all(r['matches'] for r in results)
        else 'delivery_not_yet_verified', 'assets': results,
        'remote_head_check': {'command': remote_command, 'actual_workdir': str(publication),
                              'exit_code': remote.returncode, 'output': remote.stdout + remote.stderr}}
(reports / f'live-checkpoint-{n}-attempt4.json').write_text(json.dumps(live, indent=2) + '\n')
pages_command = ['gh', 'api', 'repos/PloxKevin/ploxkevin.github.io/pages/builds/latest']
pages = subprocess.run(pages_command, cwd=publication, capture_output=True)
log = reports / f'pages-checkpoint-{n}-attempt4.log'
log.write_bytes(pages.stdout + pages.stderr)
try:
    build = json.loads(pages.stdout) if pages.returncode == 0 else {}
except json.JSONDecodeError:
    build = {}
record = {'status': 'passed' if pages.returncode == 0 and build.get('status') == 'built'
          and build.get('commit') == args.commit else 'delivery_not_yet_verified',
          'command': pages_command, 'actual_workdir': str(publication), 'exit_code': pages.returncode,
          'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'log': str(log.relative_to(ROOT)),
          'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'build_status': build.get('status'),
          'commit': build.get('commit'), 'expected_commit': args.commit,
          'limits': ['Actual Pages API response; separate HTTP checks verify31asset bytes.']}
(reports / f'pages-checkpoint-{n}-attempt4.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'live': live['status'], 'matching_assets': sum(x['matches'] for x in results),
                  'pages': record['status'], 'remote_main': head}, indent=2))
raise SystemExit(0 if live['status'] == 'passed_all31_asset_sha256' and record['status'] == 'passed' else 1)
