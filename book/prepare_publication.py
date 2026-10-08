#!/usr/bin/env python3
"""Prepare and locally verify a site-only patch without editing the publish repo."""
from datetime import datetime, timezone
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT/'reports/book/baseline'
SITE = ROOT/'SafeLearning'
OUT = ROOT/'reports/book'
plan = json.loads((OUT/'plan.json').read_text())
publication = json.loads((ROOT/'reports/lean-verification/publication.json').read_text())
assert publication['status'] == 'passed'
published_files = {Path(row['file']).name: row for row in publication['files']}
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for name, digest in plan['baseline_sha256'].items():
    assert sha(BASE/name) == digest, ('baseline modified', name)
    prior = published_files[name]
    assert prior['expected_sha256'] == prior['actual_sha256'] == digest, ('historical publication mismatch', name)

chunks = []
changed = []
site_files = sorted(p for p in SITE.iterdir() if p.suffix in {'.html', '.css', '.js'})
for path in site_files:
    original = BASE/path.name
    before = original.read_text() if original.exists() else ''
    after = path.read_text()
    if before == after:
        continue
    name = 'SafeLearning/'+path.name
    chunks.append(f'diff --git a/{name} b/{name}\n')
    if not original.exists():
        chunks.append('new file mode 100644\n')
    chunks.extend(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
                                      fromfile='a/'+name if original.exists() else '/dev/null',
                                      tofile='b/'+name))
    changed.append(name)
patch = OUT/'publication-changes.patch'
patch.write_text(''.join(chunks))
with tempfile.TemporaryDirectory(prefix='safelearning-publication-', dir='/tmp') as temp:
    staging = Path(temp)
    subprocess.run(['git', 'init', '-q', temp], check=True)
    shutil.copytree(BASE, staging/'SafeLearning')
    subprocess.run(['git', '-C', temp, 'apply', '--check', str(patch)], check=True)
    subprocess.run(['git', '-C', temp, 'apply', str(patch)], check=True)
    for path in site_files:
        assert sha(staging/'SafeLearning'/path.name) == sha(path), path.name

report = dict(status='prepared_and_locally_verified_not_pushed',
              prepared_at_utc=datetime.now(timezone.utc).isoformat(),
              baseline_recorded_published_commit=publication['commit'],
              baseline_provenance='Baseline hashes match the recorded October 7 publication HTTP checks in reports/lean-verification/publication.json; remote HEAD is not rechecked here.',
              patch=str(patch.relative_to(ROOT)), patch_sha256=sha(patch), changed_files=changed,
              source_sha256={str(p.relative_to(ROOT)): sha(p) for p in site_files},
              local_check='git apply --check, application in disposable checkout, exact SHA-256 comparison of all site files',
              remote_status='Unavailable: GitHub DNS resolution failed; see remote-check.log.',
              browser_status='Blocked before launch by sandbox; see browser-attempt.log.',
              limits=['No publishing checkout was modified and no commit was pushed.',
                      'Rendered browser/print QA and live-site checks remain pending.'])
(OUT/'publication-preparation.json').write_text(json.dumps(report, indent=2)+'\n')
print(f'Prepared site patch: {len(changed)} files; exact local application check passed. Not pushed.')
