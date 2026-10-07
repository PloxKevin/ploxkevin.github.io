#!/usr/bin/env python3
"""Check the exercise ledgers against the final Lean and browser fingerprints."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'reports/lean-verification'
formal = json.loads((OUT / 'verification.json').read_text())
assert formal['status'] == 'passed'
names = {d['name'] for d in formal['declarations']}
for path, expected in (formal['source_sha256'] | formal['proof_sha256'] |
                       formal['project_sha256']).items():
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path

def references(value):
    if isinstance(value, dict):
        for v in value.values():
            yield from references(v)
    elif isinstance(value, list):
        for v in value:
            yield from references(v)
    elif isinstance(value, str) and re.fullmatch(r'SafeLearning\.[\w.]+', value):
        yield value

files = ['primers-foundations-coverage.json', 'applied-coverage.json',
         'modules-coverage.json', 'core-coverage.json', 'core-original-coverage.json']
ledgers = []
for filename in files:
    data = json.loads((OUT / filename).read_text())
    rows = data.get('exercises', data.get('items'))
    assert isinstance(rows, list), filename
    unknown = set(references(data)) - names
    assert not unknown, (filename, unknown)
    ledgers.append(dict(file=filename, exercise_count=len(rows),
                        statuses=dict(Counter(row.get('status', row.get('formal_coverage'))
                                              for row in rows))))
assert sum(d['exercise_count'] for d in ledgers) == 489, ledgers

browser = json.loads((OUT / 'browser-final.json').read_text())
assert len(browser) == 26 and not any(row['errors'] for row in browser)
assert sum(row['exerciseCounts']['total'] for row in browser) == 489
for row in browser:
    assert row['source_sha256'] == formal['source_sha256']['SafeLearning/' + row['file']]

report = dict(status='passed', exercises_catalogued=489,
              formal_theorem_declarations=formal['theorem_count'], coverage=ledgers,
              browser_pages=26, limits='Ledger completeness and valid declaration names do not '
              'prove semantic correspondence or complete exercise coverage. Read each row\u0027s limits.')
(OUT / 'coverage-integrity.json').write_text(json.dumps(report, indent=2) + '\n')
print('Coverage and source fingerprints match:', formal['theorem_count'], 'theorems;489 exercises.')
