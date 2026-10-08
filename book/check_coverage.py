#!/usr/bin/env python3
"""Validate current source fingerprints and an explicitly partial book ledger."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

from validate import Document, exercises

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'reports/book'


def read(path):
    return json.loads((ROOT/path).read_text())


def sha(path):
    return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()


def references(value):
    if isinstance(value, dict):
        for child in value.values():
            yield from references(child)
    elif isinstance(value, list):
        for child in value:
            yield from references(child)
    elif isinstance(value, str) and re.fullmatch(r'SafeLearning\.[\w.]+', value):
        yield value


formal = read('reports/book/lean-verification/verification.json')
assert formal['status'] == 'passed'
names = {d['name'] for d in formal['declarations']}
for path, expected in (formal['source_sha256'] | formal['proof_sha256'] | formal['project_sha256']).items():
    assert sha(path) == expected, ('stale formal fingerprint', path)

integration = read('book/review/integration.json')
assert integration['status'] == 'PASS' and not integration['errors']
for path, expected in integration['page_source_sha256'].items():
    assert sha('SafeLearning/'+path) == expected, ('stale integration fingerprint', path)
assert all(row['original_teaching_body_byte_identical'] for row in integration['teaching_page_preservation'])
for chapter in integration['chapter_labs']:
    assert sha(chapter['fragment']) == chapter['source_sha256'], ('stale chapter fragment', chapter['fragment'])
for document in integration['new_reference_source_documents']:
    assert sha(document['file']) == document['sha256'], ('stale reference fragment', document['file'])

legacy = []
for filename in ['primers-foundations-coverage.json', 'applied-coverage.json',
                 'modules-coverage.json', 'core-coverage.json', 'core-original-coverage.json']:
    data = read('reports/lean-verification/'+filename)
    rows = data.get('exercises', data.get('items'))
    assert isinstance(rows, list)
    assert not (set(references(data))-names), filename
    legacy.append(dict(file='reports/lean-verification/'+filename, count=len(rows)))
assert sum(row['count'] for row in legacy) == 489

mapping = read('book/review/new-formal-map.json')
assert sha(mapping['lean_file']) == mapping['sha256']
assert len(mapping['theorems']) == mapping['theorem_count'] == 26
by_anchor = {}
for theorem in mapping['theorems']:
    assert theorem['theorem'] in names
    for anchor in theorem['source_anchors']:
        filename, target = anchor.split('#', 1)
        assert target in Document((ROOT/filename).read_text()).ids, anchor
        by_anchor.setdefault(anchor, []).append(theorem['theorem'])

rows = []
for chapter in integration['chapter_labs']:
    for exercise in chapter['new_exercises']:
        rows.append(dict(source=chapter['fragment'], site='SafeLearning/'+chapter['file'], **exercise))
for exercise in exercises(Document((ROOT/'book/case-studies.html').read_text()).root):
    rows.append(dict(source='book/case-studies.html', site='SafeLearning/case-studies.html', **exercise))
assert len(rows) == 67
for row in rows:
    row['source_anchor'] = row['source']+'#'+row['id']
    row['site_anchor'] = row['site']+'#'+row['id']
    row['lean_declarations'] = by_anchor.get(row['source_anchor'], [])
    row['formal_coverage'] = 'partial' if row['lean_declarations'] else 'not_formalized_in_this_audit'
    row['limits'] = ('Mapped general implications require their stated hypotheses and do not encode the entire '
                    'exercise, numeric instantiation, physical validity or prose interpretation.'
                    if row['lean_declarations'] else
                    'Arithmetic and independent source review provide separate evidence; no complete Lean '
                    'correspondence is claimed for this exercise.')

report = dict(status='passed', checked_at_utc=datetime.now(timezone.utc).isoformat(),
              original_exercises=489, new_exercises=67, current_exercises=556,
              original_coverage_ledgers=legacy, theorem_declarations=formal['theorem_count'],
              new_theorem_declarations=mapping['theorem_count'],
              new_exercise_formal_status_counts=dict(Counter(row['formal_coverage'] for row in rows)),
              exercises=rows, selected_new_theorem_map='book/review/new-formal-map.json',
              source_sha256={path: sha(path) for path in sorted({row['source'] for row in rows} |
                  {'book/frontmatter.html', 'book/glossary.html', 'book/review/new-formal-map.json',
                   'book/review/integration.json'})},
              limits=['The original 489 exercise bodies are byte-preserved after removing book insertions.',
                      'Valid names and complete inventories do not prove semantic correspondence.',
                      'A theorem count is not a count of fully verified exercises.',
                      'Rendered behavior is checked separately in reports/book/browser-final.json and the visual reviews.'])
(OUT/'coverage.json').write_text(json.dumps(report, indent=2)+'\n')
print(f'Coverage integrity passed: 489 preserved + 67 new exercises; {formal["theorem_count"]} Lean declarations.')
