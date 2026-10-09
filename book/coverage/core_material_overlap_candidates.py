#!/usr/bin/env python3
"""Propose exact DOM overlaps with fully reviewed exercises; do not close claims."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path,
                    default=ROOT/'book/coverage/core-material-overlap-candidates.json')
args = parser.parse_args()
spec = importlib.util.spec_from_file_location('book_static_validator', ROOT / 'book/validate.py')
static = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = static
spec.loader.exec_module(static)
inventory = json.loads((ROOT / 'book/coverage/inventory.json').read_text())
ledger = json.loads((ROOT / 'book/coverage/core.json').read_text())
complete = {e['inventory_key']: e for e in ledger['exercises'] if e['status'] == 'complete_math'}
units = {u['key']: u for u in inventory['material_source_units']}
records = []
for source in ledger['scope_pages']:
    text = (ROOT / source).read_text()
    if hashlib.sha256(text.encode()).hexdigest() != inventory['source_sha256'][source]:
        raise ValueError('Inventory source changed: ' + source)
    document = static.Document(text)
    exercise_nodes = [node for node in document.root.descendants('details')
                      if node.child('summary') and re.match(
                          r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',
                          static.clean_text(node.child('summary').text()), re.I)]
    for ordinal, exercise in enumerate(exercise_nodes, 1):
        locator = '#' + exercise.attrs['id'] if exercise.attrs.get('id') else f'::exercise-{ordinal}'
        key = Path(source).name + locator
        if key not in complete:
            continue
        owner = complete[key]
        if hashlib.sha256(exercise.text().encode()).hexdigest() != owner['text_sha256']:
            raise ValueError('Exercise source differs: ' + key)
        descendant_ids = {id(node) for node in exercise.descendants()}
        for index, node in enumerate(document.nodes, 1):
            if id(node) not in descendant_ids:
                continue
            unit_locator = '#' + node.attrs['id'] if node.attrs.get('id') else f'::node-{index}'
            unit_key = Path(source).name + unit_locator
            unit = units.get(unit_key)
            if unit is None:
                continue
            if node.text() != unit['source_text']:
                raise ValueError('Material node differs: ' + unit_key)
            records.append({
                'source_unit_key': unit_key, 'exercise_key': key,
                'source': source, 'source_sha256': inventory['source_sha256'][source],
                'unit_text_sha256': unit['text_sha256'], 'exercise_text_sha256': owner['text_sha256'],
                'unit_tag': unit['tag'], 'unit_classes': unit['classes'],
                'inventory_kind': unit['inventory_kind'],
                'unit_source_text': unit['source_text'], 'exercise_source_text': owner['source_text'],
                'reviewed_exercise_claims': owner['claims'], 'status': 'pending_overlap_correspondence_review'})
out = {'status': 'candidates_only_no_new_coverage_claim',
       'scope': 'Physical DOM descendants of complete_math core exercises with exact source hashes.',
       'records': records}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(out, indent=2) + '\n')
print(f'Proposed {len(records)} exact DOM-overlap source units; no claims promoted.')
