#!/usr/bin/env python3
"""Freeze exercise and mathematical-material source units for complete coverage.

This inventory records sources, not proof status. It deliberately does not infer
that a theorem covers an entire paragraph or an exercise from matching words.
"""
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re

from validate import Document, clean_text, exercises

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'book/coverage'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory():
    exercise_rows = []
    material_rows = []
    sources = {}
    for path in sorted((ROOT/'SafeLearning').glob('*.html')):
        relative = str(path.relative_to(ROOT))
        sources[relative] = sha(path)
        document = Document(path.read_text())
        page_exercises = exercises(document.root)
        exercise_details = []
        for node in document.root.descendants('details'):
            summary = node.child('summary')
            if summary and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',
                                    clean_text(summary.text()), re.I):
                exercise_details.append(node)
        assert len(exercise_details) == len(page_exercises)
        for ordinal, (row, node) in enumerate(zip(page_exercises, exercise_details), 1):
            locator = '#'+row['id'] if row['id'] else f'::exercise-{ordinal}'
            text = node.text()
            exercise_rows.append(dict(key=path.name+locator, source=relative,
                ordinal=ordinal, locator=locator, anchor=row['id'], line=row['line'],
                label=row['summary'], level=row['level'], source_sha256=sources[relative],
                source_text=text, text_sha256=hashlib.sha256(text.encode()).hexdigest()))

        # Record every math-bearing prose/box unit and every displayed formula.
        # Units can overlap (for example a paragraph within a theorem box).
        # Owners must split each unit into actual claims and explain exclusions.
        for ordinal, node in enumerate(document.nodes, 1):
            if node.tag not in {'p','li','div','dt','dd'}:
                continue
            classes=node.attrs.get('class','').split()
            text=node.text()
            is_formula='math-block' in classes
            is_claim_box=any(c in classes for c in ('theorem-box','definition-box','proof-box'))
            is_math_prose=node.tag in {'p','li','dt','dd'} and ('$' in text or '\\(' in text or '\\[' in text)
            if not (is_formula or is_claim_box or is_math_prose):
                continue
            locator='#'+node.attrs['id'] if node.attrs.get('id') else f'::node-{ordinal}'
            material_rows.append(dict(key=path.name+locator, source=relative,
                locator=locator, line=node.line, tag=node.tag, classes=classes,
                source_text=text, text_sha256=hashlib.sha256(text.encode()).hexdigest(),
                source_sha256=sources[relative], inventory_kind='source_unit_needs_claim_review'))
    assert len(exercise_rows)==556, len(exercise_rows)
    assert len({row['key'] for row in exercise_rows})==len(exercise_rows)
    report=dict(schema_version=1, generated_at_utc=datetime.now(timezone.utc).isoformat(),
        status='inventory_only_no_coverage_claim', source_sha256=sources,
        counts=dict(exercises=len(exercise_rows),material_source_units=len(material_rows),
                    exercises_by_page=dict(Counter(row['source'] for row in exercise_rows))),
        exercises=exercise_rows, material_source_units=material_rows,
        limits=['Source units are an exhaustive mechanically selected review queue, not automatically extracted mathematical propositions.',
                'Overlapping units must be linked to shared claims, not counted as independent proofs.',
                'Reviewers must also inspect surrounding math-free prose for mathematical assertions.',
                'Definitions, empirical assumptions, open problems and pedagogical judgments require explicit classification.'])
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'Inventoried {len(exercise_rows)} exercises and {len(material_rows)} mathematical source units on {len(sources)} pages.')


if __name__=='__main__':
    inventory()
