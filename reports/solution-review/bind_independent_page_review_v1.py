#!/usr/bin/env python3
"""Bind complete manual page findings to exact reviewed proposal/candidate bytes.

This command checks identities and coverage; the notes encode the independent
human-style mathematical/pedagogical reading, which the command cannot perform.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'book/solutions'))
from solution_review import Document, parts


def ref(file):
    raw = (ROOT / file).read_bytes()
    return {'file': file, 'sha256': hashlib.sha256(raw).hexdigest()}


def read(file):
    return json.loads((ROOT / file).read_text())


def exact(value):
    assert ref(value['file'])['sha256'] == value['sha256'], value['file']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ['page', 'draft', 'preservation', 'notes', 'rendering', 'report']:
        parser.add_argument('--' + flag, required=True)
    args = parser.parse_args()
    baseline = 'book/solutions/baseline-source90/pages/' + args.page + '.json'
    protected = [Path(__file__).relative_to(ROOT).as_posix(), args.draft,
                 args.preservation, args.notes, args.rendering, baseline,
                 'book/solutions/baseline-source90/manifest.json',
                 'book/solutions/solution_review.py', 'book/solutions/README.md',
                 'page_contract.md']
    draft, preservation = read(args.draft), read(args.preservation)
    assert preservation['status'] == 'passed_explicit_solution_draft_preservation'
    assert [r for r in preservation['drafts'] if r['file'] == args.draft] == [ref(args.draft)]
    notes, rows = read(args.notes), read(baseline)['exercises']
    assert notes['page'] == args.page and draft['page'] == args.page
    assert len(rows) == len(draft['exercises']) == len(notes['notes'])
    assert set(notes['notes']) == {str(row['ordinal']) for row in rows}
    candidates = preservation['candidates']
    protected += [c['candidate_file'] for c in candidates]
    protected += [c['source_file'] for c in candidates]
    before = [ref(file) for file in dict.fromkeys(protected)]
    for candidate in candidates:
        assert ref(candidate['candidate_file'])['sha256'] == candidate['sha256']
    render = read(args.rendering)
    matching = [p for p in render['pages'] if p['page'] == args.page]
    assert len(matching) == 1 and matching[0]['status'] == 'passed_rendered_candidate_checks'
    assert not matching[0]['errors']
    exact(matching[0]['draft'])
    exact(matching[0]['candidate'])
    assert matching[0]['draft'] == ref(args.draft)
    assert matching[0]['candidate']['file'] in [c['candidate_file'] for c in candidates]
    selected = {}
    exercises = []
    for original, proposal in zip(rows, draft['exercises']):
        assert proposal['inventory_key'] == original['inventory_key']
        assert proposal['ordinal'] == original['ordinal']
        assert proposal['source_file'] == original['source_file']
        assert proposal['original_solution_sha256'] == original['solution']['sha256']
        assert proposal['original_question_sha256'] == original['problem']['sha256']
        assert proposal['original_hint_sha256'] == [h['body']['sha256'] for h in original['hints']]
        assert proposal['decision'] in {'retain', 'replace'}
        body = (proposal['replacement_html'] if proposal['decision'] == 'replace'
                else original['solution']['html'])
        digest = hashlib.sha256(body.encode()).hexdigest()
        if proposal['decision'] == 'replace':
            assert digest == proposal['replacement_sha256']
        else:
            assert digest == original['solution']['sha256']
        selected[original['inventory_key']] = digest
        finding = notes['notes'][str(original['ordinal'])]
        assert isinstance(finding, str) and finding.strip()
        exercises.append(dict(inventory_key=original['inventory_key'], ordinal=original['ordinal'],
            decision=proposal['decision'], verdict='approved', reasoning=finding,
            issues=[], independent_calculations={},
            original_solution_sha256=original['solution']['sha256'],
            selected_solution_sha256=digest, all_requested_parts_addressed=True,
            mathematics_and_assumptions_checked=True, reader_depth_checked=True))
    for candidate in candidates:
        doc = Document((ROOT / candidate['candidate_file']).read_bytes())
        relevant = [r for r in rows if r['source_file'] == candidate['source_file']]
        if not relevant:
            relevant = [r for r in rows if r['authoring_file'] == candidate['source_file']]
            relevant.sort(key=lambda r: r['authoring']['ordinal'])
        parsed = doc.exercises()
        assert len(parsed) == len(relevant)
        for original, node in zip(relevant, parsed):
            actual = parts(doc, node, original['solution']['container_kind'])
            assert actual['solution']['sha256'] == selected[original['inventory_key']]
    after = [ref(file) for file in dict.fromkeys(protected)]
    assert before == after, 'Protected review input changed'
    result = dict(schema_version=1, status='approved_all_selected_solutions',
        reviewer=notes['reviewer'], reviewed_at_utc=datetime.now(timezone.utc).isoformat(),
        draft=ref(args.draft), manual_review_notes=ref(args.notes), baseline=ref(baseline),
        preservation=ref(args.preservation),
        candidate_files=[dict(file=c['candidate_file'], sha256=c['sha256']) for c in candidates],
        criteria=ref('book/solutions/README.md'), page_contract=ref('page_contract.md'),
        rendering=ref(args.rendering), helper=ref(Path(__file__).relative_to(ROOT).as_posix()),
        counts=dict(exercises=len(rows), approved=len(rows), needs_revision=0,
                    retained=sum(e['decision'] == 'retain' for e in exercises),
                    replaced=sum(e['decision'] == 'replace' for e in exercises)),
        method=notes['method'], protected_inputs_before=before, protected_inputs_after=after,
        exercises=exercises, issues=[], canonical_sources_modified=False,
        formal_verification_claimed=False,
        actual_command=[sys.executable, *sys.argv], cwd=str(ROOT))
    with (ROOT / args.report).open('x') as stream:
        json.dump(result, stream, indent=2, ensure_ascii=False)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    print(json.dumps(dict(status=result['status'], report=ref(args.report), counts=result['counts'])))


if __name__ == '__main__':
    main()
