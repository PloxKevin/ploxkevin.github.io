"""Bind all48 authored opening decisions and validate byte-spliced candidates."""
import copy
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review

BASE = 'book/solutions/module-opening-step-review-v1'
FULL_BASELINE = 'book/solutions/releases/source92-opening-v1/baseline-source91'


def prose_spacing(html):
    """Polish only authored prose; keep every displayed/inline formula unchanged."""
    output = []
    for segment in re.split(r'(<[^>]+>)', html):
        if segment.startswith('<'):
            output.append(segment)
            continue
        pieces = re.split(r'(\$\$[\s\S]*?\$\$|\$[^$]*\$)', segment)
        for i, piece in enumerate(pieces):
            if i % 2 == 0:
                piece = re.sub(r'(?<=[a-z])(?=[0-9])', ' ', piece)
                if i + 1 < len(pieces) and piece and piece[-1].isalnum():
                    piece += ' '
                if i and piece and piece[0].isalnum():
                    piece = ' ' + piece
            output.append(piece)
    return ''.join(output).replace(r'\text{all200 miss}', r'\text{all 200 miss}')


def main():
    manifest = review.read(BASE + '/manifest.json')
    full = review.read(FULL_BASELINE + '/manifest.json')
    assert full['exercises'] == 556 and len(full['pages']) == 22
    protected = dict(manifest['protected_before'])
    protected[BASE + '/assemble_candidates.py'] = review.ref(BASE + '/assemble_candidates.py')['sha256']
    protected[FULL_BASELINE + '/manifest.json'] = review.ref(FULL_BASELINE + '/manifest.json')['sha256']
    full_records = []
    for page_ref in full['pages'].values():
        assert review.ref(page_ref['file']) == page_ref
        full_records.extend(review.read(page_ref['file'])['exercises'])
        protected[page_ref['file']] = page_ref['sha256']
    indexed = {r['inventory_key']: r for r in full_records}
    assert len(indexed) == len(full_records) == 556
    decisions, page_packets, splices = [], [], {}
    selected_sources = set()
    for source, baseline_ref in sorted(manifest['pages'].items()):
        baseline = review.read(baseline_ref['file'])
        assert review.ref(baseline_ref['file']) == baseline_ref
        packet_name = BASE + '/decisions/' + Path(source).stem + '-v1.json'
        packet_ref = review.ref(packet_name)
        packet = review.read(packet_name)
        assert packet['baseline'] == baseline_ref and len(packet['exercises']) == 3
        page_packets.append(packet_ref)
        protected[packet_name] = packet_ref['sha256']
        for offset, (original, authored) in enumerate(zip(baseline['exercises'], packet['exercises'])):
            row = copy.deepcopy(authored)
            key = row['inventory_key']
            complete = indexed[key]
            assert complete['ordinal'] == row['ordinal'] == offset + 1
            assert complete['source_file'] == source and complete['authoring_file'] == row['authoring_file']
            assert complete['solution']['sha256'] == row['original_solution_sha256'] == original['solution']['sha256']
            assert complete['problem']['sha256'] == row['original_problem_sha256']
            assert [h['disclosure']['sha256'] for h in complete['hints']] == row['original_hint_sha256']
            selected_sources.update([source, row['authoring_file']])
            old_authored = row['replacement_html']
            if row['decision'] == 'retain':
                assert old_authored == original['solution']['html']
                row['replacement_html'] = None
                selected = original['solution']['html']
            else:
                selected = prose_spacing(old_authored)
                row['replacement_html'] = selected
                assert review.sha(selected.encode()) != row['original_solution_sha256']
                for name, span in [(source, row['original_solution_range']),
                                   (row['authoring_file'], row['authoring_solution_range'])]:
                    if name == source and name in splices and any(v['key'] == key for v in splices[name]):
                        continue
                    splices.setdefault(name, []).append({'key': key, 'range': span, 'raw': selected.encode()})
            row['author_packet'] = packet_ref
            row['author_packet_row_index'] = offset
            row['author_packet_selected_solution_sha256'] = authored['selected_solution_sha256']
            row['authored_prose_spacing_polished'] = row['decision'] == 'replace' and selected != old_authored
            row['selected_solution_sha256'] = review.sha(selected.encode())
            row['thoroughness_rationale'] = re.sub(r'(?<=[a-z])(?=[0-9])', ' ', row['thoroughness_rationale'])
            decisions.append(row)
    assert len(decisions) == len({r['inventory_key'] for r in decisions}) == 48
    assert len(page_packets) == 16 and sum(r['decision'] == 'replace' for r in decisions) == 23
    assessment_name = BASE + '/assessments-v1.json'
    assessment = {'status': 'all48_current_module_openings_assessed_candidates_pending_independent_review',
                  'source_version': 'Source91', 'baseline': review.ref(BASE + '/manifest.json'),
                  'full556_current_baseline': review.ref(FULL_BASELINE + '/manifest.json'),
                  'author_packets': page_packets, 'counts': {'exercises': 48, 'pages': 16, 'replace': 23, 'retain': 25},
                  'exercises': decisions, 'reviewer': '/root/recovery_runner35',
                  'scope': 'Manual exercise-specific step review of the first three actual DOM exercises per non-primer page. Retain bodies are null and remain exact current bytes. Replacements are substantive inner solution bodies; prose spacing is polished without altering formulas.',
                  'independent_approval_claimed': False, 'canonical_installation_claimed': False,
                  'formal_coverage_promoted': False}
    review.json_put(assessment_name, assessment)
    checks = []
    for source in sorted(selected_sources):
        snapshot = full['source_snapshots'][source]
        assert review.ref(snapshot['file']) == snapshot
        before = review.path(snapshot['file']).read_bytes()
        assert review.ref(source)['sha256'] == snapshot['sha256']
        protected[source] = snapshot['sha256']
        spans = sorted(splices.get(source, []), key=lambda r: r['range']['start_byte'])
        cursor, fragments = 0, []
        for item in spans:
            a, b = item['range']['start_byte'], item['range']['end_byte']
            assert cursor <= a <= b <= len(before)
            fragments.extend([before[cursor:a], item['raw']])
            cursor = b
        fragments.append(before[cursor:])
        candidate = b''.join(fragments)
        check = review.validate_candidate(full, full_records, source, candidate)
        assert {r['inventory_key'] for r in check['changed_solutions']} == {r['key'] for r in spans}
        target_name = BASE + '/candidates/' + source
        if candidate == before:
            target = review.path(target_name, writable=True)
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                assert target.read_bytes() == before
            else:
                os.link(review.path(snapshot['file']), target)
        else:
            review.put(target_name, candidate)
        check['candidate'] = review.ref(target_name)
        checks.append(check)
    # Complete the31-asset local browser fixture with exact unchanged snapshots.
    # Only the selected reader files above receive byte-spliced replacements.
    for source, fingerprint in sorted(full['site_before_sha256'].items()):
        target_name = BASE + '/candidates/' + source
        if review.path(target_name).exists():
            continue
        origin = full['source_snapshots'].get(source, {'file': 'reports/solution-review/runtime-source91-selected35-v1/' + source, 'sha256': fingerprint})
        assert review.ref(origin['file'])['sha256'] == fingerprint
        target = review.path(target_name, writable=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        os.link(review.path(origin['file']), target)
    after = {n: review.ref(n)['sha256'] for n in protected}
    assert protected == after
    result = {'status': 'passed_all48_current_opening_decisions_and_solution_only_candidate_preservation',
              'assessment': review.ref(assessment_name), 'assembler': review.ref(BASE + '/assemble_candidates.py'),
              'full556_baseline': review.ref(FULL_BASELINE + '/manifest.json'), 'counts': assessment['counts'],
              'source_checks': checks, 'changed_source_files': sum(bool(c['changed_solutions']) for c in checks),
              'reader_pages': 16, 'authoring_mirrors': len(selected_sources) - 16,
              'protected_before': protected, 'protected_after': after,
              'question_hint_count_anchor_script_and_all_non_solution_bytes_preserved': True,
              'all_unselected_solution_bodies_unchanged': True, 'canonical_or_old556tracker_writes': False,
              'formal_source_correspondence_or_theorem_coverage_promoted': False,
              'scope': 'All exercise bodies on every selected reader and authoring file are parsed and compared, not only the48 openings. Candidates change exactly the manually chosen23 solutions and their authored mirrors. This structural check does not independently approve pedagogical adequacy.'}
    review.json_put(BASE + '/candidate-preservation-v1.json', result)
    print(json.dumps({'status': result['status'], 'assessment': result['assessment'], 'counts': result['counts'],
                      'changed_source_files': result['changed_source_files'], 'preservation': review.ref(BASE + '/candidate-preservation-v1.json')}))


if __name__ == '__main__':
    main()
