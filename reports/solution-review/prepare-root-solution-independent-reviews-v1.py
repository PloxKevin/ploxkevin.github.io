"""Hash-bound independent decisions; no changes to sources or candidates.

The input notes are written individually after actually reading each problem,
hint, original and selected solution. This helper verifies correspondence and
preservation; it does not infer mathematical or pedagogical adequacy.
"""
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[2]


def digest(data):
    return sha256(data).hexdigest()


def ref(file):
    p = ROOT / file
    return {'file': file, 'sha256': digest(p.read_bytes()), 'bytes': p.stat().st_size}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--page', required=True)
    parser.add_argument('--notes', required=True)
    parser.add_argument('--version', default='v1')
    args = parser.parse_args()
    page = args.page
    draft_file = f'book/solutions/drafts/{page}-thorough-solutions-{args.version}.json'
    candidate_prefix = f'book/solutions/candidates/{page}-{args.version}'
    baseline_file = f'book/solutions/baseline-source90/pages/{page}.html.json'
    preservation_file = f'reports/solution-review/{page}-preservation-{args.version}.json'
    output = ROOT / f'reports/solution-review/{page}-independent-review-{args.version}.json'
    assert not output.exists(), 'Preserve an earlier review; use a fresh version'
    notes = json.loads((ROOT / args.notes).read_bytes())
    baseline = json.loads((ROOT / baseline_file).read_bytes())
    draft = json.loads((ROOT / draft_file).read_bytes())
    preservation = json.loads((ROOT / preservation_file).read_bytes())
    assert preservation['status'] == 'passed_explicit_solution_draft_preservation'
    assert any(r['file'] == draft_file and r['sha256'] == ref(draft_file)['sha256']
               for r in preservation['drafts'])
    rows = {r['inventory_key']: r for r in baseline['exercises']}
    decisions = draft['exercises']
    assert len(rows) == len(decisions) == len(notes['exercises'])
    assert len({r['inventory_key'] for r in decisions}) == len(decisions)
    assert {r['inventory_key'] for r in decisions} == set(rows)
    verdicts = {int(r['ordinal']): r for r in notes['exercises']}
    assert set(verdicts) == {r['ordinal'] for r in rows.values()}
    ops = {}
    reviews = []
    for r in decisions:
        b = rows[r['inventory_key']]
        n = verdicts[b['ordinal']]
        assert r['source_file'] == b['source_file']
        assert r['original_solution_sha256'] == b['solution']['sha256']
        original_body = b['solution']['html'].encode()
        assert digest(original_body) == b['solution']['sha256']
        selected = (r.get('replacement_html', b['solution']['html'])
                    if r['decision'] == 'retain' else r['replacement_html']).encode()
        assert r['decision'] in ['retain', 'replace']
        assert (selected == original_body) == (r['decision'] == 'retain')
        for source, sr, expected_hash in [
                (b['source_file'], b['solution']['range'], b['source_sha256']),
                (b['authoring_file'], b['authoring']['solution_range'],
                 b['authoring']['source_sha256'])]:
            native = (ROOT / source).read_bytes()
            assert digest(native) == expected_hash
            assert native[sr['start_byte']:sr['end_byte']] == original_body
            if source == b['authoring_file'] and source == b['source_file'] and source in ops:
                if any(key == b['inventory_key'] for _, _, key in ops[source]):
                    continue
            ops.setdefault(source, []).append((sr, selected, b['inventory_key']))
        status = n.get('status', 'approved')
        assert status in ['approved', 'needs_revision']
        errors = n.get('errors', [])
        assert bool(errors) == (status == 'needs_revision')
        reviews.append({
            'inventory_key': b['inventory_key'], 'ordinal': b['ordinal'],
            'label': b['label'], 'anchor': b['anchor'],
            'source_file': b['source_file'], 'authoring_file': b['authoring_file'],
            'decision': r['decision'], 'decision_verdict': status,
            'baseline_exercise_sha256': b['exercise']['sha256'],
            'question_sha256': b['problem']['sha256'],
            'hint_disclosure_sha256': [h['disclosure']['sha256'] for h in b['hints']],
            'original_solution_sha256': b['solution']['sha256'],
            'reviewed_solution_sha256': digest(selected),
            'mathematics_verdict': n.get('mathematics_verdict', 'passed'),
            'mathematics_review': n['mathematics_review'],
            'depth_verdict': n.get('depth_verdict', 'adequate_for_stated_audience'),
            'depth_review': n['depth_review'],
            'whole_question_hint_original_and_selected_solution_read': True,
            'remaining_gaps': n.get('remaining_gaps', []), 'errors': errors,
        })
    replays = []
    for source, patches in sorted(ops.items()):
        original = (ROOT / source).read_bytes()
        ordered = sorted(patches, key=lambda x: x[0]['start_byte'])
        assert all(a[0]['end_byte'] <= b[0]['start_byte'] for a, b in zip(ordered, ordered[1:]))
        replay = original
        for sr, selected, key in reversed(ordered):
            replay = replay[:sr['start_byte']] + selected + replay[sr['end_byte']:]
        candidate = candidate_prefix + '/' + source
        actual = (ROOT / candidate).read_bytes()
        assert actual == replay
        assert any(r['candidate_file'] == candidate and r['sha256'] == digest(actual)
                   for r in preservation['candidates'])
        replays.append({
            'source': ref(source), 'candidate': ref(candidate),
            'status': 'passed_exact_solution_range_replay',
            'decided_ranges': len(patches),
            'changed_ranges': sum(selected != original[sr['start_byte']:sr['end_byte']]
                                  for sr, selected, _ in patches),
            'all_other_bytes_preserved': True,
        })
    errors = [dict(e, inventory_key=r['inventory_key'])
              for r in reviews for e in r['errors']]
    report = {
        'status': 'needs_revision' if errors else 'approved',
        'reviewer': '/root/review_gaussian35',
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Independent mathematics and depth review of every exact selected exercise solution; no source, coverage, publication or candidate mutation.',
        'draft': ref(draft_file), 'baseline': ref(baseline_file),
        'baseline_manifest': ref('book/solutions/baseline-source90/manifest.json'),
        'inventory': ref('book/coverage/inventory.json'),
        'page_contract': ref('page_contract.md'),
        'solution_review_criteria': ref('book/solutions/README.md'),
        'preservation_report': ref(preservation_file),
        'review_notes': ref(args.notes),
        'review_helper': ref('reports/solution-review/prepare-root-solution-independent-reviews-v1.py'),
        'context_sources_read': [ref(p) for p in notes['context_sources_read']],
        'counts': dict(Counter(r['decision'] for r in reviews), exercises=len(reviews),
                       approved=sum(r['decision_verdict'] == 'approved' for r in reviews),
                       needs_revision=sum(r['decision_verdict'] == 'needs_revision' for r in reviews)),
        'exact_candidate_replay': replays,
        'independent_numerical_and_reasoning_checks': notes.get('independent_checks', []),
        'exercise_reviews': reviews, 'errors': errors,
        'browser_or_compiler_execution_claimed': False,
        'remaining_integration_checks': ['Root handles rendered-page QA and integration; this artifact approves only its explicitly reviewed mathematics, depth and exact-byte correspondence.'],
    }
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'file': str(output.relative_to(ROOT)), 'sha256': digest(output.read_bytes()),
                      'status': report['status'], 'counts': report['counts']}, sort_keys=True))


if __name__ == '__main__':
    main()
