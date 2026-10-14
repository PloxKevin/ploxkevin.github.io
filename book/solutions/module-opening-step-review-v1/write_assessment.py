"""Bind manually authored decisions to the exact current opening extraction."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review

BASE = 'book/solutions/module-opening-step-review-v1'


def write_page(page, authored):
    baseline_name = BASE + '/pages/' + page + '.html.json'
    baseline = review.read(baseline_name)
    rows = baseline['exercises']
    assert len(authored) == len(rows) == 3
    decisions = []
    for original, choice in zip(rows, authored):
        assert choice['inventory_key'] == original['inventory_key']
        assert choice['decision'] in {'retain', 'replace'}
        assert choice['thoroughness_rationale'].strip()
        body = choice.get('replacement_html', original['solution']['html'])
        assert body.strip()
        assert (body == original['solution']['html']) == (choice['decision'] == 'retain')
        assert review.ref(original['current_source']['file']) == original['current_source']
        assert review.ref(original['authoring_source']['file']) == original['authoring_source']
        decisions.append({'inventory_key': original['inventory_key'], 'source_file': original['source_file'],
                          'ordinal': original['ordinal'], 'label': original['label'], 'anchor': original['anchor'],
                          'current_source': original['current_source'], 'authoring_source': original['authoring_source'],
                          'authoring_file': original['authoring_file'], 'original_solution_sha256': original['solution']['sha256'],
                          'original_problem_sha256': original['problem']['sha256'],
                          'original_hint_sha256': [h['disclosure']['sha256'] for h in original['hints']],
                          'original_solution_range': original['solution']['range'],
                          'authoring_solution_range': original['authoring_solution_range'],
                          'solution_container_kind': original['solution']['container_kind'],
                          'decision': choice['decision'], 'thoroughness_rationale': choice['thoroughness_rationale'],
                          'selected_solution_sha256': review.sha(body.encode()),
                          'replacement_html': body, 'status': 'manual_step_review_candidate_pending_independent_review'})
    name = BASE + '/decisions/' + page + '-v1.json'
    review.json_put(name, {'status': 'all3_current_openings_manually_assessed_candidates_pending_independent_review',
                           'baseline': review.ref(baseline_name), 'page_contract': review.ref('page_contract.md'),
                           'reviewer': '/root/recovery_runner35', 'exercises': decisions,
                           'pedagogical_review_basis': 'Actual method, notation/assumptions, intermediate reasoning, requested cases and result interpretation; no length metric.',
                           'formal_coverage_or_canonical_installation_claimed': False})
    return review.ref(name)
