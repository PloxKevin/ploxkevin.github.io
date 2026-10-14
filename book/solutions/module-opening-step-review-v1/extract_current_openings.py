"""Freeze the first three current Source91 exercises on each non-primer page."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review

BASE = 'book/solutions/module-opening-step-review-v1'
INVENTORY = 'book/solutions/releases/source91-v1/source91-inventory/inventory.json'
PLAN = 'book/solutions/releases/source91-v1/plan.json'


def main():
    inventory, release = review.read(INVENTORY), review.read(PLAN)
    snapshots = {r['file']: r['after'] for r in release['files']}
    pages = sorted(n for n in inventory['counts']['exercises_by_page'] if not Path(n).name.startswith('primer-'))
    assert len(pages) == 16
    protected = {n: review.ref(n)['sha256'] for n in release['site_source91_sha256']}
    assert protected == release['site_source91_sha256']
    for name in [INVENTORY, PLAN, 'page_contract.md', 'book/solutions/solution_review.py',
                 'book/solutions/baseline-source90/review-tracker.json', BASE + '/extract_current_openings.py']:
        protected[name] = review.ref(name)['sha256']
    baseline_pages = {}
    cached = {}

    def document(name):
        if name not in cached:
            raw = review.path(name).read_bytes()
            protected[name] = review.sha(raw)
            assert protected[name] == snapshots[name]['sha256']
            assert review.ref(snapshots[name]['file'])['sha256'] == protected[name]
            cached[name] = review.Document(raw)
        return cached[name]

    for source in pages:
        doc = document(source)
        nodes = doc.exercises()
        inventory_rows = [r for r in inventory['exercises'] if r['source'] == source]
        assert len(nodes) == len(inventory_rows) == inventory['counts']['exercises_by_page'][source]
        rows = []
        for ordinal, (node, original) in enumerate(zip(nodes[:3], inventory_rows[:3]), 1):
            assert original['ordinal'] == ordinal
            assert original['label'] == review.clean(node.child('summary').text())
            assert original['anchor'] == node.attrs.get('id')
            text = node.text().replace('\r\n', '\n').replace('\r', '\n')
            assert review.sha(text.encode()) == original['text_sha256']
            item = review.parts(doc, node)
            authored = review.author_file(source, doc, node)
            authored_doc = document(authored)
            if authored == source:
                author_ordinal, author_node = ordinal, node
            else:
                matches = [(i, n) for i, n in enumerate(authored_doc.exercises(), 1) if n.attrs.get('id') == original['anchor']]
                assert len(matches) == 1
                author_ordinal, author_node = matches[0]
            author_parts = review.parts(authored_doc, author_node)
            assert item['exercise']['html'] == author_parts['exercise']['html']
            rows.append({'inventory_key': original['key'], 'source_file': source, 'ordinal': ordinal,
                         'anchor': original['anchor'], 'label': original['label'],
                         'current_source': review.ref(source), 'source_snapshot': snapshots[source],
                         'authoring_file': authored, 'authoring_source': review.ref(authored),
                         'authoring_snapshot': snapshots[authored], 'authoring_ordinal': author_ordinal,
                         'authoring_solution_range': author_parts['solution']['range'],
                         'inventory_text_sha256': original['text_sha256'], **item})
        name = BASE + '/pages/' + Path(source).name + '.json'
        review.json_put(name, {'status': 'current_source91_openings_pending_step_review',
                               'inventory': review.ref(INVENTORY), 'current_source': review.ref(source),
                               'whole_page_exercise_count': len(nodes), 'exercises': rows})
        baseline_pages[source] = review.ref(name)
    after = {n: review.ref(n)['sha256'] for n in protected}
    assert protected == after
    manifest = {'status': 'exact48_current_source91_module_openings_pending_review', 'source_version': 'Source91',
                'inventory': review.ref(INVENTORY), 'release_plan': review.ref(PLAN),
                'extractor': review.ref(BASE + '/extract_current_openings.py'),
                'page_contract': review.ref('page_contract.md'), 'pages': baseline_pages,
                'exercise_count': 48, 'page_count': 16, 'first_exercises_per_page': 3,
                'selection_definition': 'First three exercise details in actual document order, cross-checked against current Source91 inventory ordinals.',
                'protected_before': protected, 'protected_after': after,
                'source_snapshots_reused': True, 'canonical_or_authoring_or_old_tracker_writes': False,
                'formal_coverage_or_pedagogical_approval_claimed': False}
    review.json_put(BASE + '/manifest.json', manifest)
    print(json.dumps({'status': manifest['status'], 'exercises': 48, 'pages': 16,
                      'manifest': review.ref(BASE + '/manifest.json')}))


if __name__ == '__main__':
    main()
