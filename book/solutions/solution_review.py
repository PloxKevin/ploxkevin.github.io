"""Freeze exercise solutions and validate exact solution-only candidate changes.

The baseline is a review queue, not an adequacy score. No canonical page is edited.
Ranges use UTF-8 byte offsets, zero based, with an exclusive end. Line/column
locations are one based/zero based respectively. HTML is sliced, never serialized.
"""
from collections import Counter
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
import argparse
import bisect
import hashlib
import json
import os
import re
import sys
import tempfile

SELF = Path(__file__).resolve()
ROOT = SELF.parents[2]
BASELINE = 'book/solutions/baseline-source90'
INVENTORY = 'book/coverage/inventory.json'
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}
EXERCISE = re.compile(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)', re.I)
RUBRIC = {
    'audience': 'A student with first-course linear algebra and single-variable calculus; explain any additional prerequisites used.',
    'common': {
        'method_explained': 'State the approach and why it answers the question before carrying it out.',
        'assumptions_and_notation': 'Identify the data, units, symbols, hypotheses and the scope of the conclusion.',
        'intermediate_work': 'Show substitutions, intermediate algebra/calculations or the logical bridge between claims.',
        'reasons_for_steps': 'Explain the rule, theorem or assumption that justifies each substantive step.',
        'result_interpretation': 'Answer every requested part and explain the result, limiting cases and certificate limits where relevant.'},
    'alternatives': {
        'calculation': 'Write the starting formula, substitute the actual data, expand intermediate arithmetic/algebra, check the result and units.',
        'proof': 'State hypotheses and the goal, organize the implication, justify each inference, handle boundary cases, and conclude precisely.',
        'conceptual': 'Explain the distinction or mechanism in plain language; give a concrete example/counterexample and connect it to the question.',
        'algorithm': 'Identify inputs and the update rule, work through the requested steps, and explain feasibility, termination or failure conditions.',
        'application': 'Connect the mathematical model to the decision, track uncertainty and units, and distinguish assumptions from certified conclusions.'},
    'decision_policy': 'Review the actual exercise and solution. Retain a solution only with an exercise-specific rationale; replace it with substantive reasoning when needed. Length is not an adequacy criterion.',
    'contract': 'page_contract.md',
    'forbidden_shortcuts': ['No word-count adequacy claims.', 'No generic boilerplate wrappers counted as thorough solutions.', 'No automatic pedagogical approval from structural validation.']}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def path(name, *, writable=False):
    p = Path(name)
    assert isinstance(name, str) and name and not p.is_absolute() and p.as_posix() == name
    assert not {'..', '.git', '.lake', '__pycache__'}.intersection(p.parts)
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    if writable:
        assert p.is_relative_to(ROOT / 'book/solutions') or p.is_relative_to(ROOT / 'reports/solution-review')
    return p


def ref(name):
    return {'file': name, 'sha256': sha(path(name).read_bytes())}


def read(name):
    return json.loads(path(name).read_bytes())


def put(name, data):
    p = path(name, writable=True)
    if p.exists():
        assert p.read_bytes() == data, 'Existing artifact differs: ' + name
        return
    p.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.link(temporary, p)
    finally:
        os.unlink(temporary)


def json_put(name, value):
    put(name, (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())


@dataclass
class Node:
    tag: str
    attrs: dict
    start: int
    open_end: int
    close_start: int = None
    end: int = None
    closed: bool = False
    children: list = field(default_factory=list)

    def text(self):
        return ''.join(c.text() if isinstance(c, Node) else c for c in self.children)

    def descendants(self, tag=None):
        for c in self.children:
            if isinstance(c, Node):
                if tag is None or c.tag == tag:
                    yield c
                yield from c.descendants(tag)

    def child(self, tag):
        return next((c for c in self.children if isinstance(c, Node) and c.tag == tag), None)


def clean(text):
    return re.sub(r'\s+', ' ', text).strip()


class Document(HTMLParser):
    def __init__(self, raw):
        super().__init__(convert_charrefs=True)
        self.raw, self.source = raw, raw.decode('utf-8')
        self.lines = [0] + [m.end() for m in re.finditer('\n', self.source)]
        self.byte_cache = {0: 0, len(self.source): len(raw)}
        self.root = Node('document', {}, 0, 0, len(self.source), len(self.source), True)
        self.stack = [self.root]
        self.nodes = []
        self.feed(self.source)
        self.close()

    def position(self):
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        start = self.position()
        node = Node(tag, dict(attrs), start, start + len(self.get_starttag_text()))
        self.stack[-1].children.append(node)
        self.nodes.append(node)
        if tag in VOID:
            node.close_start = node.end = node.open_end
            node.closed = True
        else:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            node = self.stack.pop()
            node.close_start = node.end = node.open_end
            node.closed = True

    def handle_endtag(self, tag):
        start = self.position()
        end = self.source.index('>', start) + 1
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i].tag == tag:
                node = self.stack[i]
                node.close_start, node.end, node.closed = start, end, True
                for implicit in self.stack[i + 1:]:
                    implicit.close_start = implicit.end = start
                self.stack = self.stack[:i]
                return

    def handle_data(self, data):
        self.stack[-1].children.append(data)

    def byte(self, offset):
        if offset not in self.byte_cache:
            self.byte_cache[offset] = len(self.source[:offset].encode('utf-8'))
        return self.byte_cache[offset]

    def range(self, start, end):
        assert 0 <= start <= end <= len(self.source)
        a, b = bisect.bisect_right(self.lines, start), bisect.bisect_right(self.lines, end)
        return dict(start_byte=self.byte(start), end_byte=self.byte(end), start_line=a,
                    start_column=start - self.lines[a - 1], end_line=b, end_column=end - self.lines[b - 1])

    def piece(self, start, end):
        span = self.range(start, end)
        raw = self.raw[span['start_byte']:span['end_byte']]
        return dict(range=span, html=raw.decode('utf-8'), text=clean(Document(raw).root.text()), sha256=sha(raw))

    def exercises(self):
        return [n for n in self.root.descendants('details') if n.child('summary') and EXERCISE.match(clean(n.child('summary').text()))]


def solution_slot(node, kind=None):
    summary = node.child('summary')
    assert node.closed and summary and summary.closed
    children = [c for c in node.children if isinstance(c, Node) and c is not summary]
    if kind is None:
        kind = 'container_inner' if len(children) == 1 and children[0].tag == 'div' else 'details_after_summary'
    if kind == 'container_inner':
        assert len(children) == 1 and children[0].tag == 'div' and children[0].closed
        return children[0].open_end, children[0].close_start, kind
    assert kind == 'details_after_summary'
    return summary.end, node.close_start, kind


def parts(doc, exercise, kind=None):
    summary = exercise.child('summary')
    assert exercise.closed and summary.closed
    solutions, hints = [], []
    for n in exercise.descendants('details'):
        title = clean(n.child('summary').text()) if n.child('summary') else ''
        if re.search(r'\b(answer|solution)\b', title, re.I):
            solutions.append(n)
        if re.search(r'\bhint\b', title, re.I):
            hints.append(n)
    assert len(solutions) == 1, 'Exercise must have exactly one solution: ' + clean(summary.text())
    solution = solutions[0]
    start, end, kind = solution_slot(solution, kind)
    slot = {**doc.piece(start, end), 'container_kind': kind,
            'disclosure_range': doc.range(solution.start, solution.end),
            'summary_html': doc.source[solution.child('summary').start:solution.child('summary').end]}
    omitted = sorted([(summary.start, summary.end), *[(n.start, n.end) for n in [*hints, solution]]])
    cursor, fragments = exercise.open_end, []
    for a, b in omitted:
        assert cursor <= a <= b <= exercise.close_start
        if a > cursor:
            fragments.append(doc.piece(cursor, a))
        cursor = b
    if cursor < exercise.close_start:
        fragments.append(doc.piece(cursor, exercise.close_start))
    prompt_html = ''.join(p['html'] for p in fragments)
    return dict(exercise=doc.piece(exercise.start, exercise.end),
        problem=dict(html=prompt_html, text=clean(Document(prompt_html.encode()).root.text()),
                     sha256=sha(prompt_html.encode()), fragments=fragments),
        hints=[dict(disclosure=doc.piece(n.start, n.end), body=doc.piece(n.child('summary').end, n.close_start)) for n in hints],
        solution=slot)


def author_file(source, doc, exercise):
    if source == 'SafeLearning/case-studies.html':
        return 'book/case-studies.html'
    start = doc.source.find('<!-- BOOK APPLICATION START -->')
    end = doc.source.find('<!-- BOOK APPLICATION END -->')
    if start >= 0 and start < exercise.start < end:
        return 'book/chapters/' + Path(source).name
    return source


def outside(raw, spans):
    cursor, result = 0, []
    for span in spans:
        a, b = span['start_byte'], span['end_byte']
        assert cursor <= a <= b <= len(raw)
        result.append(raw[cursor:a])
        cursor = b
    result.append(raw[cursor:])
    return result


def extract(directory, report):
    inventory = read(INVENTORY)
    assert inventory['counts']['exercises'] == len(inventory['exercises']) == 556
    assert len(inventory['counts']['exercises_by_page']) == 22
    initial = {n: sha(path(n).read_bytes()) for n in inventory['source_sha256']}
    assert initial == inventory['source_sha256'], 'Current pages differ from Source90 inventory'
    records, page_refs, page_manifests, source_refs, cached = [], {}, {}, {}, {}
    inputs = {**initial, INVENTORY: ref(INVENTORY)['sha256'], 'page_contract.md': ref('page_contract.md')['sha256'],
              SELF.relative_to(ROOT).as_posix(): sha(SELF.read_bytes())}

    def document(name):
        if name not in cached:
            raw = path(name).read_bytes()
            cached[name] = Document(raw)
            inputs[name] = sha(raw)
            snapshot = directory + '/sources/' + name
            put(snapshot, raw)
            source_refs[name] = ref(snapshot)
        return cached[name]

    for source, expected_count in sorted(inventory['counts']['exercises_by_page'].items()):
        doc = document(source)
        exercises = doc.exercises()
        rows = [r for r in inventory['exercises'] if r['source'] == source]
        assert len(rows) == len(exercises) == expected_count
        extracted = []
        for ordinal, (original, node) in enumerate(zip(rows, exercises), 1):
            assert original['ordinal'] == ordinal and original['anchor'] == node.attrs.get('id')
            assert original['label'] == clean(node.child('summary').text())
            raw_text = node.text().replace('\r\n', '\n').replace('\r', '\n')
            assert sha(raw_text.encode()) == original['text_sha256'], original['key']
            item = parts(doc, node)
            assert item['exercise']['range']['start_line'] == original['line']
            authored = author_file(source, doc, node)
            authored_doc = document(authored)
            if authored == source:
                authored_node, authored_ordinal = node, ordinal
            else:
                candidates = [(i, n) for i, n in enumerate(authored_doc.exercises(), 1) if n.attrs.get('id') == original['anchor']]
                assert len(candidates) == 1, original['key']
                authored_ordinal, authored_node = candidates[0]
                assert authored_doc.source[authored_node.start:authored_node.end] == doc.source[node.start:node.end], original['key']
            authored_parts = parts(authored_doc, authored_node)
            assert authored_parts['solution']['sha256'] == item['solution']['sha256']
            row = dict(inventory_key=original['key'], source_file=source, ordinal=ordinal, anchor=original['anchor'],
                locator=original['locator'], label=original['label'], level=original['level'],
                inventory_text_sha256=original['text_sha256'], source_sha256=inputs[source],
                authoring_file=authored, authoring=dict(ordinal=authored_ordinal, source_sha256=inputs[authored],
                    exercise_range=authored_parts['exercise']['range'], solution_range=authored_parts['solution']['range'],
                    problem_ranges=[p['range'] for p in authored_parts['problem']['fragments']],
                    hint_ranges=[h['disclosure']['range'] for h in authored_parts['hints']]),
                status='pending_pedagogical_review', **item)
            extracted.append(row)
            records.append(row)
        page_name = directory + '/pages/' + Path(source).name + '.json'
        json_put(page_name, dict(status='baseline_pending_pedagogical_review', source=ref(source),
            inventory=ref(INVENTORY), exercises=extracted))
        page_refs[source] = ref(page_name)
        page_manifest = directory + '/pages/' + Path(source).name + '.manifest.json'
        json_put(page_manifest, dict(source=ref(source), baseline=ref(page_name), exercise_count=len(extracted),
            solution_ranges=[{'inventory_key': r['inventory_key'], **r['solution']['range'], 'sha256': r['solution']['sha256']} for r in extracted],
            non_solution_segment_sha256=[sha(s) for s in outside(doc.raw, [r['solution']['range'] for r in extracted])]))
        page_manifests[source] = ref(page_manifest)
    assert len(records) == len({r['inventory_key'] for r in records}) == 556
    assert {r['inventory_key'] for r in records} == {r['key'] for r in inventory['exercises']}
    assert all(sha(path(n).read_bytes()) == h for n, h in inputs.items()), 'Baseline input changed during extraction'
    manifest_name = directory + '/manifest.json'
    manifest = dict(schema='solution-review.source90.v1', status='baseline_all_pending_pedagogical_review', inventory=ref(INVENTORY),
        page_contract=ref('page_contract.md'), extractor=ref(SELF.relative_to(ROOT).as_posix()),
        exercise_count=556, page_count=22, pages=page_refs, page_manifests=page_manifests, source_snapshots=source_refs,
        input_sha256=inputs, rubric=RUBRIC, scope='Exact extraction and preservation baseline only; no adequacy or mathematical-completion inference.')
    json_put(manifest_name, manifest)
    tracker_name = directory + '/review-tracker.json'
    json_put(tracker_name, dict(baseline=ref(manifest_name), rubric=RUBRIC, exercises=[dict(
        inventory_key=r['inventory_key'], source_file=r['source_file'], authoring_file=r['authoring_file'],
        label=r['label'], original_solution_sha256=r['solution']['sha256'], status='pending_pedagogical_review',
        decision=None, exercise_specific_rationale=None, review_family=None,
        criteria={k: {'status': 'pending', 'evidence': None} for k in RUBRIC['common']}) for r in records]))
    summary = dict(status='passed_exact_solution_baseline_extraction', manifest=ref(manifest_name), tracker=ref(tracker_name),
        exercises=556, pages=22, all_pending_pedagogical_review=True,
        with_hint=sum(bool(r['hints']) for r in records), without_hint=sum(not r['hints'] for r in records),
        authoring_counts=dict(Counter(r['authoring_file'].split('/')[0] for r in records)),
        input_sha256_before=inputs, input_sha256_after={n: sha(path(n).read_bytes()) for n in inputs},
        canonical_pages_or_authoring_sources_modified=False, pedagogical_adequacy_claimed=False)
    json_put(report, summary)
    return summary


def load(directory):
    name = directory + '/manifest.json'
    manifest = read(name)
    records = []
    for row in manifest['pages'].values():
        assert ref(row['file']) == row
        records.extend(read(row['file'])['exercises'])
    return manifest, records


def validate_candidate(manifest, records, source, candidate_raw):
    snapshot = manifest['source_snapshots'][source]
    assert ref(snapshot['file']) == snapshot
    before = path(snapshot['file']).read_bytes()
    old_doc, new_doc = Document(before), Document(candidate_raw)
    original, candidate = old_doc.exercises(), new_doc.exercises()
    assert len(original) == len(candidate), 'Exercise count changed'
    relevant = [r for r in records if r['source_file'] == source] if source.startswith('SafeLearning/') else [r for r in records if r['authoring_file'] == source]
    order = 'ordinal' if source.startswith('SafeLearning/') else 'authoring'
    relevant.sort(key=lambda r: r['ordinal'] if order == 'ordinal' else r['authoring']['ordinal'])
    assert len(relevant) == len(original)
    old_spans, new_spans, changes = [], [], []
    for row, a, b in zip(relevant, original, candidate):
        assert a.attrs.get('id') == b.attrs.get('id') and clean(a.child('summary').text()) == clean(b.child('summary').text()), row['inventory_key']
        x, y = parts(old_doc, a, row['solution']['container_kind']), parts(new_doc, b, row['solution']['container_kind'])
        assert x['solution']['sha256'] == row['solution']['sha256']
        assert x['problem']['html'] == y['problem']['html'], 'Prompt changed: ' + row['inventory_key']
        assert x['hints'] == y['hints'] or [h['disclosure']['html'] for h in x['hints']] == [h['disclosure']['html'] for h in y['hints']], 'Hint changed: ' + row['inventory_key']
        assert len(x['hints']) == len(y['hints'])
        old_spans.append(x['solution']['range'])
        new_spans.append(y['solution']['range'])
        if x['solution']['sha256'] != y['solution']['sha256']:
            assert y['solution']['text'], 'Replacement solution is empty'
            changes.append(dict(inventory_key=row['inventory_key'], original_solution_sha256=x['solution']['sha256'], replacement_sha256=y['solution']['sha256']))
    assert outside(before, old_spans) == outside(candidate_raw, new_spans), 'Non-solution page bytes changed'
    assert [n.attrs['id'] for n in old_doc.nodes if 'id' in n.attrs] == [n.attrs['id'] for n in new_doc.nodes if 'id' in n.attrs], 'Anchor IDs changed'
    scripts = lambda d: [d.raw[d.byte(n.start):d.byte(n.end)] for n in d.nodes if n.tag == 'script']
    assert scripts(old_doc) == scripts(new_doc), 'Scripts changed'
    hooks = lambda d: [(k, v) for n in d.nodes for k, v in n.attrs.items() if k.startswith('on')]
    assert hooks(old_doc) == hooks(new_doc), 'Inline script hooks changed'
    return dict(status='passed_solution_only_preservation', source_file=source, baseline_source_sha256=sha(before),
        candidate_source_sha256=sha(candidate_raw), exercise_count=len(original), changed_solutions=changes,
        prompts_hints_non_solution_bytes_anchors_scripts_preserved=True, pedagogical_adequacy_claimed=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', default=BASELINE)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('extract')
    p.add_argument('--report', default='reports/solution-review/baseline-source90-extraction-v1.json')
    p = sub.add_parser('list')
    p.add_argument('--page', required=True)
    p.add_argument('--limit', type=int, default=3)
    p.add_argument('--chars', type=int, default=1800)
    p = sub.add_parser('validate')
    p.add_argument('--source', required=True)
    p.add_argument('--candidate', required=True)
    p.add_argument('--report', required=True)
    args = parser.parse_args()
    try:
        if args.command == 'extract':
            result = extract(args.baseline, args.report)
            print(json.dumps({k: result[k] for k in ['status', 'manifest', 'exercises', 'pages', 'with_hint', 'without_hint']}))
        else:
            manifest, records = load(args.baseline)
            if args.command == 'list':
                selected = [r for r in records if Path(r['source_file']).name == args.page or r['source_file'] == args.page]
                assert selected, 'Unknown exercise page'
                selected = selected if args.limit == 0 else selected[:args.limit]
                print(json.dumps([dict(inventory_key=r['inventory_key'], source_file=r['source_file'], authoring_file=r['authoring_file'],
                    label=r['label'], original_solution_sha256=r['solution']['sha256'],
                    problem=r['problem']['text'][:args.chars], hints=[h['body']['text'][:args.chars] for h in r['hints']],
                    solution_html=r['solution']['html'][:args.chars]) for r in selected], indent=2, ensure_ascii=False))
            else:
                result = validate_candidate(manifest, records, args.source, path(args.candidate).read_bytes())
                result.update(baseline=ref(args.baseline + '/manifest.json'), candidate=ref(args.candidate), extractor=ref(SELF.relative_to(ROOT).as_posix()))
                json_put(args.report, result)
                print(json.dumps(dict(status=result['status'], source=args.source, changed_solutions=len(result['changed_solutions']), report=ref(args.report))))
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps(dict(status='refused_solution_review_operation', error=str(error))))
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
