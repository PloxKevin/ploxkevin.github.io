"""Independent Source91 installation audit; never imports release/check helpers.

Parse original and installed native HTML independently. Locate each solution by
its disclosure summary and actual surrounding markup, compare its extracted
bytes to the approved draft, then reverse those observed spans. A successful
inverse must reproduce every Source90 byte, except the one explicitly declared
readiness delimiter repair, which is reversed separately. Existing math/depth
reviews are bound to selected hashes; this does not redo or promote proofs.
"""
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from hashlib import sha256
from html import unescape
from html.parser import HTMLParser
from pathlib import Path
import json
import re
import sys
import traceback

ROOT = Path(__file__).resolve().parents[2]
PLAN = 'book/solutions/releases/source91-v1/plan.json'
EXPECTED_PLAN_SHA = '58455c17c48c091f9c6934165d64d003ff43bfee7bda888d10f438d02e7cc11e'
OUT = ROOT / 'reports/solution-review/source91-installed-independent-review-v1.json'
assert not OUT.exists(), 'Preserve an earlier review; use a new reviewer version'
VOID = {'area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr'}
SOLUTION_SUMMARIES = {'show solution','show answer','show worked solution','worked solution'}


def digest(data):
    return sha256(data).hexdigest()


def ref(file):
    p = ROOT / file
    return {'file':file, 'sha256':digest(p.read_bytes()), 'bytes':p.stat().st_size}


def load_bound(expected):
    p = ROOT / expected['file']
    data = p.read_bytes()
    assert digest(data) == expected['sha256'], ('bound reference mismatch', expected['file'])
    return json.loads(data)


@dataclass(eq=False)
class Node:
    tag: str
    attrs: dict
    start: int
    opening_end: int
    parent: object
    children: list = field(default_factory=list)
    closing_start: int = -1
    end: int = -1


class NativeHTML(HTMLParser):
    """A fresh raw-token tree with UTF-8 offsets, independent of repository code."""
    def __init__(self, data):
        super().__init__(convert_charrefs=False)
        self.data = data
        self.source = data.decode('utf-8')
        self.line_starts = [0]
        self.line_starts.extend(i+1 for i,c in enumerate(self.source) if c == '\n')
        self.byte_offsets = [0]
        position = 0
        for c in self.source:
            position += len(c.encode('utf-8'))
            self.byte_offsets.append(position)
        assert position == len(data)
        self.nodes = []
        self.stack = []
        self.feed(self.source)
        self.close()

    def offset(self):
        line,column = self.getpos()
        return self.line_starts[line-1]+column

    def handle_starttag(self, tag, attrs):
        start = self.offset()
        opening_end = start+len(self.get_starttag_text())
        parent = self.stack[-1] if self.stack else None
        n = Node(tag,dict(attrs),start,opening_end,parent)
        if parent:
            parent.children.append(n)
        self.nodes.append(n)
        if tag in VOID:
            n.closing_start = opening_end
            n.end = opening_end
        else:
            self.stack.append(n)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag,attrs)
        if tag not in VOID:
            n = self.stack.pop()
            n.closing_start = n.opening_end
            n.end = n.opening_end

    def handle_endtag(self, tag):
        start = self.offset()
        end = self.source.index('>',start)+1
        for i in range(len(self.stack)-1,-1,-1):
            if self.stack[i].tag == tag:
                n = self.stack[i]
                n.closing_start = start
                n.end = end
                # Raw HTML can omit unrelated inner end tags; the enclosing
                # disclosure/div bounds still come from their actual end tags.
                for omitted in self.stack[i+1:]:
                    if omitted.end < 0:
                        omitted.closing_start = start
                        omitted.end = start
                del self.stack[i:]
                return

    def brange(self, node):
        assert node.end >= node.opening_end >= node.start
        return self.byte_offsets[node.start],self.byte_offsets[node.end]

    def raw(self, node):
        a,b = self.brange(node)
        return self.data[a:b]

    def opening(self, node):
        return self.data[self.byte_offsets[node.start]:self.byte_offsets[node.opening_end]]

    def summary(self, node):
        summaries = [n for n in node.children if n.tag == 'summary']
        assert len(summaries) == 1, ('disclosure summary count',len(summaries))
        return summaries[0]

    def summary_text(self, node):
        s = self.summary(node)
        text = self.source[s.opening_end:s.closing_start]
        return ' '.join(unescape(re.sub(r'<[^>]*>','',text)).lower().split())

    def solution_disclosures(self, outer=None):
        def within(n):
            if outer is None:
                return True
            p = n.parent
            while p:
                if p is outer:
                    return True
                p = p.parent
            return False
        return [n for n in self.nodes if n.tag == 'details' and within(n)
                and any(c.tag == 'summary' for c in n.children)
                and self.summary_text(n) in SOLUTION_SUMMARIES]

    def solution_body(self, disclosure):
        summary = self.summary(disclosure)
        a,b = summary.end,disclosure.closing_start
        following = [n for n in disclosure.children if n.start >= a]
        # A sole div which covers all non-whitespace after the summary is the
        # original editable body container. Otherwise the disclosure remainder
        # is itself editable (the21 unwrapped original project/lab answers).
        if (len(following) == 1 and following[0].tag == 'div'
                and not self.source[a:following[0].start].strip()
                and not self.source[following[0].end:b].strip()):
            container = following[0]
            kind = 'container_inner'
            a,b = container.opening_end,container.closing_start
        else:
            kind = 'details_after_summary'
        start,end = self.byte_offsets[a],self.byte_offsets[b]
        return start,end,self.data[start:end],kind


def byte_range(r):
    return r['start_byte'],r['end_byte']


def main():
    assert ref(PLAN)['sha256'] == EXPECTED_PLAN_SHA
    plan = json.loads((ROOT/PLAN).read_bytes())
    manifest = load_bound(plan['baseline_manifest'])
    assert manifest['exercise_count'] == 556 and manifest['page_count'] == 22
    assert plan['counts'] == {'exercises':556,'pages':22,'retain':305,'replace':251}
    assert len(plan['drafts']) == len(plan['independent_reviews']) == 22
    assert len(plan['files']) == len(manifest['source_snapshots']) == 44
    assert len(plan['site_source91_sha256']) == 31
    baseline = {}
    baseline_page_refs = []
    page_manifest_refs = []
    for source,bref in manifest['pages'].items():
        page = load_bound(bref)
        baseline_page_refs.append(ref(bref['file']))
        load_bound(manifest['page_manifests'][source])
        page_manifest_refs.append(ref(manifest['page_manifests'][source]['file']))
        for b in page['exercises']:
            assert b['source_file'] == source
            assert b['inventory_key'] not in baseline
            assert digest(b['solution']['html'].encode()) == b['solution']['sha256']
            baseline[b['inventory_key']] = b
    assert len(baseline) == 556

    drafts = {}
    draft_rows = {}
    for r in plan['drafts']:
        d = load_bound(r)
        rows = d if isinstance(d,list) else d.get('exercises',d.get('solutions',d.get('proposals')))
        assert isinstance(rows,list)
        drafts[r['file']] = set()
        for x in rows:
            key = x['inventory_key']
            assert key in baseline and key not in draft_rows
            b = baseline[key]
            assert x['source_file'] == b['source_file']
            assert x['original_solution_sha256'] == b['solution']['sha256']
            assert x['decision'] in {'retain','replace'}
            body = x.get('replacement_html',b['solution']['html']).encode()
            assert (body == b['solution']['html'].encode()) == (x['decision'] == 'retain')
            drafts[r['file']].add(key)
            draft_rows[key] = {'row':x,'draft':r,'body':body,'selected_sha256':digest(body)}
    assert set(draft_rows) == set(baseline)
    counts = Counter(v['row']['decision'] for v in draft_rows.values())
    assert counts == {'retain':305,'replace':251}

    prior_review_bindings = []
    review_rows = {}
    approved_statuses = {'approved','approved_all_selected_solutions','approved_all34_selected_solutions',
                         'approved_all_35_selected_solutions','approved_all_44_selected_solutions',
                         'approved_all_20_selected_solutions'}
    for rr in plan['independent_reviews']:
        review = load_bound(rr)
        assert review['status'] in approved_statuses
        assert not review.get('errors',[]) and not review.get('issues',[])
        dr = review['draft']
        assert dr['file'] in drafts
        assert dr['sha256'] == ref(dr['file'])['sha256']
        rows = review.get('exercise_reviews',review.get('exercises'))
        assert {r['inventory_key'] for r in rows} == drafts[dr['file']]
        for r in rows:
            key = r['inventory_key']
            assert key not in review_rows
            assert r.get('decision_verdict',r.get('verdict')) == 'approved'
            assert not r.get('errors',[]) and not r.get('issues',[]) and not r.get('remaining_gaps',[])
            assert r['decision'] == draft_rows[key]['row']['decision']
            assert r['original_solution_sha256'] == baseline[key]['solution']['sha256']
            selected_hash = r.get('reviewed_solution_sha256',r.get('selected_solution_sha256'))
            assert selected_hash == draft_rows[key]['selected_sha256']
            review_rows[key] = {'reference':rr,'row':r}
        prior_review_bindings.append({'review':ref(rr['file']), 'draft':ref(dr['file']),
                                     'status':'passed_exact_selected_prior_math_depth_approval_binding',
                                     'exercise_count':len(rows),
                                     'mathematics_or_depth_reperformed_here':False})
    assert set(review_rows) == set(baseline)

    tracker = load_bound(plan['approved_tracker'])
    tr = {r['inventory_key']:r for r in tracker['exercises']}
    assert len(tr) == 556 and set(tr) == set(baseline)
    for key,r in tr.items():
        assert r['status'] == 'independently_approved_draft_pending_adoption'
        assert r['decision'] == draft_rows[key]['row']['decision']
        assert r['original_solution_sha256'] == baseline[key]['solution']['sha256']
        assert r['selected_solution_sha256'] == draft_rows[key]['selected_sha256']
        assert r['draft']['file'] == draft_rows[key]['draft']['file']
        assert r['draft']['sha256'] == draft_rows[key]['draft']['sha256']
        assert r['independent_review'] == review_rows[key]['reference']
        for criterion,evidence in r['criteria'].items():
            assert evidence['status'] == 'approved_in_independent_review'
            assert evidence['evidence']['inventory_key'] == key
            assert evidence['evidence']['review'] == review_rows[key]['reference']

    # Read every original, immutable selected and installed source directly.
    originals = {}
    installed = {}
    source_records = {}
    trees90 = {}
    trees91 = {}
    for f in plan['files']:
        source = f['file']
        assert source not in originals
        assert manifest['source_snapshots'][source] == f['before']
        original = (ROOT/f['before']['file']).read_bytes()
        selected = (ROOT/f['after']['file']).read_bytes()
        actual = (ROOT/source).read_bytes()
        assert digest(original) == f['before_sha256'] == f['before']['sha256']
        assert digest(selected) == f['after_sha256'] == f['after']['sha256']
        assert actual == selected and digest(actual) == f['after_sha256']
        assert f['changed'] == (original != actual)
        originals[source],installed[source] = original,actual
        trees90[source],trees91[source] = NativeHTML(original),NativeHTML(actual)
        source_records[source] = {'installed_source':ref(source),
                                  'preserved_source90_snapshot':ref(f['before']['file']),
                                  'immutable_selected_source91_snapshot':ref(f['after']['file']),
                                  'installed_equals_immutable_selected_bytes':True,
                                  'parsed_solutions':0}
    assert set(originals) == set(manifest['source_snapshots'])

    inverses = defaultdict(list)
    located90 = defaultdict(set)
    located91 = defaultdict(set)
    exercise_records = []
    source_occurrences = []
    hint_count = 0
    for key,b in sorted(baseline.items(),key=lambda kv:(kv[1]['source_file'],kv[1]['ordinal'])):
        occurrences = []
        for source,er,sr,problem_fragments,hints in [
                (b['source_file'],b['exercise']['range'],b['solution']['range'],
                 [x['range'] for x in b['problem']['fragments']],
                 [h['disclosure']['range'] for h in b['hints']]),
                (b['authoring_file'],b['authoring']['exercise_range'],b['authoring']['solution_range'],
                 b['authoring']['problem_ranges'],b['authoring']['hint_ranges'])]:
            if source in [r['source_file'] for r in occurrences]:
                continue
            t90,t91 = trees90[source],trees91[source]
            roots90 = [n for n in t90.nodes if n.tag == 'details' and t90.brange(n) == byte_range(er)]
            assert len(roots90) == 1, ('baseline exercise parse',key,source,len(roots90))
            outer90 = roots90[0]
            assert t90.raw(outer90) == b['exercise']['html'].encode()
            summary90 = t90.raw(t90.summary(outer90))
            if outer90.attrs.get('id'):
                roots91 = [n for n in t91.nodes if n.attrs.get('id') == outer90.attrs['id']]
            else:
                roots91 = [n for n in t91.nodes if n.tag == 'details'
                           and any(c.tag == 'summary' for c in n.children)
                           and t91.raw(t91.summary(n)) == summary90]
            assert len(roots91) == 1, ('installed exercise locator',key,source,len(roots91))
            outer91 = roots91[0]
            assert outer91.tag == 'details' and t91.raw(t91.summary(outer91)) == summary90
            answer90,answer91 = t90.solution_disclosures(outer90),t91.solution_disclosures(outer91)
            assert len(answer90) == len(answer91) == 1
            old_disc,new_disc = answer90[0],answer91[0]
            a0,z0,old_body,kind90 = t90.solution_body(old_disc)
            a1,z1,new_body,kind91 = t91.solution_body(new_disc)
            assert (a0,z0) == byte_range(sr)
            assert old_body == b['solution']['html'].encode()
            assert kind90 == kind91 == b['solution']['container_kind']
            assert new_body == draft_rows[key]['body']
            assert digest(new_body) == draft_rows[key]['selected_sha256']
            assert t90.raw(t90.summary(old_disc)) == t91.raw(t91.summary(new_disc))
            located90[source].add(old_disc)
            located91[source].add(new_disc)
            inverses[source].append((a1,z1,old_body,key))
            x0,y0 = t90.brange(outer90)
            x1,y1 = t91.brange(outer91)
            original_exercise = originals[source][x0:y0]
            current_exercise = installed[source][x1:y1]
            reverted = current_exercise[:a1-x1]+old_body+current_exercise[z1-x1:]
            assert reverted == original_exercise
            assert digest(original_exercise) == b['exercise']['sha256']
            delta = len(new_body)-len(old_body)

            def map_original_range(r):
                start,end = byte_range(r)
                assert x0 <= start <= end <= y0
                assert end <= a0 or start >= z0, ('protected fragment overlaps answer',key,source)
                shift = delta if start >= z0 else 0
                current_start = x1+(start-x0)+shift
                current_end = x1+(end-x0)+shift
                assert originals[source][start:end] == installed[source][current_start:current_end]
                return installed[source][current_start:current_end]

            assert len(problem_fragments) == len(b['problem']['fragments'])
            current_question = b''.join(map_original_range(r) for r in problem_fragments)
            assert current_question == b['problem']['html'].encode()
            assert digest(current_question) == b['problem']['sha256']
            assert len(hints) == len(b['hints'])
            for hr,h in zip(hints,b['hints']):
                current_hint = map_original_range(hr)
                assert current_hint == h['disclosure']['html'].encode()
                assert digest(current_hint) == h['disclosure']['sha256']
            if source == b['source_file']:
                hint_count += len(hints)
            occurrences.append({'source_file':source,'installed_source_sha256':digest(installed[source]),
                                'parsed_solution_range':{'start_byte':a1,'end_byte':z1},
                                'parsed_exercise_range':{'start_byte':x1,'end_byte':y1},
                                'selected_solution_sha256':digest(new_body),
                                'question_sha256':digest(current_question),
                                'hint_disclosure_sha256':[h['disclosure']['sha256'] for h in b['hints']],
                                'solution_container_kind':kind91,
                                'full_exercise_reverts_to_exact_source90_bytes':True,
                                'question_hints_and_disclosure_summary_preserved':True})
            source_records[source]['parsed_solutions'] += 1
            source_occurrences.append((key,source))
        assert len(occurrences) == (1 if b['source_file'] == b['authoring_file'] else 2)
        assert {r['selected_solution_sha256'] for r in occurrences} == {draft_rows[key]['selected_sha256']}
        exercise_records.append({'inventory_key':key,'ordinal':b['ordinal'],'label':b['label'],
                                 'decision':draft_rows[key]['row']['decision'],
                                 'original_solution_sha256':b['solution']['sha256'],
                                 'selected_solution_sha256':draft_rows[key]['selected_sha256'],
                                 'draft':draft_rows[key]['draft'],
                                 'existing_independent_math_depth_review':review_rows[key]['reference'],
                                 'installation_verdict':'passed','occurrences':occurrences})
    assert hint_count == 427
    assert len(exercise_records) == 556
    assert len(set(source_occurrences)) == len(source_occurrences) == 623

    exception_records = []
    assert len(plan['formatting_exceptions']) == 1
    exception = plan['formatting_exceptions'][0]
    assert exception['source_file'] == 'SafeLearning/toolkit-gp.html'
    assert exception['before'] == 'What bound does Cauchy–Schwarz give for $|\\langle u,v\nangle|$?'
    assert exception['after'] == 'What bound does Cauchy–Schwarz give for $|\\langle u,v\\rangle|$?'
    for source in sorted(originals):
        assert set(trees90[source].solution_disclosures()) == located90[source]
        assert set(trees91[source].solution_disclosures()) == located91[source]
        ordered = sorted(inverses[source])
        assert all(a[1] <= b[0] for a,b in zip(ordered,ordered[1:]))
        actual = installed[source]
        reverse = actual
        for start,end,old_body,key in reversed(ordered):
            reverse = reverse[:start]+old_body+reverse[end:]
        if source == exception['source_file']:
            before,after = exception['before'].encode(),exception['after'].encode()
            assert originals[source].count(before) == reverse.count(after) == 1
            assert actual.count(before) == 0 and actual.count(after) == 1
            position = actual.index(after)
            assert not any(start <= position < end for start,end,_,_ in ordered)
            reverse = reverse.replace(after,before,1)
            exception_records.append({'source_file':source,'before_sha256':digest(before),
                                      'after_sha256':digest(after),'reversed_occurrences':1,
                                      'outside_every_inventory_exercise_solution':True,
                                      'exact_plan_exception_only':True,
                                      'semantic_statement_or_hint_change_claimed':False})
        assert reverse == originals[source], ('full-source inverse mismatch',source)
        ids90 = [(n.attrs['id'],trees90[source].opening(n)) for n in trees90[source].nodes if 'id' in n.attrs]
        ids91 = [(n.attrs['id'],trees91[source].opening(n)) for n in trees91[source].nodes if 'id' in n.attrs]
        assert ids90 == ids91, ('anchor bytes changed',source)
        scripts90 = [trees90[source].raw(n) for n in trees90[source].nodes if n.tag == 'script']
        scripts91 = [trees91[source].raw(n) for n in trees91[source].nodes if n.tag == 'script']
        assert scripts90 == scripts91, ('script bytes changed',source)
        hooks90 = [(k,v) for n in trees90[source].nodes for k,v in n.attrs.items() if k.startswith('on')]
        hooks91 = [(k,v) for n in trees91[source].nodes for k,v in n.attrs.items() if k.startswith('on')]
        assert hooks90 == hooks91, ('inline hook changed',source)
        source_records[source].update({
            'independent_inverse_status':'passed_exact_source90_reconstruction',
            'reconstructed_source90_sha256':digest(reverse),
            'all_non_solution_bytes_preserved_after_only_declared_exception_inverse':True,
            'anchor_count':len(ids91),'exact_anchor_start_tag_bytes_preserved':True,
            'script_count':len(scripts91),'exact_script_block_bytes_preserved':True,
            'inline_hook_count':len(hooks91),'inline_hook_attributes_preserved':True,
        })

    asset_records = []
    assert set(plan['site_source91_sha256']) == set(plan['site_source90_sha256'])
    for asset,expected in sorted(plan['site_source91_sha256'].items()):
        assert ref(asset)['sha256'] == expected
        assert manifest['input_sha256'][asset] == plan['site_source90_sha256'][asset]
        asset_records.append({'installed_asset':ref(asset),'planned_source91_sha256':expected,
                              'source90_sha256':plan['site_source90_sha256'][asset],
                              'status':'passed_planned_installed_asset_hash'})
    assert sum(r['parsed_solutions'] for s,r in source_records.items() if s.startswith('SafeLearning/')) == 556
    assert sum(r['parsed_solutions'] for s,r in source_records.items() if s.startswith('book/')) == 67
    assert plan['formal_source_correspondence_for_rewritten_answers'] == 'pending_explicit_rebase_no_automatic_coverage_claim'
    assert plan['historical_checkpoint35_formal_coverage_unchanged'] is True
    return {
        'schema':'solutions.source91.independent-installed-review.v1',
        'status':'approved_mechanical_installation', 'errors':[],
        'reviewer':'/root/review_gaussian35', 'reviewed_utc':datetime.now(timezone.utc).isoformat(),
        'plan':ref(PLAN), 'baseline_manifest':ref(plan['baseline_manifest']['file']),
        'baseline_pages':baseline_page_refs, 'baseline_page_manifests':page_manifest_refs,
        'immutable_approved_tracker':ref(plan['approved_tracker']['file']),
        'selected_drafts':[ref(r['file']) for r in plan['drafts']],
        'selected_prior_math_depth_review_bindings':prior_review_bindings,
        'counts':{'exercises':556,'pages':22,'replace':251,'retain':305,
                  'source_files':44,'reader_assets':31,'canonical_solution_occurrences':556,
                  'additional_authored_mirror_occurrences':67,'parsed_solution_occurrences':623,
                  'canonical_hints_preserved':427,'formatting_exceptions':1},
        'method':[
            'Read every installed native source and immutable selected/baseline snapshot directly; verify exact planned hashes.',
            'Parse every original and installed solution disclosure using a separately implemented HTMLParser tree with UTF-8 byte offsets; no repository extraction/install/check helper is imported or invoked.',
            'Locate exercises by conserved IDs or exact disclosure summaries, extract actual editable body containers, and bind all556 bodies to exact draft and prior independent-review hashes.',
            'Check every question fragment, hint disclosure, solution summary and authored/integrated mirror from actual installed byte ranges.',
            'Reverse independently observed solution spans, then the sole exact GP readiness delimiter exception, and demand exact Source90 reconstruction for every44 source files.',
            'Compare every complete anchor start tag, script block and inline event-hook attribute against Source90; compare every31 planned reader asset hash.',
        ],
        'independent_checker':ref('reports/solution-review/check-source91-installed-independent-v1.py'),
        'source_file_checks':list(source_records.values()), 'asset_checks':asset_records,
        'formatting_exception_checks':exception_records,'exercise_installation_checks':exercise_records,
        'math_and_depth_scope':'The22 exact prior independent reports already approve the selected556 bodies. This review checks those bindings and installed correspondence; it does not claim to have redone every mathematical/depth review.',
        'formal_coverage_scope':'Source90/checkpoint35 formal evidence remains historical. Correspondence of rewritten Source91 answers to formal declarations requires an explicit separate rebase; no formal unit or exercise is promoted here.',
        'browser_or_compiler_execution_claimed':False,
        'canonical_sources_owners_coverage_progress_publication_mutated_by_this_review':False,
        'remaining_external_checks':'Root is separately running the full29-page browser QA and selected35 native proof audit.',
    }


if __name__ == '__main__':
    try:
        report = main()
    except Exception as exc:
        failure = ROOT/'reports/solution-review/source91-installed-independent-failure-attempt-v1.json'
        assert not failure.exists(), 'Preserve an earlier failure attempt'
        record = {'status':'failed_independent_installation_check_attempt','errors':[str(exc)],
                  'traceback':traceback.format_exc(), 'plan':ref(PLAN),
                  'checker':ref('reports/solution-review/check-source91-installed-independent-v1.py'),
                  'approval_claimed':False,'canonical_mutations':False}
        failure.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
        print(json.dumps({'file':str(failure.relative_to(ROOT)),'status':record['status'],'errors':record['errors']}))
        sys.exit(1)
    OUT.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'file':str(OUT.relative_to(ROOT)),'sha256':digest(OUT.read_bytes()),
                      'status':report['status'],'counts':report['counts']},sort_keys=True))
