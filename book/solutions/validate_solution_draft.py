"""Validate explicit retain/replace decisions and create solution-only candidates.

Draft JSON may be a list or an object with an exercises/solutions/proposals list.
Each row needs inventory_key, source_file, original_solution_sha256, decision,
and thoroughness_rationale. A replace row also needs replacement_html. This
command writes candidates only under book/solutions and never edits authoring
sources, the teaching pages, coverage records, or publication.
"""
from pathlib import Path
import argparse
import json
import sys
import solution_review as review


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', default=review.BASELINE)
    parser.add_argument('--draft', action='append', required=True)
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--report', required=True)
    parser.add_argument('--require-complete-pages', action='store_true')
    args = parser.parse_args()
    try:
        review.path(args.output_dir, writable=True)
        assert review.path(args.output_dir).is_relative_to(review.ROOT / 'book/solutions')
        manifest, baseline_rows = review.load(args.baseline)
        index = {r['inventory_key']: r for r in baseline_rows}
        proposals, draft_refs, inputs = [], [], {}
        for name in args.draft:
            value = review.read(name)
            if isinstance(value, dict):
                found = [value[k] for k in ['exercises', 'solutions', 'proposals'] if k in value]
                assert len(found) == 1, 'Draft must contain one exercise-decision list'
                value = found[0]
            assert isinstance(value, list) and value, 'Draft has no exercise decisions'
            proposals.extend(value)
            draft_refs.append(review.ref(name))
            inputs[name] = review.ref(name)['sha256']
        assert len({p['inventory_key'] for p in proposals}) == len(proposals), 'Duplicate exercise decision'
        edits, page_decisions, retained, replaced = {}, {}, [], []
        for p in proposals:
            key = p['inventory_key']
            row = index[key]
            assert p['source_file'] == row['source_file'], key
            assert p['original_solution_sha256'] == row['solution']['sha256'], 'Original solution differs: ' + key
            assert isinstance(p['thoroughness_rationale'], (str, list, dict)) and p['thoroughness_rationale'], 'Missing exercise-specific rationale: ' + key
            assert p['decision'] in {'retain', 'replace'}, 'Unknown decision: ' + key
            page_decisions.setdefault(row['source_file'], []).append(key)
            if p['decision'] == 'retain':
                assert p.get('replacement_html', row['solution']['html']) == row['solution']['html'], 'Retained solution has replacement bytes: ' + key
                retained.append(key)
                continue
            replacement = p['replacement_html']
            assert isinstance(replacement, str) and replacement.strip(), 'Empty replacement: ' + key
            assert review.sha(replacement.encode()) != row['solution']['sha256'], 'Replace decision has unchanged bytes: ' + key
            replaced.append(key)
            slots = [(row['source_file'], row['solution']['range'])]
            if row['authoring_file'] != row['source_file']:
                slots.append((row['authoring_file'], row['authoring']['solution_range']))
            for source, span in slots:
                edits.setdefault(source, []).append((span, replacement.encode(), key))
        coverage = {}
        for page, decided in page_decisions.items():
            expected = {r['inventory_key'] for r in baseline_rows if r['source_file'] == page}
            missing = sorted(expected - set(decided))
            if args.require_complete_pages:
                assert not missing, 'Page decisions incomplete: ' + page
            coverage[page] = dict(expected=len(expected), decided=len(decided), missing_inventory_keys=missing)
        outputs, validations, candidates = [], [], []
        for source, swaps in sorted(edits.items()):
            snapshot = manifest['source_snapshots'][source]
            assert review.ref(snapshot['file']) == snapshot
            raw = review.path(snapshot['file']).read_bytes()
            cursor = len(raw)
            for span, replacement, key in sorted(swaps, key=lambda item: item[0]['start_byte'], reverse=True):
                a, b = span['start_byte'], span['end_byte']
                assert 0 <= a <= b <= cursor
                assert review.sha(raw[a:b]) == index[key]['solution']['sha256'], key
                raw = raw[:a] + replacement + raw[b:]
                cursor = a
            validation = review.validate_candidate(manifest, baseline_rows, source, raw)
            output = args.output_dir + '/' + source
            candidates.append((output, raw))
            validations.append(validation)
            outputs.append(dict(source_file=source, candidate_file=output, sha256=review.sha(raw)))
        # Every swap is checked before any candidate is written.
        for name, raw in candidates:
            review.put(name, raw)
        assert all(review.ref(name)['sha256'] == expected for name, expected in inputs.items()), 'Draft changed during validation'
        result = dict(status='passed_explicit_solution_draft_preservation', baseline=review.ref(args.baseline + '/manifest.json'),
            drafts=draft_refs, helper=review.ref(Path(__file__).resolve().relative_to(review.ROOT).as_posix()),
            extractor=review.ref(review.SELF.relative_to(review.ROOT).as_posix()), retained=retained, replaced=replaced,
            page_decision_coverage=coverage, candidates=outputs, preservation_checks=validations,
            canonical_sources_modified=False, pedagogical_adequacy_claimed=False,
            scope='Draft decisions/rationales are reviewer proposals. Structural preservation does not approve the reasoning or mathematical content.')
        review.json_put(args.report, result)
        print(json.dumps(dict(status=result['status'], retained=len(retained), replaced=len(replaced),
            candidate_files=len(outputs), report=review.ref(args.report))))
        return 0
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps(dict(status='refused_solution_draft', error=str(error))))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
