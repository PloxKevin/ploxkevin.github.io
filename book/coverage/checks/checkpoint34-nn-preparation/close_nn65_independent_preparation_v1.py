#!/usr/bin/env python3
"""Close preparation metadata without compiling, selecting or promoting anything."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations, without_comments


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {'file': str(path.relative_to(ROOT)), 'sha256': sha(path), 'bytes': path.stat().st_size}


def exact(record):
    path = Path(record['file'])
    if not path.is_absolute():
        path = ROOT / path
    assert sha(path) == record['sha256'], record['file']
    if 'bytes' in record:
        assert path.stat().st_size == record['bytes']
    return path


def full_public(text):
    # The existing source index omits declarations with an individual noncomputable modifier.
    normalized = re.sub(r'(?m)^(\s*)noncomputable\s+(?=(?:def|abbrev)\s)', r'\1', text)
    return declarations(normalized)


def main():
    output = OUT / 'nn65-future34-independent-preparation-closure-v1.json'
    assert not output.exists()
    readiness_path = OUT / 'nn65-future34-paired-readiness-v1.json'
    readiness = json.loads(readiness_path.read_bytes())
    assert readiness['errors'] == [] and len(readiness['actual_paired_records']) == 2
    canonical = exact(readiness['canonical_source'])
    assert canonical.read_bytes() == exact(readiness['original_source']).read_bytes()
    assert readiness['currently_selected_in33'] is False
    assert readiness['source_qualification_or_owner_promotion_or_publication_performed'] is False
    for pair in readiness['actual_paired_records']:
        actual = json.loads(exact(pair['actual_record']).read_bytes())
        assert actual['status'] == 'passed' and actual['actual_exit_code'] == 0 and actual['protection_errors'] == []
        assert exact(actual['source']).read_bytes() == exact(actual['source_snapshot']).read_bytes()
        exact(actual['raw_log'])
    reader_path = OUT / 'independent-scope-reader-v1.json'
    reader = json.loads(reader_path.read_bytes())
    assert sha(reader_path) == 'b4ea80780e4f52b8a2d0cbd28dcce7bb64a68d2a28a0e71ea7de07fb0f0bdad2'
    assert reader['errors'] == [] and reader['public_theorem_count'] == 65 and reader['public_name_count'] == 95
    baseline = json.loads(exact(readiness['protected_baseline']).read_bytes())
    changes = [name for name, fingerprint in baseline['protected_sha256'].items() if sha(ROOT / name) != fingerprint]
    assert changes == []
    selection_path = exact(readiness['selected33_selection'])
    selection = json.loads(selection_path.read_bytes())
    selected_names = set()
    selected_text = []
    for name, record in selection['proof_files'].items():
        path = ROOT / name
        assert sha(path) == record['sha256']
        text = path.read_text()
        selected_names.update(d['name'] for d in full_public(text))
        selected_text.append(without_comments(text))
    sources = []
    for stem, expected in [('CompleteModulesNNScalarOriginLinearization34', 95),
                           ('CompleteModulesShiftedTemporalIQC34', 26),
                           ('CompleteAppliedConditionalExpectationMSEDensityWhole34', 33)]:
        path = ROOT / f'verification/lean/SafeLearning/{stem}.lean'
        public = full_public(path.read_text())
        names = {d['name'] for d in public}
        assert len(names) == len(public) == expected
        assert names.isdisjoint(selected_names)
        namespaces = sorted({d['name'].rsplit('.', 1)[0] for d in public})
        assert all(namespace not in text for namespace in namespaces for text in selected_text)
        sources.append({'source': ref(path), 'public_name_count_including_individual_noncomputable_definitions': len(names),
                        'public_theorem_count': sum(d['kind'] == 'theorem' for d in public),
                        'namespace_declaration_name_conflicts_with_selected33': [], 'public_declarations': public})
    for index, first in enumerate(sources):
        first_names = {d['name'] for d in first['public_declarations']}
        for second in sources[index + 1:]:
            assert first_names.isdisjoint({d['name'] for d in second['public_declarations']})
    summary_path = exact(readiness['correspondence_summary'])
    summary = json.loads(summary_path.read_bytes())
    assert summary['current_whole_exercise_approved'] is False
    assert summary['source_qualification_required_and_not_applied'] is True
    assert summary['current_owner_exercise']['status'] == 'pending'
    assert [r['line_1_based'] for r in summary['remaining_exact_four_whole_line_replacements']] == [982, 988, 989, 990]
    exact(summary['exact_current_NN_page'])
    for stem in ('foundations', 'applied', 'modules', 'core'):
        text = (ROOT / f'book/coverage/{stem}.json').read_text()
        assert canonical.name not in text and str(canonical.relative_to(ROOT)) not in text
    assert all(str(canonical.relative_to(ROOT)) != name for name in selection['proof_files'])
    value = {'status': 'passed_independent_exact_NN65_future34_preparation_closure_unselected_only',
             'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(),
             'fresh_actual_paired_readiness': ref(readiness_path), 'independent_full65_scope_review': ref(reader_path),
             'exact_prospective_correspondence_and_unapplied_four_lines': ref(summary_path),
             'protected_baseline': readiness['protected_baseline'], 'protected_file_changes': changes,
             'selected33_proof_source_count': len(selection['proof_files']),
             'selected33_public_name_count_including_individual_noncomputable_definitions': len(selected_names),
             'unselected_future_sources_checked_for_conflicts': sources,
             'pairwise_future_public_name_conflicts': [], 'current_Exercise14_3_status': 'pending',
             'current_Exercise14_3_whole_approved': False, 'remaining_exact_line_application': [982, 988, 989, 990],
             'currently_selected_in33_or_in_owner33_proof_metadata': False,
             'source_qualification_owner_promotion_aggregate_axiom_kernel_or_publication_performed': False,
             'progress_and_publicationrepo_never_edited_and_concurrent_authorized33_delivery_excluded_from_guard': True,
             'historical_failure_pass_axiom_records_and_measured_times_retained_in_paired_readiness_and_scope_review': True,
             'closure_helper': ref(Path(__file__)), 'coverage_complete': False}
    output.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'closure': ref(output), 'unselected_future34': True}))


if __name__ == '__main__':
    main()
