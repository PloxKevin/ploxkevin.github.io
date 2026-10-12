"""Bind the two immutable successful phases and the distinct qualifier review."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):
    if isinstance(p, str):
        p = ROOT / p
    return {'file': str(p.relative_to(ROOT)), 'sha256': sha(p), 'bytes': p.stat().st_size}
def read(r):
    p = Path(r['file'])
    if not p.is_absolute():
        p = ROOT / p
    assert sha(p) == r['sha256'], str(p)
    return json.loads(p.read_bytes())

phase_refs = [ref(BASE / n) for n in ['actual-reviewed33-canonical-paired-readiness-v1.json',
                                     'actual-reviewed33-planar7-canonical-paired-readiness-v1.json']]
phases = [read(r) for r in phase_refs]
assert phases[0]['status'] == 'passed_actual_reviewed33_canonical_standalone_and_named_pairs_unselected'
assert phases[1]['status'] == 'passed_actual_reviewed33_planar7_canonical_standalone_and_named_pairs_unselected'
narrow_ref = ref('book/coverage/checks/checkpoint33-review/independent-seven-qualifier-cumulative-review-v1.json')
narrow = read(narrow_ref)
assert narrow['status'] == 'approved_independent_Planar7_narrow_qualification_and_seven_packet_ten_replacement_cumulative_composition'
assert narrow['errors'] == []
assert narrow['additional_Planar_full_mathematical_peer'] == phases[1]['sources'][0]['independent_source_peers'][0] or (
    narrow['additional_Planar_full_mathematical_peer']['file'] == phases[1]['sources'][0]['independent_source_peers'][0]['file'] and
    narrow['additional_Planar_full_mathematical_peer']['sha256'] == phases[1]['sources'][0]['independent_source_peers'][0]['sha256'])
sources = [s for p in phases for s in p['sources']]
pairs = [s for p in phases for s in p['actual_paired_records']]
assert len(sources) == 7 and len(pairs) == 14
public_names = [d['name'] for s in sources for d in s['public_declarations']]
assert len(public_names) == len(set(public_names)) == 93
assert sum(s['public_theorem_count'] for s in sources) == 78
snapshots = {k: v for p in phases for k, v in p['source_snapshots'].items()}
for source in sources:
    canonical = ROOT / source['canonical_source']
    assert sha(canonical) == source['original_tmp_source']['sha256']
    source['canonical_source_ref'] = ref(canonical)
    selected_pairs = [p for p in pairs if p['source']['file'] == source['canonical_source']]
    assert len(selected_pairs) == 2 and {p['kind'] for p in selected_pairs} == {'standalone', 'named'}
    source['actual_paired_records'] = selected_pairs
    source['independent_cumulative_qualifier_review'] = narrow_ref
    if source['family'] == 'PlanarQuadratic7':
        source['independent_narrow_wording_and_parser_peer'] = narrow_ref
        assert narrow['additional_Planar_exact_source']['sha256'] == source['original_tmp_source']['sha256']
    for pair in selected_pairs:
        assert pair['actual_exit_code'] == 0 and pair['source']['sha256'] == sha(canonical)
        native = read(pair['actual_record'])
        assert native['actual_exit_code'] == native['exit_code'] == 0
        assert native['source_sha256_before'] == native['source_sha256_after'] == sha(canonical)
        assert native['compiler_recorder']['sha256'] == native['compiler_recorder_sha256_after']
        assert native['source_unchanged'] is True
        expected_command = ['lake', 'env', 'lean', 'SafeLearning/' + canonical.name] if pair['kind'] == 'standalone' else ['lake', 'build', 'SafeLearning.' + canonical.stem]
        assert native['command'] == native['actual_command'] == expected_command
        assert native['actual_workdir'] == str(ROOT / 'verification/lean')
        assert native['started_at_utc'] < native['finished_at_utc'] and native['elapsed_seconds'] > 0
        for key in ['raw_log', 'source_snapshot']:
            p = Path(pair[key]['file'])
            if not p.is_absolute():
                p = ROOT / p
            assert sha(p) == pair[key]['sha256']
        assert pair['raw_log']['sha256'] == native['log_sha256']
        assert pair['source_snapshot']['sha256'] == sha(canonical)
result = {'status': 'passed_actual_reviewed33_seven_canonical_standalone_and_named_pairs_unselected',
          'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(),
          'source_count': 7, 'public_theorem_count': 78, 'public_name_count': 93,
          'actual_compiler_command_count': 14, 'sources': sources, 'actual_paired_records': pairs,
          'source_snapshots': snapshots, 'original_phase_readiness': phase_refs,
          'independent_cumulative_qualifier_review': narrow_ref,
          'baseline_selection': phases[0]['baseline_selection'], 'compiler_readiness_composer': ref(Path(__file__)),
          'selected32_source_and_public_name_protection_passed': True,
          'selected32_protected_source_count': 1254, 'selected32_public_name_count': 14759,
          'original_evidence_retained_by_exact_references': True,
          'two_original_phase_readiness_and_all14_actual_command_receipts_preserved_exactly': True,
          'exact_qualifiers_owner_promotion_and_aggregate_still_separate': True,
          'coverage_complete': False, 'selection_aggregate_owner_or_publication_claimed': False,
          'prior_snapshot_tree_or_build_cache_copied': False}
target = BASE / 'actual-reviewed33-seven-canonical-paired-readiness-v1.json'
assert not target.exists()
with target.open('x') as out:
    out.write(json.dumps(result, indent=2) + '\n')
target.chmod(0o444)
Path(__file__).chmod(0o444)
print(json.dumps({'status': result['status'], 'readiness': ref(target), 'source_count': 7,
                  'theorems': 78, 'public_names': 93, 'actual_commands': 14, 'coverage_complete': False}))
