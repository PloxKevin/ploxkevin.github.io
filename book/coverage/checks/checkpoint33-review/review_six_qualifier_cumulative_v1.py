#!/usr/bin/env python3
"""Independent reconstruction of the six Source81 qualifier packets for Root."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path(__file__).resolve().parent
INDEX = ROOT / 'book/coverage/checks/recovery32/next-batch-source-qualification-index-v1.json'


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def ref(path):
    path = Path(path)
    name = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
    data = path.read_bytes()
    return {'file': name, 'sha256': sha_bytes(data), 'bytes': len(data)}


def exact(record):
    path = Path(record['file'])
    if not path.is_absolute():
        path = ROOT / path
    data = path.read_bytes()
    assert sha_bytes(data) == record['sha256'], str(path)
    if 'bytes' in record:
        assert len(data) == record['bytes'], str(path)
    return path


def read_json(record):
    return json.loads(exact(record).read_bytes())


def literal_fields(row):
    return {k: v for k, v in row.items() if k != 'source_sha256'}


def run_inventory(tree, label):
    driver = tree / 'run_fresh_inventory.py'
    driver.write_text(
        "from pathlib import Path\nimport sys,json\n"
        "sys.path.insert(0,str(Path(__file__).resolve().parent/'book'))\n"
        "import inventory_claims as inv\n"
        "root=Path(__file__).resolve().parent\n"
        "assert inv.ROOT.resolve()==root and inv.OUT.resolve()==root/'book/coverage'\n"
        "assert root.is_relative_to('/tmp') and inv.OUT.is_relative_to('/tmp')\n"
        "print(json.dumps({'actual_ROOT':str(root),'actual_OUT':str(inv.OUT)}),flush=True)\n"
        "inv.inventory()\n"
    )
    command = [sys.executable, '-B', str(driver)]
    start = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    logfile = OUT / f'{label}-full29-parser.log'
    with logfile.open('xb') as stream:
        result = subprocess.run(command, cwd=tree, stdout=stream, stderr=subprocess.STDOUT,
                                env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    elapsed = time.monotonic() - tick
    assert result.returncode == 0, logfile.read_text()
    report = tree / 'book/coverage/inventory.json'
    native = {'actual_command': command, 'actual_workdir': str(tree),
              'actual_exit_code': result.returncode, 'started_at_utc': start,
              'finished_at_utc': datetime.now(timezone.utc).isoformat(),
              'elapsed_seconds': elapsed, 'raw_log': ref(logfile),
              'actual_ROOT': str(tree), 'actual_OUT': str(tree / 'book/coverage'),
              'parser': ref(tree / 'book/inventory_claims.py'),
              'validator': ref(tree / 'book/validate.py'),
              'driver': ref(driver), 'inventory': ref(report)}
    return json.loads(report.read_bytes()), native


def main():
    assert not (OUT / 'independent-six-qualifier-cumulative-review-v1.json').exists()
    index = json.loads(INDEX.read_bytes())
    offer_ref = index['authoritative_indexes']['six_qualifier_offer']
    offer = read_json(offer_ref)
    assert offer.get('errors') == [] and len(offer['packets']) == 6
    assert offer['exact_replacement_count'] == 9
    before_inventory = read_json(offer['baseline_Source81_inventory'])
    assert ref(ROOT / 'book/coverage/inventory.json')['sha256'] == index['current_checkpoint']['inventory']['sha256']
    original = {}
    cumulative = {}
    replacements = []
    packet_results = []
    for packet in offer['packets']:
        source = packet['source']
        raw = exact(packet['immutable_current_source']).read_bytes()
        assert (ROOT / source).read_bytes() == raw
        original[source] = raw
        cumulative.setdefault(source, raw)
        assert sha_bytes(cumulative[source]) == packet['cumulative_preview_before_sha256']
        proposal = read_json(packet['exact_original_proposal'])
        assert proposal['exact_replacements'] == packet['raw_exact_replacements']
        individual = raw
        for replacement in packet['raw_exact_replacements']:
            old = replacement['before'].encode()
            new = replacement['after'].encode()
            assert individual.count(old) == cumulative[source].count(old) == 1
            individual = individual.replace(old, new, 1)
            cumulative[source] = cumulative[source].replace(old, new, 1)
            replacements.append({'family': packet['family'], 'source': source,
                                 **replacement, 'old_occurrences': 1})
        assert individual == exact(packet['individual_reviewed_proposed_page']).read_bytes()
        assert sha_bytes(cumulative[source]) == packet['cumulative_preview_after_sha256']
        authorities = {}
        for field in ('independent_narrow_literal_and_full29_parser_peer',
                      'independent_whole_mathematical_or_composed_peer'):
            peer = read_json(packet[field])
            assert peer['status'].startswith('passed') and peer.get('errors', []) == []
            authorities[field] = {'reference': packet[field], 'exact_status': peer['status']}
        packet_results.append({'family': packet['family'], 'source': source,
                               'proposal': packet['exact_original_proposal'],
                               'original_source': packet['immutable_current_source'],
                               'individual_candidate': packet['individual_reviewed_proposed_page'],
                               'cumulative_before_sha256': packet['cumulative_preview_before_sha256'],
                               'cumulative_after_sha256': packet['cumulative_preview_after_sha256'],
                               'authorities': authorities})
    assert len(replacements) == 9
    inverse = dict(cumulative)
    for replacement in reversed(replacements):
        source = replacement['source']
        old = replacement['before'].encode()
        new = replacement['after'].encode()
        assert inverse[source].count(new) == 1
        inverse[source] = inverse[source].replace(new, old, 1)
    assert inverse == original
    candidates = {}
    physical_lines = {}
    for source, raw in cumulative.items():
        assert raw == exact(offer['combined_cumulative_candidates'][source]).read_bytes()
        old = original[source].decode()
        new = raw.decode()
        assert re.findall(r'<[^>]*>', old) == re.findall(r'<[^>]*>', new)
        assert re.findall(r'<script\b[^>]*>.*?</script>', old, re.S | re.I) == re.findall(r'<script\b[^>]*>.*?</script>', new, re.S | re.I)
        old_lines, new_lines = old.splitlines(keepends=True), new.splitlines(keepends=True)
        assert len(old_lines) == len(new_lines)
        physical_lines[source] = [i + 1 for i, (a, b) in enumerate(zip(old_lines, new_lines)) if a != b]
        destination = OUT / 'exact-cumulative-candidate' / source
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)
        candidates[source] = ref(destination)
    trees = {label: Path(tempfile.mkdtemp(prefix=f'checkpoint33-{label}-full29-', dir='/tmp'))
             for label in ('baseline', 'candidate')}
    inputs = []
    pages = sorted((ROOT / 'SafeLearning').glob('*.html'))
    assert len(pages) == 29
    for tree in trees.values():
        (tree / 'SafeLearning').mkdir()
        (tree / 'book').mkdir()
    for page in pages:
        source = str(page.relative_to(ROOT))
        raw = page.read_bytes()
        assert sha_bytes(raw) == before_inventory['source_sha256'][source]
        inputs.append(ref(page))
        for label, tree in trees.items():
            (tree / source).write_bytes(cumulative[source] if label == 'candidate' and source in cumulative else raw)
    for tree in trees.values():
        for name in ('inventory_claims.py', 'validate.py'):
            (tree / 'book' / name).write_bytes((ROOT / 'book' / name).read_bytes())
    baseline, baseline_native = run_inventory(trees['baseline'], 'baseline')
    candidate, candidate_native = run_inventory(trees['candidate'], 'candidate')
    assert baseline['counts'] == candidate['counts'] == before_inventory['counts']
    assert baseline['source_sha256'] == before_inventory['source_sha256']
    changes = {}
    records = {}
    for kind in ('exercises', 'material_source_units'):
        frozen = {r['key']: r for r in before_inventory[kind]}
        base = {r['key']: r for r in baseline[kind]}
        final = {r['key']: r for r in candidate[kind]}
        assert frozen == base and base.keys() == final.keys()
        changed = sorted(k for k in base if literal_fields(base[k]) != literal_fields(final[k]))
        changes[kind] = changed
        for key in base:
            assert final[key]['source_sha256'] == candidate['source_sha256'][final[key]['source']]
            if key not in changed:
                assert literal_fields(base[key]) == literal_fields(final[key])
        if kind == 'material_source_units':
            records = final
    assert changes == {'exercises': [], 'material_source_units': index['changed_literal_keys']}
    assert candidate['source_sha256'] == {
        **before_inventory['source_sha256'], **{k: sha_bytes(v) for k, v in cumulative.items()}}
    for key, pair in offer['entire_current_and_cumulative_prospective_changed_literals'].items():
        assert records[key] == pair['entire_cumulative_prospective']
    mappings = []
    peer_reads = []
    for family in index['ready_for_exact_source_qualification']:
        source = exact(family['source'])
        source_text = source.read_text()
        request = read_json(family['author_request'])
        whole = read_json(family['whole_prospective_peer'])
        narrow = read_json(family['narrow_wording_and_parser_peer'])
        assert whole.get('errors', []) == narrow.get('errors', []) == []
        names = whole['public_theorem_names']
        assert len(names) == family['theorems']
        for name in names:
            assert re.search(r'\btheorem\s+' + re.escape(name.rsplit('.', 1)[1]) + r'\b', source_text), name
        assert whole['actual_source']['sha256'] == family['source']['sha256']
        decisions = whole.get('prospective_whole_decisions', whole.get('whole_unit_decisions'))
        underlying = whole
        if 'original_full_mathematical_peer' in whole:
            underlying = read_json(whole['original_full_mathematical_peer'])
            assert underlying['actual_source']['sha256'] == family['source']['sha256']
        for unit in family['conditionally_approved_whole_material']:
            key = unit['key']
            decision = decisions[key]
            assert decision.get('whole_semantic_approved', decision.get('prospective_whole_semantic_approved')) is True
            assert decision.get('missing_requirements', decision.get('prospective_missing_requirements')) == []
            expected = decision.get('exact_entire_proposed_literal')
            if expected is None:
                expected = underlying.get('entire_prospective_literal')
                if expected is None:
                    for field in ('entire_prospective_literals', 'entire_current_and_prospective_literals'):
                        if field in underlying:
                            expected = underlying[field]
                            break
            if isinstance(expected, dict) and expected.get('key') == key:
                assert literal_fields(expected) == literal_fields(records[key])
            mappings.append({'key': key, 'family': family['family'],
                             'existing_pending_claim_ids': unit['pending_claim_ids'],
                             'entire_candidate_literal': records[key],
                             'source': family['source'], 'public_theorem_names': names,
                             'prospective_whole_decision': decision,
                             'whole_peer': family['whole_prospective_peer'],
                             'distinct_narrow_peer': family['narrow_wording_and_parser_peer'],
                             'exact_proposal': family['exact_proposal'],
                             'definitions_and_support_statement_scope': {
                                 k: v for k, v in whole.items()
                                 if k in ('full_definition_clause_correspondence', 'actual_factual_attribution_scope')},
                             'underlying_full_peer': whole.get('original_full_mathematical_peer')})
        peer_reads.append({'family': family['family'], 'whole': family['whole_prospective_peer'],
                           'narrow': family['narrow_wording_and_parser_peer'],
                           'author_request': family['author_request'], 'source': family['source'],
                           'all_source_theorem_names_match_exact_peer': True})
    assert len(mappings) == 9
    assert sorted(m['key'] for m in mappings) == sorted(index['prospective_whole_keys'])
    inherited = records['primer-linalg.html::node-311']
    assert literal_fields(inherited) == literal_fields(next(r for r in baseline['material_source_units'] if r['key'] == inherited['key']))
    assert '$m,n\\ge1$' in records['primer-linalg.html::node-307']['source_text']
    assert records['primer-linalg.html::node-307']['line'] < inherited['line']
    assert 'primer-basics.html::node-922' not in [m['key'] for m in mappings]
    assert 'primer-linalg.html::node-529' not in [m['key'] for m in mappings]
    for record in inputs:
        assert exact(record).read_bytes(), record['file']
    replacements_path = OUT / 'exact-nine-replacements-and-inverse-v1.json'
    replacements_path.write_text(json.dumps({'forward': replacements,
        'inverse': [{'family': r['family'], 'source': r['source'],
                     'before': r['after'], 'after': r['before']} for r in reversed(replacements)],
        'exact_byte_inverse': True}, indent=2) + '\n')
    report = {
        'schema_version': 1,
        'status': 'approved_independent_Source81_exact_six_packet_nine_replacement_cumulative_qualification_composition',
        'errors': [], 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Exact source qualification and cumulative correspondence composition; canonical Lean audit and owner application remain Root work.',
        'index': ref(INDEX), 'original_offer': offer_ref,
        'baseline_inventory': offer['baseline_Source81_inventory'],
        'current_Source81_page_identity': {k: sha_bytes(v) for k, v in original.items()},
        'exact_candidate_pages': candidates, 'exact_replacements': ref(replacements_path),
        'packet_composition': packet_results, 'peer_and_source_reads': peer_reads,
        'fresh_baseline_full29_parser': baseline_native,
        'fresh_cumulative_full29_parser': candidate_native,
        'all29_current_inputs': inputs, 'counts_unchanged': candidate['counts'],
        'exact_changed_physical_inventory_records': changes,
        'changed_source_lines': physical_lines,
        'whole_two_page_exact_byte_inverse': True,
        'tags_attributes_script_bytes_and_line_counts_unchanged': True,
        'all_other27_page_bytes_and_unaffected_literal_fields_exact': True,
        'no_exercise_statement_changed': True,
        'whole_statement_mappings_conditional_on_exact_application_and_canonical_audit': mappings,
        'approved_prospective_whole_keys': sorted(m['key'] for m in mappings),
        'overlap_rule': '916 and 918 share the same clauses; 305 and 307 share the same table clauses. These are existing overlapping inventory rows, not additional independent mathematical claims.',
        'node311_context': {'text_unchanged': True, 'entire_candidate_literal': inherited,
            'domain_supplied_by': ['primer-linalg.html::node-305', 'primer-linalg.html::node-307'],
            'domain': 'm,n >= 1; established p-norm and Holder-conjugate exponent context remains in force.'},
        'node922': {'whole_approved': False, 'entire_candidate_literal': records['primer-basics.html::node-922'],
            'remaining': index['outstanding_correspondence'][1]['remaining_correspondence']},
        'Planar7_and_node529': 'Outside this batch; no change or approval.',
        'current_pages_owners_inventory_proof_selection_publication_mutated': False,
        'new_Lean_compile_or_aggregate_audit_claimed': False,
        'coverage_complete': False}
    path = OUT / 'independent-six-qualifier-cumulative-review-v1.json'
    path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'decision': report['status'], 'report': ref(path),
                      'candidates': candidates, 'changed': changes,
                      'wholes': report['approved_prospective_whole_keys']}))


if __name__ == '__main__':
    main()
