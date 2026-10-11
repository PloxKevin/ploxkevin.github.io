"""Apply four independently reviewed source clarifications after delivered25.

No proof, owner ledger, frozen checkpoint, or semantic-review body is rewritten.
The fresh complete inventory is parsed in isolation before any source mutation.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, shutil, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
HISTORY = REPORTS / 'source-history/approved-mpc-scenario-scope-correction53-20261011'
OUT = REPORTS / 'source53-correction-application-v1.json'
PROPOSAL = Path('/tmp/foundations-hertneck-and-scenario-source53-qualification-proposal26-v1.json')
PEER = Path('/tmp/hertneck-scenario-source53-independent-applied-semantic-and-full-parser-review26-v1.json')
PROPOSAL_SHA = '9b3018d98c731db5f708f588aa69cfc8d1da1bd51d88375055a6c584d37d3323'
PEER_SHA = '349044d041663e5aaf6f59307297b4f01406d01c3a578d8544f2955f3c20a40e'
INVENTORY_SHA = '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(p):
    return json.loads(p.read_text())


def ref(p):
    return {'file': p.relative_to(ROOT).as_posix(), 'sha256': sha(p)}


def write_new(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as stream:
        stream.write(data)


def encoded(data):
    return (json.dumps(data, indent=2) + '\n').encode()


def main():
    assert not HISTORY.exists() and not OUT.exists()
    inventory_path = ROOT / 'book/coverage/inventory.json'
    corrections_path = ROOT / 'book/coverage/material-corrections.json'
    after_path = ROOT / 'book/coverage/inventory-after-correction53.json'
    before_path = ROOT / 'book/coverage/inventory-before-correction53.json'
    assert not after_path.exists() and not before_path.exists()
    assert sha(PROPOSAL) == PROPOSAL_SHA and sha(PEER) == PEER_SHA
    proposal, peer = read(PROPOSAL), read(PEER)
    assert peer['proposal_approved'] is True and peer['errors'] == []
    assert peer['proposal'] == {'file': str(PROPOSAL), 'sha256': PROPOSAL_SHA}
    assert peer['entire_original_proposal_body_and_preparation_time'] == proposal
    assert len(proposal['replacements']) == len(peer['replacement_decisions']) == 4
    assert all(row['approved'] is True and row['missing_clauses'] == []
               for row in peer['replacement_decisions'])
    assert sha(inventory_path) == sha(ROOT / 'book/coverage/inventory-after-correction52.json') == INVENTORY_SHA
    corrections = read(corrections_path)
    assert len(corrections['corrections']) == 52
    assert [row['correction_id'] for row in corrections['corrections']] == list(range(1, 53))
    manifest = read(REPORTS / 'checkpoint-25-manifest.json')
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert len(manifest['proof_files']) == 1156
    protected = {n: row['sha256'] for n, row in manifest['proof_files'].items()}
    protected.update(proposal['current31_assets_sha256'])
    owners = {'book/coverage/' + name + '.json': value
              for name, value in proposal['current5_installed25_owner_sha256'].items()}
    protected.update(owners)
    assert len(proposal['current31_assets_sha256']) == 31 and len(owners) == 5
    for name, digest in protected.items():
        assert sha(ROOT / name) == digest, name
    progress = read(ROOT / 'book/coverage/progress.json')
    assert progress['publication_status'] == 'checkpoint25_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
    for stem in ['live25-attempt1-execution-v1', 'live25-attempt2-execution-v1',
                 'publication25-content-push-execution-v1',
                 'publication25-delivery-metadata-push-execution-v1']:
        actual = read(REPORTS / (stem + '.json'))
        assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
        assert sha(ROOT / actual['log']) == actual['log_sha256']
    live = read(REPORTS / 'live-checkpoint-25-attempt2.json')
    pages = read(REPORTS / 'pages-checkpoint-25-attempt2.json')
    assert live['status'] == 'passed_all31_asset_sha256' and len(live['assets']) == 31
    assert live['commit'] == live['remote_main'] == pages['commit'] == pages['expected_commit']
    assert pages['status'] == 'passed'
    assert subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT / 'reports/book/publication-repo',
                          check=True, capture_output=True).stdout.decode().strip() == live['commit']
    assert {row['source']: row['actual_sha256'] for row in live['assets']} == proposal['current31_assets_sha256']
    for row in live['assets']:
        assert row['http_status'] == 200 and row['matches'] is True
        assert row['actual_sha256'] == row['expected_sha256']
    source = ROOT / proposal['source']
    assert sha(source) == proposal['source_sha256_before']
    old_text = source.read_text()
    new_text = old_text
    for row in proposal['replacements']:
        assert row['count'] == 1 and new_text.count(row['before']) == 1
        assert row['after'] not in new_text
        new_text = new_text.replace(row['before'], row['after'], 1)
    assert hashlib.sha256(new_text.encode()).hexdigest() == proposal['proposed_source_sha256_after']
    reverse = new_text
    for row in reversed(proposal['replacements']):
        assert reverse.count(row['after']) == 1
        reverse = reverse.replace(row['after'], row['before'], 1)
    assert reverse == old_text and new_text.count('\n') == old_text.count('\n')
    old_inventory = read(inventory_path)
    parser_path = ROOT / 'book/inventory_claims.py'
    parser_sha = sha(parser_path)
    assert parser_sha == 'b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
    # Execute the existing full parser with a fresh isolated root and output.
    with tempfile.TemporaryDirectory(prefix='root-source53-parser-') as temporary:
        isolated = Path(temporary)
        (isolated / 'SafeLearning').mkdir()
        for page in (ROOT / 'SafeLearning').glob('*.html'):
            if page == source:
                (isolated / 'SafeLearning' / page.name).write_text(new_text)
            else:
                (isolated / 'SafeLearning' / page.name).symlink_to(page)
        sys.path.insert(0, str(ROOT / 'book'))
        spec = importlib.util.spec_from_file_location('source53_complete_inventory_parser', parser_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        module.ROOT = isolated
        module.OUT = isolated / 'book/coverage'
        module.inventory()
        new_inventory_path = module.OUT / 'inventory.json'
        new_inventory_bytes = new_inventory_path.read_bytes()
        new_inventory = read(new_inventory_path)
    assert sha(parser_path) == parser_sha
    assert new_inventory['counts'] == old_inventory['counts']
    assert new_inventory['counts']['material_source_units'] == 12774
    assert new_inventory['counts']['exercises'] == 556
    assert len(new_inventory['source_sha256']) == 29
    assert new_inventory['source_sha256'] == {
        **old_inventory['source_sha256'], proposal['source']: proposal['proposed_source_sha256_after']}
    changed = {}
    for field in ['exercises', 'material_source_units']:
        before = {row['key']: row for row in old_inventory[field]}
        after = {row['key']: row for row in new_inventory[field]}
        assert before.keys() == after.keys()
        changed[field] = []
        for key in before:
            a, b = dict(before[key]), dict(after[key])
            if a['source'] == proposal['source']:
                assert b['source_sha256'] == proposal['proposed_source_sha256_after']
                a.pop('source_sha256'); b.pop('source_sha256')
            if a != b:
                assert {k: v for k, v in a.items() if k not in {'source_text', 'text_sha256'}} == {
                    k: v for k, v in b.items() if k not in {'source_text', 'text_sha256'}}
                changed[field].append(key)
        assert changed[field] == proposal['exact_changed_text_keys'][field]
    # All guards and the independent full parser have passed before first write.
    original_refs = {str(PROPOSAL): PROPOSAL_SHA, str(PEER): PEER_SHA,
                     **peer['closed_evidence_sha256']}
    for original_name, digest in original_refs.items():
        original = Path(original_name)
        assert original.is_absolute() and original.is_file() and not original.is_symlink()
        assert original.is_relative_to(ROOT) or original.parent == Path('/tmp')
        assert sha(original) == digest
    copies = {}
    for original in [source, inventory_path, corrections_path, *(ROOT / n for n in owners)]:
        target = HISTORY / original.relative_to(ROOT)
        write_new(target, original.read_bytes())
        assert sha(target) == sha(original)
        copies[original.relative_to(ROOT).as_posix()] = ref(target)
    aliases = {}
    for original_name, digest in original_refs.items():
        original = Path(original_name)
        assert original.is_absolute() and original.is_file() and sha(original) == digest
        if original.is_relative_to(ROOT):
            target = HISTORY / 'semantic-original-root' / original.relative_to(ROOT)
        else:
            assert original.parent == Path('/tmp')
            target = HISTORY / 'semantic-original-tmp' / original.name
        # Primary source text is archived as raw log bytes for the freezer.
        if target.suffix == '.txt':
            target = target.with_suffix('.txt.log')
        if not target.exists():
            write_new(target, original.read_bytes())
        assert sha(target) == digest
        aliases[original_name] = ref(target)
    preserved_path = HISTORY / 'preserved-history.json'
    write_new(preserved_path, encoded({'status': 'exact_source52_and_owner25_original_bytes_preserved_before_source53',
        'closed_at_utc': datetime.now(timezone.utc).isoformat(), 'original_root_files': copies,
        'original_absolute_byte_aliases': aliases,
        'entire_original_proposal_body_and_time': proposal,
        'entire_original_independent_semantic_review_body_and_time': peer}))
    write_new(before_path, inventory_path.read_bytes())
    source.write_text(new_text)
    inventory_path.write_bytes(new_inventory_bytes)
    write_new(after_path, new_inventory_bytes)
    corrected_at = datetime.now(timezone.utc).isoformat()
    correction = {'correction_id': 53, 'source': proposal['source'], 'line': 517,
        'before_sha256': proposal['source_sha256_before'],
        'after_sha256': proposal['proposed_source_sha256_after'],
        'replacements': proposal['replacements'], 'corrected_at_utc': corrected_at,
        'status': 'source_corrected_exact_independently_reviewed_four_scope_snippets_owner_identity_rebase_pending',
        'historical_source': copies[proposal['source']]['file'],
        'historical_source_sha256': proposal['source_sha256_before'],
        'preserved_history': ref(preserved_path), 'independent_semantic_review': aliases[str(PEER)],
        'scope': 'Explicit finite-entry switched validation event and actual original-objective unique scenario optimisation assumptions. No new whole exercise or material approval.'}
    corrections['corrections'].append(correction)
    corrections_path.write_bytes(encoded(corrections))
    for name, digest in protected.items():
        if name != proposal['source']:
            assert sha(ROOT / name) == digest, name
    assert sha(source) == proposal['proposed_source_sha256_after']
    assert sha(inventory_path) == sha(after_path)
    record = {'status': 'passed_actual_source53_correction_and_full29_page_inventory_owner_identity_rebase_pending',
        'applied_at_utc': corrected_at, 'helper': ref(Path(__file__)),
        'source_before': copies[proposal['source']], 'source_after': ref(source),
        'inventory_before': ref(before_path), 'inventory_after': ref(after_path),
        'changed_text_keys': changed, 'full29_page_parser': ref(parser_path),
        'preserved_history': ref(preserved_path), 'delivered25_metadata_commit': live['commit'],
        'selected25_proof_sources_unchanged': 1156, 'other30_book_assets_unchanged': 30,
        'five_installed25_owner_ledgers_unchanged': True, 'coverage_complete': False,
        'scope': 'Actual source/inventory clarification only. Frozen25 and all original semantic review bodies/times remain exact; current owner identities require separate source53 review and integration.'}
    write_new(OUT, encoded(record))
    print(json.dumps({'status': 'passed', 'correction': 53, 'changed_text_keys': changed,
                      'inventory_sha256': sha(after_path), 'coverage_complete': False}))


if __name__ == '__main__':
    main()
