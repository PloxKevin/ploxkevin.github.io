"""Apply precisely reviewed corrections56-60 after completed checkpoint27 delivery.

All five full29 parser runs and evidence guards precede canonical writes.
Installed owner identities are rebased separately; no coverage is promoted.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
SELF = 'book/coverage/checks/root_apply_source56_60_v1.py'
CONTRACT = Path('/tmp/root-source56-60-full29-application-contract28-v1.json')
CONTRACT_SHA = 'be17fcaf5580436b5fd2d2e2af7a5b23f67e6089584211ab37ca8550f1a9906d'
CLOSURE = 'book/coverage/checks/future27-core/completed27-content-and-metadata-delivery-closure-v1.json'
HISTORY = ROOT/'reports/full-coverage/source-history/approved-corrections56-60-20261011'
OUT = ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json'
PEERS = [
    ('/tmp/source56-wording-probability57-independent-foundations28-v2.json','ff84d8e2882d24a2512a4ad9c64af5db31942d824a49b40bead7f287da90304f','passed_independent_source56_explicit_wording_and_probability57_narrow_source_review'),
    ('/tmp/modules-zero-sign-source58-independent-foundations-parser28-v2.json','11eaf14376112e862a9d6a91af03e6fe68be81ee05d25615fdee726750f7984e','passed_independent_source58_zero_sign_wording_and_isolated_full29_parser'),
    ('/tmp/modules-source59-exact-denominator-independent-applied-review28-v1.json','f8ffbdcf5dfc67328b8ea1086921a7236ddb3e2604abc77e0e1b3ce561070985','passed_independent_source59_exact_denominator_wording_and_isolated_full29_parser'),
    ('/tmp/mpc-source60-row-definitions-independent-foundations28-v2.json','e37a5d04c72dd58ea826472a739f7a4ef2a6f7c40479dfe315a4da3f0b19a4e5','passed_independent_source60_primary_row_definitions_and_fresh_isolated_full29_parser_review'),
]

def module(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT/file)
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value

b = module('source56_60_original_parser_guard', 'book/coverage/checks/root_apply_source54_55_v3.py')
d = module('source56_60_original_delivery_guard', 'book/coverage/checks/root_close_publication27_delivery_v5.py')
sha, read, safe, encoded = b.sha, b.read, b.safe, b.encoded

def external(n):
    p = Path(n)
    assert p.is_absolute() and (p.is_relative_to(ROOT) or p.is_relative_to('/tmp'))
    assert p.is_file() and not p.is_symlink() and p.stat().st_size < 100_000_000
    return p

def ready(closure_sha):
    assert Path(__file__).resolve() == ROOT/SELF
    assert sha(ROOT/'book/coverage/checks/root_apply_source54_55_v3.py') == '6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
    assert sha(ROOT/d.SELF) == 'f09f881b61313f847be329410eaabfc9d26a99bbd498a297229adb74bef3c561'
    assert not OUT.exists() and not HISTORY.exists()
    assert sha(CONTRACT) == CONTRACT_SHA
    contract = read(CONTRACT)
    assert contract['status'] == 'prepared_exact_cumulative_source56_to60_full29_application_contract_only'
    assert [r['correction_id'] for r in contract['steps']] == [56,57,58,59,60]
    assert sha(ROOT/CLOSURE) == closure_sha
    closure = read(ROOT/CLOSURE)
    assert closure['status'] == 'completed_checkpoint27_actual_content_and_metadata_delivery_closed'
    assert closure['both_actual_pages_runs_and_all31_live_assets_passed'] is True and closure['coverage_complete'] is False
    assert d.git(['rev-parse','HEAD']).decode().strip() == closure['metadata_commit']
    assert d.git(['ls-remote','origin','refs/heads/main']).decode().split() == [closure['metadata_commit'],'refs/heads/main']
    for n,h in closure['exact_original_evidence_sha256'].items():
        assert sha(safe(n)) == h
    assets = d.immutable()
    inv_path, corr_path = ROOT/'book/coverage/inventory.json', ROOT/'book/coverage/material-corrections.json'
    assert sha(inv_path) == contract['before_inventory']['sha256'] == '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
    assert sha(corr_path) == contract['before_corrections']['sha256'] == '21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
    corrections = read(corr_path); assert len(corrections['corrections']) == 55
    for num in range(56,61):
        assert not (ROOT/f'book/coverage/inventory-before-correction{num}.json').exists()
        assert not (ROOT/f'book/coverage/inventory-after-correction{num}.json').exists()
    peers, evidence = [], {str(CONTRACT): CONTRACT_SHA, str(ROOT/CLOSURE):closure_sha}
    for n,h,status in PEERS:
        p = external(n); assert sha(p) == h
        peer = read(p); assert peer['status'] == status and peer['errors'] == []
        r = peer.get('actual_reader_execution', peer.get('actual_independent_reader'))
        assert sha(external(r['file'])) == r['sha256']; d.zero(read(external(r['file'])))
        peers.append(peer); evidence[n] = h
        for name,digest in peer['closed_evidence_sha256'].items():
            assert name not in evidence or evidence[name] == digest
            assert sha(external(name)) == digest
            evidence[name] = digest
        evidence[r['file']] = r['sha256']
    assert [r['packet'] for r in peers[0]['results']] == [s['proposal'] for s in contract['steps'][:2]]
    assert all(r['decision']['approved'] is True for r in peers[0]['results'])
    assert peers[1]['proposal'] == contract['steps'][2]['proposal'] and peers[1]['approved_narrow_wording'] is True
    assert peers[2]['proposal'] == contract['steps'][3]['proposal'] and peers[2]['wording_decision']['approved'] is True and peers[2]['arithmetic_decision']['approved'] is True
    assert peers[3]['author_request'] == contract['steps'][4]['proposal'] and peers[3]['approved_narrow_source_correction'] is True
    candidates, parsed = {}, []
    previous = read(inv_path)
    import sys
    sys.path.insert(0,str(ROOT/'book'))
    from validate import Document
    for step in contract['steps']:
        source = step['source']; original = candidates.get(source,safe(source).read_bytes()).decode()
        assert hashlib.sha256(original.encode()).hexdigest() == step['source_sha256_before']
        p = external(step['proposal']['file']); assert sha(p) == step['proposal']['sha256']
        candidate = external(step['candidate']['file']); assert sha(candidate) == step['candidate']['sha256']
        evidence[str(p)] = sha(p); evidence[str(candidate)] = sha(candidate)
        new = original
        for r in step['exact_replacements']:
            assert new.count(r['before']) == 1 and r['after'] not in new
            new = new.replace(r['before'],r['after'],1)
        assert new.encode() == candidate.read_bytes() and new.count('\n') == original.count('\n')
        reverse = new
        for r in reversed(step['exact_replacements']):
            assert reverse.count(r['after']) == 1
            reverse = reverse.replace(r['after'],r['before'],1)
        assert reverse == original
        assert [(n.tag,n.attrs,n.line) for n in Document(original).nodes] == [(n.tag,n.attrs,n.line) for n in Document(new).nodes]
        candidates[source] = new.encode()
        data, following = b.full_parser(candidates)
        changed = b.inventory_diff(previous,following,step)
        parsed.append((step,new.encode(),data,changed)); previous = following
    assert previous['source_sha256'] == contract['final_page_sources_sha256']
    prep = ROOT/'reports/full-coverage/source56-60-contract-preparation28-execution-v1.json'
    d.zero(read(prep)); evidence[str(prep)] = sha(prep)
    prep_log = safe(read(prep)['log']); assert sha(prep_log) == read(prep)['log_sha256']; evidence[str(prep_log)] = sha(prep_log)
    for p in [ROOT/SELF,ROOT/'book/coverage/checks/root_apply_source54_55_v3.py',Path('/tmp/root_prepare_source56_60_contract28_v1.py')]:
        evidence[str(p)] = sha(p)
    return contract,closure,corrections,assets,evidence,parsed

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--closure-sha256',required=True)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    contract,closure,corrections,assets,evidence,parsed = ready(args.closure_sha256)
    if not args.apply:
        print(json.dumps({'status':'ready_exact_reviewed_source56_to60_no_canonical_writes','steps':5,'coverage_complete':False})); return
    # Every guard above precedes writes. Exact before-owner files already exist
    # as immutable reviewed candidates; reference their bytes without copying.
    owner_rows = read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']
    owners = {r['destination']:r['candidate'] for r in owner_rows}
    for n,r in owners.items():
        assert sha(safe(n)) == sha(safe(r['file'])) == r['sha256']
    original_names = ['book/coverage/inventory.json','book/coverage/material-corrections.json',*sorted({r['source'] for r in contract['steps']})]
    originals, aliases = {}, {}
    for n in original_names:
        target = HISTORY/'source55-original-root'/n
        b.write_new(target,safe(n).read_bytes()); originals[n] = b.ref(target)
        aliases[str(ROOT/n)] = b.ref(target)
    for n,r in owners.items():
        originals[n] = r; aliases[str(ROOT/n)] = r
    # Reuse exact already archived originals from the prior bounded review.
    catalog = ROOT/'book/coverage/checks/future28-foundations/original-source56-wording-probability57-independent-foundations-peer28-v1/original-closed-byte-aliases-v1.json'
    assert sha(catalog) == '3e776da374150ac84d772d7269498e624292bb8a3ebec3da419217721571a736'
    existing = read(catalog)['aliases']
    for n,h in evidence.items():
        p = external(n); assert sha(p) == h
        if n in aliases:
            assert aliases[n]['sha256'] == h; continue
        if n in existing and existing[n]['sha256'] == h:
            r = existing[n]; assert sha(safe(r['file'])) == h; aliases[n] = r; continue
        target = HISTORY/'semantic-original-by-sha256'/h/p.name
        if target.exists():
            assert sha(target) == h
        else:
            b.write_new(target,p.read_bytes())
        aliases[n] = b.ref(target)
    history = HISTORY/'preserved-history-v1.json'
    b.write_new(history,encoded({'status':'exact_source55_and_owner27_original_bytes_preserved_before_source56_to60',
        'closed_at_utc':datetime.now(timezone.utc).isoformat(),'original_root_files':originals,
        'original_absolute_byte_aliases':aliases,'completed27_delivery':b.ref(ROOT/CLOSURE),
        'original_proposal_and_review_bodies_and_times_unchanged':True,'coverage_complete':False}))
    applications = []
    for index,(step,new,data,changed) in enumerate(parsed):
        num = step['correction_id']; source = safe(step['source'])
        assert sha(source) == step['source_sha256_before'] and len(corrections['corrections']) == num-1
        before = ROOT/f'book/coverage/inventory-before-correction{num}.json'
        after = ROOT/f'book/coverage/inventory-after-correction{num}.json'
        b.write_new(before,(ROOT/'book/coverage/inventory.json').read_bytes())
        b.write_new(HISTORY/f'material-corrections-before{num}-original.json',(ROOT/'book/coverage/material-corrections.json').read_bytes())
        applied = datetime.now(timezone.utc).isoformat()
        source.write_bytes(new); (ROOT/'book/coverage/inventory.json').write_bytes(data); b.write_new(after,data)
        peer_index = 0 if num in (56,57) else num-57
        corrections['corrections'].append({'correction_id':num,'source':step['source'],
            'before_sha256':step['source_sha256_before'],'after_sha256':step['candidate']['sha256'],
            'replacements':step['exact_replacements'],'corrected_at_utc':applied,
            'status':'source_corrected_exact_independently_reviewed_scope_snippets_owner_identity_rebase_pending',
            'source_proposal':aliases[step['proposal']['file']],'independent_semantic_review':aliases[PEERS[peer_index][0]],
            'preserved_history':b.ref(history),'inventory_before':b.ref(before),'inventory_after':b.ref(after),
            'scope':'Only exact reviewed literal source changes. No mathematical coverage promotion.'})
        (ROOT/'book/coverage/material-corrections.json').write_bytes(encoded(corrections))
        assert sha(source) == step['candidate']['sha256'] and sha(ROOT/'book/coverage/inventory.json') == sha(after)
        applications.append({'correction_id':num,'applied_at_utc':applied,'source_after':b.ref(source),'inventory_before':b.ref(before),'inventory_after':b.ref(after),'exact_changed_text_keys':changed})
    manifest = read(ROOT/'reports/full-coverage/checkpoint-27-manifest.json')
    for n,r in manifest['proof_files'].items():
        assert sha(safe(n)) == r['sha256']
    changed_names = {r['source'] for r in contract['steps']}
    for n,h in assets.items():
        if n not in changed_names: assert sha(safe(n)) == h
    for n,r in owners.items(): assert sha(safe(n)) == r['sha256']
    assert len(read(ROOT/'book/coverage/material-corrections.json')['corrections']) == 60
    report = {'status':'passed_actual_source56_to60_corrections_full29_inventory_owner_identity_rebase_pending',
        'helper':b.ref(ROOT/SELF),'applications':applications,'preserved_history':b.ref(history),
        'completed27_metadata_commit':closure['metadata_commit'],'selected27_proof_sources_unchanged':1175,
        'other27_book_assets_unchanged':27,'five_installed27_owner_ledgers_unchanged':True,'coverage_complete':False,
        'scope':'Source and inventory corrections only. Five owners require separately reviewed current60 rebasing; frozen27 and every original native receipt/body/time stay exact.'}
    b.write_new(OUT,encoded(report))
    print(json.dumps({'status':'passed','corrections':[56,57,58,59,60],'inventory_sha256':sha(ROOT/'book/coverage/inventory.json'),'coverage_complete':False}))

if __name__ == '__main__':
    main()
