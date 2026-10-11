"""Close the exact Foundation27 canonical offer with its independent peer.

Only a new reviewed offer and immutable evidence aliases are written. Root must
review this helper before --apply; original mathematics, candidate and offer stay
byte-exact, and this makes no installed-owner or aggregate claim.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'book/coverage/checks/foundations-future27/source55'
OFFER = BASE / 'foundations-audit27-candidate-source55-additions-v1.json'
OFFER_SHA = '5114ee9d15f977df95dae5e98c47e84f2ae07dd7224c00270da5d650d1b485e2'
DEST = BASE / 'foundations-audit27-candidate-source55-additions-v1-reviewed.json'
ARCHIVE = BASE / 'original-final-mapping-peer-v1'
PEER = Path('/tmp/foundations27-current55-canonical-final-mapping-independent-applied-confirmation-v1.json')
PEER_SHA = 'dcd4ff33a0e23f13d75d1f049c995b2a50ef4c7949461792e4e5a79a17d33c1e'
ACTUAL = 'reports/full-coverage/foundations27-current55-canonical-binding-execution-v1.json'
ACTUAL_SHA = '2ad417566e50cbfb7d641dcab251c1d93ed1dad62de38f2649710dfe1210f165'
BUILDER = 'book/coverage/checks/root_finalize_foundations27_current55_v1.py'
BUILDER_SHA = 'eefc6488a65b9ce326488e909ae09ec80ca69b33b9feac96792b1ae8a37bc24b'
OLD = 'book/coverage/foundations.json'
OLD_SHA = '60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a'
INV_SHA = '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
ORIGINAL_AUTHOR_PREFLIGHT_SHA256 = {'book/coverage/checks/root_close_foundations27_reviewed_offer_v1.py': '379af66e2322a04321b550ef019aa9567ff438bb03fe5c590296540dcad59cd7', '/tmp/check-foundations27-reviewed-offer-closure-preflight-v1.py': '91fabc0052dbd8b57956e9d4ffe08341456b70ba5b3bc42527bef9125243271e', '/tmp/run-foundations27-reviewed-offer-closure-preflight-v1.py': '0df41832525612434c9f78c1df79875a4046253c45717610eee4a2a6e3388087', '/tmp/foundations27-reviewed-offer-closure-preflight-actual-v1.json': '35695f37ab36ee9f4a675b17eec19ab357138619664aba3a8d4da0a8bc8a52a6', '/tmp/foundations27-reviewed-offer-closure-preflight-actual-v1.log': '78517197686634900f145652dd752e05938155375cc14a56a873a02e784cd851'}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_bytes())
def locate(name):
    assert isinstance(name, str)
    p = Path(name)
    if p.is_absolute():
        assert p.is_relative_to(ROOT) or p.is_relative_to(Path('/tmp'))
    else:
        assert str(p) == name and '..' not in p.parts
        p = ROOT / p
    assert p.is_file() and not p.is_symlink()
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
    return p
def checked(ref):
    assert set(ref) == {'file', 'sha256'} and re.fullmatch('[0-9a-f]{64}', ref['sha256'])
    p = locate(ref['file']); assert sha(p) == ref['sha256'], str(p)
    return p
def ref(p): return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p)}
def zero(d):
    codes = [d[k] for k in ('actual_exit_code', 'exit_code', 'actual_runner_exit_code') if k in d]
    assert codes and all(type(c) is int and c == 0 for c in codes)
def write(p, d):
    with p.open('x') as f: f.write(json.dumps(d, ensure_ascii=False, indent=2) + '\n')

def prepare():
    assert not DEST.exists() and not ARCHIVE.exists()
    checked({'file': str(OFFER), 'sha256': OFFER_SHA})
    checked({'file': str(PEER), 'sha256': PEER_SHA})
    checked({'file': OLD, 'sha256': OLD_SHA})
    checked({'file': 'book/coverage/inventory.json', 'sha256': INV_SHA})
    old = read(OFFER); peer = read(PEER)
    assert old['status'] == 'paired_isolated_current55_foundations_candidate_awaiting_final_independent_mapping_review'
    assert old['final_independent_candidate_mapping_peer_pending'] is True
    assert old['actual_finalizer_record_pending'] is True
    assert old['new_proof_file_count'] == len(old['proof_files']) == 3
    assert old['new_theorem_or_lemma_count'] == 43 and old['actual_canonical_commands'] == 6
    assert peer['status'] == 'passed_independent_exact_foundations27_current55_canonical_three_source43_final_mapping_mechanics'
    assert peer['errors'] == [] and peer['reviewed_at_utc']
    assert peer['reviewed_offer'] == ref(OFFER)
    assert peer['candidate'] == old['candidate']
    assert peer['canonical_binding'] == old['material27_exact_interface_binding']
    for key in ['exact_canonical_inverse_to_entire_reviewed_tmp_draft',
                'exact_composed_inverse_to_entire_installed26_foundations',
                'all_five_original_whole_claim_reasons_hypotheses_names_times_exact',
                'all119_exercises_247_old_proof_rows_nonpending_material_rows_exact',
                'all_old1167_and_new8_canonical_sources_and_current55_assets_and_five_owners_exact']:
        assert peer[key] is True
    assert peer['new_proof_file_count'] == 3 and peer['new_public_theorem_count'] == 43
    commands = peer['genuine_canonical_compiler_commands']
    assert isinstance(commands, list) and len(commands) == 6
    expected_pairs = {(n, kind) for n in old['proof_files'] for kind in ['standalone', 'named']}
    seen_pairs = set()
    for row in commands:
        native = read(checked(row['native_record'])); zero(native)
        assert native == row['entire_native_actual_body_time_and_log']
        n = native['source']; kind = row['kind']; assert (n, kind) in expected_pairs
        assert (n, kind) not in seen_pairs; seen_pairs.add((n, kind))
        h = old['proof_files'][n]['sha256']
        assert native['source_sha256_before'] == native['source_sha256_after'] == h
        assert native['source_unchanged'] is True
        expected_command = ['lake', 'env', 'lean', 'SafeLearning/' + Path(n).name] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + Path(n).stem]
        assert native['command'] == expected_command and native['actual_workdir'] == str(ROOT / 'verification/lean')
        assert row['raw_log'] == {'file': native['log'], 'sha256': native['log_sha256']}
        checked(row['raw_log']); checked({'file': n, 'sha256': h})
    assert seen_pairs == expected_pairs
    checked(old['candidate']); checked(old['material27_exact_interface_binding'])
    actual_path = checked({'file': ACTUAL, 'sha256': ACTUAL_SHA}); actual = read(actual_path); zero(actual)
    assert peer['actual_root_finalizer'] == {'file': ACTUAL, 'sha256': ACTUAL_SHA}
    assert peer['entire_original_actual_finalizer_body_time'] == actual
    assert actual['actual_command'] == ['python3', BUILDER, '--apply'] and actual['actual_workdir'] == str(ROOT)
    assert actual['helper_sha256_before'] == actual['helper_sha256_after'] == {BUILDER: BUILDER_SHA}
    checked({'file': BUILDER, 'sha256': BUILDER_SHA})
    checked({'file': actual['log'], 'sha256': actual['log_sha256']})
    peer_actual_path = checked(peer['actual_independent_final_mapping_checker'])
    peer_actual = read(peer_actual_path); zero(peer_actual)
    assert peer_actual['actual_workdir'] == str(ROOT)
    assert peer_actual['actual_command'] == ['python3', '/tmp/check-foundations27-current55-canonical-final-mapping-independent-applied-v1.py']
    checker = checked({'file': peer_actual['actual_command'][1], 'sha256': peer_actual['checker_sha256_after']})
    assert peer_actual['checker_sha256_before'] == peer_actual['checker_sha256_after'] == sha(checker)
    checked({'file': peer_actual['raw_log'], 'sha256': peer_actual['raw_log_sha256']})
    closed = peer['closed_evidence_sha256']; assert isinstance(closed, dict)
    for n, h in closed.items(): checked({'file': n, 'sha256': h})
    for n, h in old['additional_frozen_inputs'].items(): checked({'file': n, 'sha256': h})
    # Raw TMP histories already archived by the first finalizer reuse its exact
    # aliases. New peer/reader originals get content-addressed copies below.
    existing = old['original_closed_byte_aliases']; aliases = {}; copies = {}
    def add(n, h):
        p = checked({'file': n, 'sha256': h})
        key = n + '::' + h
        if key in existing:
            target_ref = existing[key]['immutable_byte_copy']
            checked(target_ref); assert target_ref['sha256'] == h
        elif p.is_relative_to(ROOT):
            target_ref = {'file': str(p.relative_to(ROOT)), 'sha256': h}
        else:
            target = ARCHIVE / h / p.name
            target_ref = {'file': str(target.relative_to(ROOT)), 'sha256': h}
            assert not target.exists()
            if target in copies: assert copies[target] == (p, h)
            else: copies[target] = (p, h)
        aliases[n] = {'file': target_ref['file'], 'sha256': h}
        return target_ref
    add(str(PEER), PEER_SHA)
    for n, h in ORIGINAL_AUTHOR_PREFLIGHT_SHA256.items(): add(n, h)
    original_preflight = read(locate('/tmp/foundations27-reviewed-offer-closure-preflight-actual-v1.json'))
    assert type(original_preflight['actual_exit_code']) is int and original_preflight['actual_exit_code'] == 1
    for n, h in closed.items():
        if Path(n).is_absolute(): add(n, h)
    add(ACTUAL, ACTUAL_SHA); add(actual['log'], actual['log_sha256'])
    new = copy.deepcopy(old)
    updates = {
        'status': 'independently_reviewed_isolated_foundations27_current55_three_source43_five_whole_unit_offer',
        'final_independent_candidate_mapping_peer_pending': False,
        'actual_finalizer_record_pending': False,
        'finalized_at_utc': datetime.now(timezone.utc).isoformat(),
        'actual_builder_record': ACTUAL,
        'actual_builder_record_sha256': ACTUAL_SHA,
        'actual_builder_raw_log': {'file': actual['log'], 'sha256': actual['log_sha256']},
        'final_independent_candidate_mapping_peer': aliases[str(PEER)],
        'original_final_independent_peer_body_and_time': peer,
        'final_independent_peer_actual_execution': aliases[str(peer_actual_path)],
        'final_independent_peer_raw_log': aliases[peer_actual['raw_log']],
        'final_independent_peer_checker': aliases[str(checker)],
        'final_independent_peer_runner': aliases['/tmp/run-foundations27-current55-canonical-final-mapping-independent-applied-v1.py'],
        'final_independent_peer_exact_original_provenance': aliases,
        'offer_finalization_helper': ref(Path(__file__)),
        'scope': 'Isolated independently reviewed Foundation3/43 canonical offer and five whole literal mappings. Every original mathematical body, hypothesis, time and failure is retained. Root actual finalizer and final independent checker are closed; installed-owner, selection, aggregate and publication claims remain pending.'
    }
    original_fields = {k: {'present': k in old, 'value': copy.deepcopy(old.get(k))} for k in updates}
    new.update(updates)
    new['additional_frozen_inputs'] = copy.deepcopy(old['additional_frozen_inputs'])
    for row in aliases.values(): new['additional_frozen_inputs'][row['file']] = row['sha256']
    for n, h in closed.items():
        if not Path(n).is_absolute() and n.startswith('book/coverage/'):
            new['additional_frozen_inputs'][n] = h
    new['additional_frozen_inputs'][str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    new['offer_finalization'] = {
        'original_offer': ref(OFFER), 'original_fields': original_fields,
        'original_additional_frozen_inputs': old['additional_frozen_inputs'],
        'entire_candidate_proof_rows_and_math_bodies_times_unchanged': True,
        'original_author_preflight_sha256': ORIGINAL_AUTHOR_PREFLIGHT_SHA256,
        'entire_original_author_preflight_failure_body_and_time': original_preflight,
        'original_author_preflight_failure_reason': 'The first author preflight expected integer6, whereas the exact independent peer has a list of six full native command records. Version2 validates all six native records without changing the peer.',
        'scope': 'Reversible evidence/status closure only; no semantic redecision.'
    }
    inverse = copy.deepcopy(new); inverse.pop('offer_finalization')
    inverse['additional_frozen_inputs'] = old['additional_frozen_inputs']
    for k, row in original_fields.items():
        if row['present']: inverse[k] = row['value']
        else: inverse.pop(k)
    assert inverse == old and new['proof_files'] == old['proof_files'] and new['candidate'] == old['candidate']
    assert new['coverage_complete'] is False
    return old, new, copies

def execute():
    helper_sha = sha(Path(__file__)); old, new, copies = prepare()
    ARCHIVE.mkdir()
    for target, (source, h) in copies.items():
        assert sha(source) == h; target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as f: f.write(source.read_bytes())
        assert sha(target) == h
    for n, h in new['additional_frozen_inputs'].items(): checked({'file': n, 'sha256': h})
    write(DEST, new)
    assert sha(OFFER) == OFFER_SHA and sha(ROOT / OLD) == OLD_SHA
    assert sha(ROOT / 'book/coverage/inventory.json') == INV_SHA and sha(Path(__file__)) == helper_sha
    print(json.dumps({'status': 'passed_isolated_reviewed_foundations27_offer_closure',
                      'reviewed_offer': ref(DEST), 'candidate': new['candidate'],
                      'original_offer_unchanged': True, 'source_count': 3, 'exports': 43,
                      'canonical_commands': 6, 'installed_owner_write': False}))

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--apply', action='store_true')
    assert p.parse_args().apply, 'Root must review before explicit --apply'
    execute()
