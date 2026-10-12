"""Bind four reviewed current65 candidates and their actual compiler records."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json

ROOT = Path(__file__).resolve().parents[3]
DEST = 'book/coverage/checks/future29-core/current65-owner29-binding-v1.json'
INSTALLER = 'book/coverage/checks/root_integrate_owner29_candidates_v1.py'
INSTALLER_SHA = 'f146d32801dbc4f174121decde8596021e9b79c808aa36e8e01f3569f3b1ff84'
CONTEXT = Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
CONTEXT_SHA = '10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'

def safe(n):
    assert type(n) is str and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    p = ROOT/n
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p
def sha(n): return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n): return json.loads(safe(n).read_bytes())
def ref(n): return {'file': n, 'sha256': sha(n)}
def checked(r):
    assert set(r) == {'file', 'sha256'} and sha(r['file']) == r['sha256']
    return read(r['file'])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--offers', required=True, help='Root-relative JSON map of the four exact final offer references.')
    ap.add_argument('--offers-sha256', required=True)
    ap.add_argument('--code-peer', required=True)
    ap.add_argument('--code-peer-sha256', required=True)
    args = ap.parse_args()
    offers = checked({'file': args.offers, 'sha256': args.offers_sha256})
    assert set(offers) == {'core', 'foundations', 'applied', 'modules'}
    assert sha(INSTALLER) == INSTALLER_SHA
    code_peer = checked({'file': args.code_peer, 'sha256': args.code_peer_sha256})
    assert code_peer['helper'] == ref(INSTALLER) and code_peer['errors'] == [] and code_peer['status'].startswith('passed_')
    assert hashlib.sha256(CONTEXT.read_bytes()).hexdigest() == CONTEXT_SHA
    context = json.loads(CONTEXT.read_bytes())
    for n, h in {**context['pins_sha256'], **context['held_current_source_sha256']}.items(): assert sha(n) == h
    spec = importlib.util.spec_from_file_location('reviewed_owner29_installer', safe(INSTALLER))
    installer = importlib.util.module_from_spec(spec); spec.loader.exec_module(installer)
    owners = {}
    for owner, offer_ref in offers.items():
        offer = checked(offer_ref); candidate = offer['candidate']; checked(candidate)
        peer_ref = offer.get('final_mapping_peer') or offer['final_independent_candidate_mapping_peer']
        peer = checked(peer_ref)
        assert peer['errors'] == [] and peer['candidate'] == candidate
        original_peer = peer
        if not peer['status'].startswith('passed_'):
            assert peer['status'] == 'exact_original_independent_peer_pointer_alias_interface'
            original_peer = checked(peer['original_peer'])
            assert original_peer['errors'] == [] and original_peer['status'] == peer['original_peer_status']
            assert original_peer['status'].startswith('passed_') and peer['original_peer_body_and_review_time_preserved'] is True
        actual_ref = peer['actual_finalizer']
        if 'final_independent_mapping_actual' in offer:
            assert offer['final_independent_mapping_actual'] == actual_ref
        actual = checked(actual_ref)
        assert peer['actual_finalizer'] == actual_ref and type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
        log_fields = ['log', 'log_sha256'] if 'log' in actual else ['raw_log', 'raw_log_sha256']
        supplied_aliases = offer.get('actual_finalizer_original_byte_aliases') or peer.get('actual_finalizer_original_byte_aliases') or original_peer['actual_finalizer_original_byte_aliases']
        needed = {n: h for n, h in actual['helper_sha256_before'].items() if Path(n).is_absolute()}
        if Path(actual[log_fields[0]]).is_absolute(): needed[actual[log_fields[0]]] = actual[log_fields[1]]
        aliases = {}
        for n, h in needed.items():
            r = supplied_aliases[n]
            assert r['sha256'] == h and sha(r['file']) == h
            aliases[n] = {'file': r['file'], 'sha256': h}
        dest = 'book/coverage/'+owner+'.json'
        assert sha(dest) == installer.OLD[owner]
        row = {'destination': dest, 'installed28_sha256': installer.OLD[owner],
               'candidate': candidate, 'reviewed_offer': offer_ref, 'final_mapping_peer': peer_ref,
               'expected_final_mapping_peer_status': peer['status'],
               'offer_candidate_pointer': ['candidate'], 'peer_candidate_pointer': ['candidate'],
               'peer_actual_finalizer_pointer': ['actual_finalizer'], 'actual_finalizer': actual_ref,
               'expected_actual_finalizer_status': actual['status'],
               'expected_actual_finalizer_command': actual['actual_command'],
               'expected_actual_finalizer_helpers_sha256': actual['helper_sha256_before'],
               'actual_finalizer_log_fields': log_fields, 'actual_finalizer_original_byte_aliases': aliases,
               'new_sources': {n: p['sha256'] for n, p in offer['proof_files'].items()}}
        if owner == 'applied':
            assert peer['candidate_promotions'] == offer['candidate_promotions']
            row['companion_candidates'] = [{'destination': 'book/coverage/applied-promotions.json',
                 'candidate': offer['candidate_promotions'], 'offer_candidate_pointer': ['candidate_promotions'],
                 'peer_candidate_pointer': ['candidate_promotions']}]
        owners[owner] = row
    batches = []
    for readiness, execution, count, theorems in [
        ('book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json', 'reports/full-coverage/current65-canonical-pairs10-application29-execution-v1.json', 10, 202),
        ('book/coverage/checks/future29-core/current65-monitoring29-canonical-pair-v1/actual-reviewed29-canonical-paired-readiness-v1.json', 'reports/full-coverage/current65-monitoring29-canonical-pair-application-execution-v1.json', 1, 16)]:
        actual, compiler = read(execution), read(readiness)
        assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
        assert compiler['errors'] == [] and compiler['source_count'] == count and compiler['public_theorem_count'] == theorems
        batches.append({'readiness': ref(readiness), 'actual_execution': ref(execution),
                        'expected_command': actual['actual_command'], 'expected_helper_sha256': actual['helper_sha256_before'],
                        'expected_readiness_status': compiler['status'], 'source_count': count, 'public_theorem_count': theorems})
    assets = {n: h for n, h in context['held_current_source_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets) == 31
    for n, h in assets.items(): assert sha(n) == h
    additional_names = [
        args.offers, 'book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json',
        'reports/full-coverage/source61-64-corrections-application-v1.json',
        'reports/full-coverage/source61-64-corrections-application29-execution-v1.json',
        'reports/full-coverage/source65-correction-application-v1.json',
        'reports/full-coverage/source65-correction-application29-execution-v1.json',
        'reports/full-coverage/integration-29-source65-static-v1.json',
        'reports/full-coverage/integration29-source65-static-execution-v1.json',
        'book/coverage/checks/future29-core/original-root29-preintegration-native-v1/original-closed-byte-aliases-v1.json',
        'reports/full-coverage/browser-checkpoint-29.json', 'reports/full-coverage/browser-corrections-29-inputs.json',
        'reports/full-coverage/browser29-evidence-merge-execution-v1.json',
        'reports/full-coverage/source65-four-page-math-scroll29-v2.json',
        'reports/full-coverage/source65-four-page-math-scroll29-execution-v2.json']
    additional = [ref(n) for n in additional_names]
    for n in additional_names:
        d = read(n)
        if 'actual_exit_code' in d:
            assert type(d['actual_exit_code']) is int and d['actual_exit_code'] == 0
            assert sha(d['log']) == d['log_sha256']
            additional.append({'file': d['log'], 'sha256': d['log_sha256']})
    result = {'status': 'all_four_reviewed_current65_owner29_candidates_bound_ready_for_root_execution',
              'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'helper': ref(INSTALLER),
              'independent_helper_review': {'file': args.code_peer, 'sha256': args.code_peer_sha256},
              'expected_independent_helper_review_status': code_peer['status'],
              'inventory': ref('book/coverage/inventory-after-correction65.json'),
              'baseline28_selection': ref('reports/full-coverage/checkpoint-28-selection.json'),
              'exact_current65_safelearning_assets_sha256': assets, 'additional_immutable_inputs': additional,
              'canonical_pair_batches': batches, 'owners': owners, 'coverage_complete': False,
              'owner_installation_or_global_audit_claimed': False}
    p = safe(DEST); assert not p.exists(); p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write((json.dumps(result, indent=2)+'\n').encode())
    print(json.dumps({'status': result['status'], 'binding': ref(DEST), 'owners': 4, 'candidate_files': 5, 'new_sources': 11}))

if __name__ == '__main__': main()
