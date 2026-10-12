"""Bind actual installed owner29/current65 integrity to reviewed selection code."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
DEST = 'book/coverage/checks/future29-core/checkpoint29-installed-owner-selection-plan-v1.json'

def safe(n):
    assert type(n) is str and n and not Path(n).is_absolute() and '..' not in Path(n).parts and Path(n).as_posix() == n
    p = ROOT/n; assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p
def sha(n): return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def ref(n): return {'file': n, 'sha256': sha(n)}
def read(n): return json.loads(safe(n).read_bytes())
def checked(r):
    assert set(r) == {'file', 'sha256'} and sha(r['file']) == r['sha256']
    return read(r['file'])
def zero(d):
    assert type(d['actual_exit_code']) is int and d['actual_exit_code'] == 0 and d['status'] == 'passed'
    assert sha(d['log']) == d['log_sha256']

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--code-peer', required=True); ap.add_argument('--code-peer-sha256', required=True)
    args = ap.parse_args()
    peer_ref = {'file': args.code_peer, 'sha256': args.code_peer_sha256}; peer = checked(peer_ref)
    assert peer['errors'] == [] and peer['helper'] == ref('book/coverage/prepare_checkpoint29_selection_v3.py')
    helpers = peer['reviewed_helpers_sha256']; assert len(helpers) == 3 and all(sha(n) == h for n, h in helpers.items())
    integration_name = 'reports/full-coverage/owner29-reviewed-candidate-integration-v1.json'
    actual_name = 'reports/full-coverage/owner29-reviewed-candidate-integration-execution-v1.json'
    global_name = 'reports/full-coverage/root-source65-final-owner-integration29-v1.json'
    global_execution_name = 'reports/full-coverage/root-source65-final-owner-integration29-execution-v1.json'
    integration, actual, global_report, global_actual = [read(n) for n in [integration_name, actual_name, global_name, global_execution_name]]
    assert integration['applied'] is True; zero(actual); zero(global_actual)
    assert global_report['integrity_status'] == 'passed' and global_report['errors'] == [] and global_report['mathematical_coverage_complete'] is False
    binding = checked({'file': integration['binding_manifest'], 'sha256': integration['binding_manifest_sha256']})
    extras = {}
    def retain(n, h):
        assert sha(n) == h
        p = safe(n)
        if not any(p.resolve().is_relative_to((ROOT/base).resolve()) for base in ['book/coverage', 'reports/full-coverage/source-history']):
            suffix = p.suffix if p.suffix in {'.py', '.json', '.md', '.log', '.html', '.lean', '.js', '.mjs', '.cjs', '.txt'} else '.txt'
            alias = 'book/coverage/checks/future29-core/selection29-extra-original-byte-aliases-v1/'+h+'/'+p.stem+suffix
            target = safe(alias); target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists(): assert sha(alias) == h
            else:
                with target.open('xb') as f: f.write(p.read_bytes())
            n = alias
        row = {'sha256': h, 'scope': 'immutable_audit_or_local_source_evidence'}
        assert n not in extras or extras[n] == row; extras[n] = row
    for owner, row in binding['owners'].items():
        offer = checked(row['reviewed_offer'])
        for n, r in offer.get('additional_frozen_inputs', {}).items():
            h = r if type(r) is str else r['sha256']
            if type(r) is dict: assert set(r) == {'sha256', 'scope'} and r['scope'] == 'immutable_audit_or_local_source_evidence'
            retain(n, h)
    closure_name = 'book/coverage/checks/future29-core/original-root29-preintegration-native-v1/original-closed-byte-aliases-v1.json'
    closure = read(closure_name)
    for r in closure['aliases'].values(): retain(r['file'], r['sha256'])
    retain(closure_name, sha(closure_name))
    for r in binding['additional_immutable_inputs']: retain(r['file'], r['sha256'])
    for n in ['reports/full-coverage/root29-preintegration-originals-close-execution-v1.json', 'book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json']:
        retain(n, sha(n))
        d = read(n)
        if 'actual_exit_code' in d: zero(d); retain(d['log'], d['log_sha256'])
    result = {'status': 'exact_current65_owner29_and_eleven_sources_explicit_selection_plan',
              'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'independent_selection_helper_review': peer_ref,
              'expected_independent_selection_helper_review_status': peer['status'], 'helpers_sha256': helpers,
              'baseline_selection': ref('reports/full-coverage/checkpoint-28-selection.json'),
              'baseline_manifest': ref('reports/full-coverage/checkpoint-28-manifest.json'),
              'baseline_audit': ref('reports/full-coverage/lean-checkpoint-28/verification-original.json'),
              'inventory': ref('book/coverage/inventory-after-correction65.json'), 'integration_result': ref(integration_name),
              'actual_integration_execution': ref(actual_name), 'global_integrity': ref(global_name),
              'actual_global_integrity_execution': ref(global_execution_name), 'additional_frozen_inputs': extras, 'coverage_complete': False}
    p = safe(DEST); assert not p.exists(); p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write((json.dumps(result, indent=2)+'\n').encode())
    print(json.dumps({'status': result['status'], 'plan': ref(DEST), 'additional_exact_frozen_inputs': len(extras)}))

if __name__ == '__main__': main()
