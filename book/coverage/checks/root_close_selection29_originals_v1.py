"""Archive exact real selection preparation records, including failed attempts."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
DEST = 'book/coverage/checks/future29-core/original-root29-selection-native-v1'
BINDING = 'book/coverage/checks/future29-core/current65-owner29-binding-v1.json'
NATIVES = [
    'owner29-binding-preparation-execution-v1',
    'owner29-reviewed-candidate-preflight-execution-v1',
    'owner29-reviewed-candidate-integration-execution-v1',
    'root-source65-final-owner-integration29-execution-v1',
    *['selection29-plan-preparation-execution-v'+str(i) for i in range(1,5)],
    *['selection29-preflight-execution-v'+str(i) for i in range(1,5)],
    'selection29-application-execution-v1']

def safe(n):
    assert type(n) is str and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    p = ROOT/n
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p
def sha(n): return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n): return json.loads(safe(n).read_bytes())
def ref(n): return {'file': n, 'sha256': sha(n)}

def main():
    assert not safe(DEST).exists()
    selection = read('reports/full-coverage/checkpoint-29-selection.json')
    binding = read(BINDING)
    held = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    held.update(binding['exact_current65_safelearning_assets_sha256'])
    for r in binding['owners'].values():
        held[r['destination']] = r['candidate']['sha256']
        for c in r.get('companion_candidates', []): held[c['destination']] = c['candidate']['sha256']
    held['book/coverage/inventory.json'] = binding['inventory']['sha256']
    held['book/coverage/material-corrections.json'] = '5c3a871bbc5782a02c5b19bfa33a8fa6e4dc311a9e72c525d76fcc526f37eafd'
    held['reports/full-coverage/checkpoint-29-selection.json'] = sha('reports/full-coverage/checkpoint-29-selection.json')
    assert len(selection['proof_files']) == 1197
    assert all(sha(n) == h for n, h in held.items())
    needed, records = {}, []
    for stem in NATIVES:
        n = 'reports/full-coverage/'+stem+'.json'
        d = read(n)
        assert type(d['actual_exit_code']) is int and d['actual_exit_code'] in (0,1)
        assert d['status'] == ('passed' if d['actual_exit_code'] == 0 else 'failed')
        assert d['actual_workdir'] == str(ROOT) and type(d['actual_command']) is list
        assert d['helper_sha256_before'] == d['helper_sha256_after']
        needed[n] = sha(n)
        assert sha(d['log']) == d['log_sha256']; needed[d['log']] = d['log_sha256']
        for helper, h in d['helper_sha256_before'].items():
            assert sha(helper) == h; needed[helper] = h
        records.append({'original': ref(n), 'actual_exit_code': d['actual_exit_code'],
            'status': d['status'], 'original_command': d['actual_command'],
            'original_started_at_utc': d['started_at_utc'], 'original_finished_at_utc': d['finished_at_utc']})
    assert [r['actual_exit_code'] for r in records if '/selection29-preflight-' in r['original']['file']] == [1,1,1,0]
    needed['book/coverage/checks/root_record_actual29_v1.py'] = sha('book/coverage/checks/root_record_actual29_v1.py')
    aliases = {}
    for n, h in needed.items():
        alias = DEST+'/'+h+'/'+Path(n).name
        p = safe(alias); p.parent.mkdir(parents=True, exist_ok=True)
        if not p.exists():
            with p.open('xb') as output: output.write(safe(n).read_bytes())
        assert sha(alias) == h
        aliases[n] = {'file': alias, 'sha256': h}
    result = {'status': 'closed_exact_original_root29_selection_execution_bytes',
        'closed_at_utc': datetime.now(timezone.utc).isoformat(), 'aliases': aliases,
        'original_actual_records': records, 'actual_record_count': len(records),
        'true_failed_preflight_count': 3, 'current_selection': ref('reports/full-coverage/checkpoint-29-selection.json'),
        'scope': 'Byte-exact original records, helper versions and raw logs. Commands, exit codes, hypotheses, recorded times and old recorder footers retain their original meanings. No aggregate or delivery success is inferred.',
        'coverage_complete': False}
    assert all(sha(n) == h for n, h in held.items())
    p = safe(DEST+'/original-closed-byte-aliases-v1.json')
    with p.open('x') as output: output.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'actual_records': len(records), 'aliases': len(aliases), 'true_failed_preflights': 3}))

if __name__ == '__main__': main()
