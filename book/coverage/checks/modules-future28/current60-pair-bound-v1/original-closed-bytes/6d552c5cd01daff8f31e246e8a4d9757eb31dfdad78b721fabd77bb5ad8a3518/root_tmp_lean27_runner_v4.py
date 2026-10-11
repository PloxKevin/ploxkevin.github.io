"""Run a TMP Lean trial while protecting the installed26 proof sources and actual current55 inputs.

This records only the actual temporary compiler run. It installs no canonical
proof, modifies no ledger, and makes no aggregate or mathematical coverage claim.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
assert len(sys.argv) == 3
source, record = map(Path, sys.argv[1:3])
for path in (source, record):
    assert path.is_absolute() and path.resolve().is_relative_to(Path('/tmp'))
assert source.is_file() and source.suffix == '.lean'
assert record.suffix == '.json'
log = record.with_suffix('.log')
snapshot = record.with_name(record.stem + '-source.lean')
assert all(not p.exists() for p in (record, log, snapshot))

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(ROOT / name)}

PINNED = {
    'reports/full-coverage/checkpoint-26-selection.json': '12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f',
    'reports/full-coverage/checkpoint-25-selection.json': '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff',
    'reports/full-coverage/checkpoint-25-manifest.json': '0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363',
    'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json': '00a94eefea80aff4bd57ee2d511d3102f1a8652dfda1977272aefd9b7fe41cfb',
    'reports/full-coverage/owner26-reviewed-candidate-integration-v1.json': '7fa88d829c47797ab8258eb84ff5c7ce3399da66c9b03b591ea9820ca1eca06e',
    'reports/full-coverage/root-source53-final-owner-integration26-v1.json': '4029138dca32a74e8fd718fbe563d0b867d8ed408ad49a869e7308ea9867259d',
    'book/coverage/inventory.json': '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
    'book/coverage/inventory-after-correction55.json': '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
    'reports/full-coverage/source54-55-corrections-application-v1.json': '845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528',
    'reports/full-coverage/source54-55-corrections-application-execution-v1.json': 'a255862de464e0f1acf284807c4a48b732bc69055cf71b445ea2df5920494805',
    'book/coverage/material-corrections.json': '21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94',
    'book/coverage/inventory-after-correction53.json': '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be',
}
for name, digest in PINNED.items(): assert sha(ROOT / name) == digest, name
selection = read('reports/full-coverage/checkpoint-26-selection.json')
baseline = read('reports/full-coverage/checkpoint-25-selection.json')
binding = read('book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json')
integration = read('reports/full-coverage/owner26-reviewed-candidate-integration-v1.json')
global_audit = read('reports/full-coverage/root-source53-final-owner-integration26-v1.json')
assert selection['proof_file_count'] == len(selection['proof_files']) == 1167
assert selection['new_file_count'] == binding['new_proof_sources'] == 11
assert len(baseline['proof_files']) == 1156
assert set(baseline['proof_files']) <= set(selection['proof_files'])
assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline['proof_files'].items())
assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
assert integration['applied'] is True and integration['all44111_frozen25_inputs_exact'] is True
assert integration['all1156_selected25_root_source_hashes_exact'] is True
application = read('reports/full-coverage/source54-55-corrections-application-v1.json')
assert application['status'] == 'passed_actual_source54_and_source55_corrections_full29_inventory_owner_identity_rebase_pending'
assert application['selected26_proof_sources_unchanged'] == 1167
assert application['five_installed26_owner_ledgers_unchanged'] is True
assert application['coverage_complete'] is False
assert [r['correction_id'] for r in application['applications']] == [54,55]
expected_changed_assets = {
    'SafeLearning/lyapunov-mpc.html': '63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f',
    'SafeLearning/verification.html': 'd01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53',
}
assert {r['source_after']['file']:r['source_after']['sha256'] for r in application['applications']} == expected_changed_assets
assets = {**binding['exact_current53_safelearning_assets_sha256'],**expected_changed_assets}
assert len(assets) == 31
assert read('book/coverage/inventory-after-correction55.json')['source_sha256'] == {n:h for n,h in assets.items() if n.endswith('.html')}
owners = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
assert len(owners) == 5
for row in global_audit['domains']:
    assert row['ledger_sha256'] == owners['book/coverage/' + row['domain'] + '.json']
held = {n: r['sha256'] for n, r in selection['proof_files'].items()}
held.update(assets)
held.update(owners)
corrections = 'book/coverage/material-corrections.json'
assert len(read(corrections)['corrections']) == 55
old_corrections_path = ROOT / 'reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root/book/coverage/material-corrections.json'
assert sha(old_corrections_path) == binding['source53_corrections_sha256']
assert read(corrections)['corrections'][:53] == json.loads(old_corrections_path.read_text())['corrections']
assert [r['correction_id'] for r in read(corrections)['corrections'][53:]] == [54,55]
for stem in ('owner26-integration-apply-execution-v1', 'root-source53-final-owner-integration26-execution-v1', 'prepare-checkpoint26-selection-execution-v1', 'source54-55-corrections-application-execution-v1'):
    name = 'reports/full-coverage/' + stem + '.json'
    actual = read(name)
    codes = [actual[k] for k in ('actual_exit_code', 'exit_code') if k in actual]
    assert codes and all(type(code) is int and code == 0 for code in codes)
    assert actual['actual_workdir'] == str(ROOT)
    assert actual['helper_sha256_before'] == actual['helper_sha256_after']
    assert sha(ROOT / actual['log']) == actual['log_sha256']
    for helper, digest in actual['helper_sha256_after'].items():
        assert sha(ROOT / helper) == digest
        PINNED[helper] = digest
    PINNED[name] = sha(ROOT / name)
    PINNED[actual['log']] = actual['log_sha256']
for name in ('verification/lean/lean-toolchain', 'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json'):
    PINNED[name] = sha(ROOT / name)
# Eight new canonical sources are installed and genuinely paired, but remain
# unselected until Root completes current55 owner integration and audit27.
PAIRS27_NAME = 'book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json'
PAIRS27_SHA = '74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f'
PAIR27_ACTUAL_NAME = 'reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json'
PAIR27_ACTUAL_SHA = '9ee7428bc5d16d6b65ec0fd88877d85e3ba38cb879f11951eca72ddd0b6df384'
assert sha(ROOT/PAIRS27_NAME)==PAIRS27_SHA
assert sha(ROOT/PAIR27_ACTUAL_NAME)==PAIR27_ACTUAL_SHA
pairs27=read(PAIRS27_NAME);pair27_actual=read(PAIR27_ACTUAL_NAME)
assert pairs27['status']=='passed_actual_eight_source141_canonical_standalone_and_named_pairs_unselected_future27'
assert pairs27['errors']==[] and pairs27['source_count']==8 and pairs27['public_theorem_count']==141
assert pair27_actual['actual_command']==['python3','book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py','--apply']
assert type(pair27_actual['actual_exit_code']) is int and pair27_actual['actual_exit_code']==0
assert pair27_actual['helper_sha256_before']==pair27_actual['helper_sha256_after']
assert pair27_actual['actual_workdir']==str(ROOT)
assert sha(ROOT/pair27_actual['log'])==pair27_actual['log_sha256']
new27={r['canonical_source']:r['source']['sha256'] for r in pairs27['sources']}
assert len(new27)==8 and not set(new27).intersection(selection['proof_files'])
assert len(pairs27['actual_paired_records'])==16
seen27=set()
for row in pairs27['actual_paired_records']:
    name=row['source']['file'];kind=row['kind']
    assert name in new27 and row['source']['sha256']==new27[name] and kind in {'standalone','named'}
    assert (name,kind) not in seen27;seen27.add((name,kind))
    assert type(row['actual_exit_code']) is int and row['actual_exit_code']==0
    record27=read(row['actual_record']['file'])
    assert sha(ROOT/row['actual_record']['file'])==row['actual_record']['sha256']
    assert type(record27['exit_code']) is int and record27['exit_code']==0
    assert record27['source']==name and record27['source_sha256_before']==record27['source_sha256_after']==new27[name]
    stem=Path(name).stem
    expected27=['lake','env','lean','SafeLearning/'+stem+'.lean'] if kind=='standalone' else ['lake','build','SafeLearning.'+stem]
    assert record27['command']==expected27 and record27['actual_workdir']==str(ROOT/'verification/lean')
    assert row['raw_log']=={'file':record27['log'],'sha256':record27['log_sha256']}
    assert row['source_snapshot']['sha256']==new27[name]
    for key in ['actual_record','raw_log','source_snapshot']:
        assert sha(ROOT/row[key]['file'])==row[key]['sha256']
        PINNED[row[key]['file']]=row[key]['sha256']
assert seen27=={(n,k) for n in new27 for k in ['standalone','named']}
held.update(new27)
PINNED[PAIRS27_NAME]=PAIRS27_SHA;PINNED[PAIR27_ACTUAL_NAME]=PAIR27_ACTUAL_SHA
PINNED[pair27_actual['log']]=pair27_actual['log_sha256']
for n,h in pair27_actual['helper_sha256_after'].items():
    assert sha(ROOT/n)==h;PINNED[n]=h

runner_before = sha(Path(__file__))

def guard():
    for name, digest in {**held, **PINNED}.items():
        assert sha(ROOT / name) == digest, name
    assert sha(Path(__file__)) == runner_before

guard()
before = sha(source)
with snapshot.open('xb') as stream: stream.write(source.read_bytes())
assert sha(snapshot) == before
command = ['lake', 'env', 'lean', str(source)]
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with log.open('xb') as stream:
    actual = subprocess.run(command, cwd=ROOT / 'verification/lean', stdout=stream, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc).isoformat()
after = sha(source)
protection_errors = []
try: guard()
except Exception as error: protection_errors.append(str(error))
passed = actual.returncode == 0 and before == after and not protection_errors
out = {
    'status': 'passed_actual_tmp_lean_only' if passed else 'failed_actual_tmp_lean_or_protection',
    'actual_exit_code': actual.returncode, 'actual_runner_exit_code': 0 if passed else 1,
    'actual_command': command, 'actual_workdir': str(ROOT / 'verification/lean'),
    'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': time.monotonic() - tick,
    'source': str(source), 'source_sha256_before': before, 'source_sha256_after': after,
    'source_unchanged': before == after, 'source_snapshot': str(snapshot), 'source_snapshot_sha256': sha(snapshot),
    'raw_log': str(log), 'raw_log_sha256': sha(log),
    'original_actual_runner': {'file': str(Path(__file__)), 'sha256': runner_before},
    'actual_installed26_selection': ref('reports/full-coverage/checkpoint-26-selection.json'),
    'historical_source53_installed26_global_integrity': ref('reports/full-coverage/root-source53-final-owner-integration26-v1.json'),
    'protected_proof_sources': 1175, 'protected_selected26_proof_sources': 1167,
    'protected_unselected_paired27_canonical_proof_sources': 8,
    'actual_unselected27_canonical_pair_readiness': ref(PAIRS27_NAME),
    'unchanged_baseline25_selected_proof_sources': 1156,
    'unchanged_canonical_new26_proof_sources': 11, 'unchanged_current55_book_assets': 31,
    'unchanged_installed26_live_owners': 5, 'installed26_owner_sha256': owners,
    'original_installed26_provenance_sha256': PINNED, 'protection_errors': protection_errors,
    'current55_owner_identity_rebase_pending': True,
    'actual_source54_55_application': ref('reports/full-coverage/source54-55-corrections-application-v1.json'),
    'canonical_installation_or_aggregate_verification_claimed': False,
}
with record.open('x') as stream: stream.write(json.dumps(out, indent=2) + '\n')
print(json.dumps(out))
raise SystemExit(0 if passed else 1)
