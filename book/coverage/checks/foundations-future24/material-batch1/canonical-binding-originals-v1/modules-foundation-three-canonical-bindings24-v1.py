from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def read(p):
    return json.loads(Path(p).read_text())

def checked(r):
    p = Path(r['file'])
    if not p.is_absolute():
        p = ROOT / p
    assert sha(p) == r['sha256'], str(p)
    return p

def ref(p):
    return {'file': str(p), 'sha256': sha(p)}

batch_path = ROOT / 'book/coverage/checks/foundations-future24/material-batch1/five-source37-export-actual-canonical-readiness24-v1.json'
assert sha(batch_path) == '758e81e120ab257f9b87fe0c6602ce92bfab26d3f90ca6d4a726937ca293164d'
batch = read(batch_path)
assert batch['source_count'] == 5 and batch['public_theorem_count'] == 37
inv = read(ROOT / 'book/coverage/inventory-after-correction51.json')
assert sha(ROOT / 'book/coverage/inventory.json') == sha(ROOT / 'book/coverage/inventory-after-correction51.json') == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
units = {u['key']: u for u in inv['material_source_units']}
expected = {
    'orthonormal121': ('cc8583c0652cd11c02e9f92d80902c69aebe6b2fa149645f91910e35d1eca909', 6),
    'extreme-value1145-1147': ('6b09ec5114104dbb479201aad306365266aa47cf4e4f5f07b08539676956bb0a', 11),
    'audit1163': ('10b7efabe7880daef385edae9705cec7a0be8c3bc0bb367f2c46b3e4e3e69e8f', 5),
}
groups = []
for r in batch['groups']:
    p = checked(r)
    g = read(p)
    if g['group'] not in expected:
        continue
    peer_sha, count = expected[g['group']]
    peer_p = checked(g['original_full_semantic_peer'])
    assert sha(peer_p) == peer_sha
    peer = read(peer_p)
    assert peer == g['entire_original_full_semantic_peer_body_and_time']
    req_p = checked(g['original_TMP_request'])
    request = read(req_p)
    assert request == g['entire_original_TMP_request_body_and_time']
    src = checked(g['canonical_source'])
    snap = checked(g['canonical_source_snapshot'])
    assert src.read_bytes() == snap.read_bytes()
    assert g['canonical_source']['sha256'] == request['new_actual_source']['sha256']
    original = checked(request['new_actual_source'])
    assert src.read_bytes() == original.read_bytes()
    names = [d['name'] for d in declarations(src.read_text()) if d['kind'] in ('theorem', 'lemma')]
    assert names == g['public_theorem_names'] and len(names) == count == g['public_theorem_count']
    for old, alias in g['all_original_TMP_byte_copies'].items():
        ap = checked(alias)
        assert Path(old).read_bytes() == ap.read_bytes()
    actuals = []
    modes = set()
    for row in g['actual_canonical_pair']:
        rp = checked(row['actual_record'])
        lp = checked(row['raw_log'])
        sp = checked(row['source_snapshot'])
        a = read(rp)
        assert a['status'] == 'passed' and a['actual_exit_code'] == row['actual_exit_code'] == 0
        assert a['source_sha256_before'] == a['source_sha256_after'] == sha(src)
        assert a['source_unchanged'] is True and a['source'] == g['canonical_source']['file']
        assert a['log_sha256'] == sha(lp) and a['log'] == row['raw_log']['file']
        assert a['source_snapshot_sha256'] == sha(sp) == sha(src)
        assert a['source_snapshot'] == row['source_snapshot']['file']
        assert a['actual_workdir'] == str(ROOT / 'verification/lean')
        assert a['started_at_utc'] < a['finished_at_utc'] and a['elapsed_seconds'] >= 0
        if a['kind'] == 'actual_future24_canonical_named-build':
            assert a['actual_command'] == ['lake', 'build', 'SafeLearning.' + src.stem]
            modes.add('named')
        else:
            assert a['kind'] == 'actual_future24_canonical_standalone'
            assert a['actual_command'] == ['lake', 'env', 'lean', 'SafeLearning/' + src.name]
            modes.add('standalone')
        assert sha(ROOT / a['actual_pair_helper']) == a['actual_pair_helper_sha256']
        actuals.append({'original_actual_record_body_and_time': a, 'actual_record': row['actual_record'], 'raw_log': row['raw_log'], 'source_snapshot': row['source_snapshot']})
    assert modes == {'named', 'standalone'} and len(actuals) == 2
    for u in peer['material_units']:
        original_unit = u.get('entire_inventory_record', u.get('entire_original_inventory_record'))
        assert original_unit is not None
        assert original_unit == units[original_unit['key']]
        assert sha(ROOT / original_unit['source']) == original_unit['source_sha256']
    groups.append({'group': g['group'], 'canonical_readiness': r, 'canonical_source': g['canonical_source'], 'original_semantic_peer': g['original_full_semantic_peer'], 'entire_original_semantic_peer_body_and_time': peer, 'original_TMP_request': g['original_TMP_request'], 'original_semantic_decisions_and_times_unchanged': True, 'whole_literal_inventory_records_unchanged': True, 'public_theorem_names': names, 'actual_paired_records': actuals, 'original_TMP_alias_count': len(g['all_original_TMP_byte_copies'])})
assert len(groups) == 3 and sum(len(g['public_theorem_names']) for g in groups) == 22
manifest = read(ROOT / 'reports/full-coverage/checkpoint-23-manifest.json')
assert len(manifest['proof_files']) == 1131
for n, row in manifest['proof_files'].items():
    assert sha(ROOT / n) == row['sha256']
selection = read(ROOT / 'reports/full-coverage/checkpoint-23-selection.json')
for n, d in selection['safelearning_asset_sha256'].items():
    assert sha(ROOT / n) == d
owner_sha = {'core': '1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a', 'foundations': '6008c0225111ce8a8db195475036d85af95567f620e57929ea485d39e9d42279', 'applied': 'cf35fa4605bd21c1d6b638ab2fecfdd871beea8e7a3b850456b8053832ae9131', 'modules': '448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367', 'applied-promotions': '64d40e98a0cb98cbb0e4355c38709a6a89b7d2822e982e34fc340dbc402fcdce'}
for n, d in owner_sha.items():
    assert sha(ROOT / ('book/coverage/' + n + '.json')) == d
out = {'status': 'independent_exact_original_semantic_peer_canonical_source_and_paired_evidence_binding_passed', 'reviewer': '/root/modules_resume', 'binding_checked_at_utc': datetime.now(timezone.utc).isoformat(), 'errors': [], 'canonical_batch': ref(batch_path), 'groups': groups, 'group_count': 3, 'source_count': 3, 'public_theorem_count': 22, 'all1131_selected23_proof_source_hashes_exact': True, 'all31_source51_assets_exact': True, 'all_five_live23_owner_bytes_exact': True, 'checker': ref(Path(__file__)), 'scope': 'New byte/evidence correspondence only. The three complete original semantic review bodies, decisions, reasons, hypotheses, declarations and times are embedded without alteration. Genuine canonical standalone and named records are additional execution evidence; no new mathematical decision, compilation, live mapping, selection24 or aggregate24 claim.'}
target = Path('/tmp/foundations-three-canonical-sources-original-module-peers-binding24-v1.json')
assert not target.exists()
target.write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'peer': ref(target), 'groups': 3, 'theorems': 22}))
