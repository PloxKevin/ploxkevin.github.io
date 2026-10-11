from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations
BINDING = 'book/coverage/checks/root-owner23-reviewed-candidate-bindings-v1.json'
OUTPUT = Path('/tmp/root23-concrete-four-owner-binding-independent-modules-confirmation-v3.json')
cache = {}
def path(n):
    p = Path(n)
    assert not p.is_absolute() and str(p) == n and '..' not in p.parts, n
    r = (ROOT / p).resolve()
    assert r.is_relative_to(ROOT.resolve()), n
    return r
def sha(n, fresh=False):
    if fresh or n not in cache: cache[n] = hashlib.sha256(path(n).read_bytes()).hexdigest()
    return cache[n]
def read(n): return json.loads(path(n).read_text())
def check(r):
    assert sha(r['file']) == r['sha256'], r['file']
    return read(r['file'])
def ref(n): return {'file':n, 'sha256':sha(n)}
def actual0(a):
    codes = [a[k] for k in ('actual_exit_code','exit_code') if k in a]
    assert codes and all(type(c) is int and c == 0 for c in codes)
def log_check(a, evidence=None):
    name = a.get('log', a.get('raw_log'))
    digest = a.get('log_sha256', a.get('raw_log_sha256'))
    if name.startswith('/'):
        assert evidence is not None
        alternatives = [n for n,s in evidence.items() if s == digest and n.endswith('.log')]
        assert alternatives
        for n in alternatives: assert sha(n) == digest
    else: assert sha(name) == digest, name
    return digest

assert not OUTPUT.exists()
b = read(BINDING)
assert sha(BINDING) == '4b6dd0eb2bae622be47e0fd96adf12a4b3c2dc10cc44baf1b34703c6cca8b054'
assert b['status'] == 'all_four_reviewed_current51_owner_candidates_bound_ready_for_root_execution'
assert b['coverage_complete'] is False and set(b['owners']) == {'core','foundations','applied','modules'}
baseline = check(b['baseline22_manifest'])
assert len(baseline['proof_files']) == 1113 and len(baseline['frozen_inputs_sha256']) == 34051
assert sha('book/coverage/inventory.json') == sha('book/coverage/inventory-after-correction51.json') == b['inventory_sha256'] == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
inventory = read('book/coverage/inventory.json')
for n,s in inventory['source_sha256'].items(): assert sha(n) == s
assert len(b['exact_current51_safelearning_assets_sha256']) == 31
for n,s in b['exact_current51_safelearning_assets_sha256'].items(): assert sha(n) == s
assert sha('book/coverage/material-corrections.json') == b['source51_corrections_sha256']
apply = check(b['actual_source51_apply']); actual0(apply); log_check(apply)
post = check(b['actual_source51_postwrite']); assert post.get('errors', []) == []
code_peer = check(b['independent_helper_review'])
assert 'pass' in code_peer['status']
check(b['helper']) if b['helper']['file'].endswith('.json') else None
assert sha(b['helper']['file']) == b['helper']['sha256']
assert sha(b['preparation_helper']['file']) == b['preparation_helper']['sha256'] == '7499b1d6711f7aadd63522f0dc5380e582112ea3698faaacb2ea2c39dff798d2'
history = []
for version, expected in ((1,1),(2,1),(3,0)):
    name = f'reports/full-coverage/owner23-binding-preparation-execution-v{version}.json'
    a = read(name)
    assert type(a['actual_exit_code']) is int and a['actual_exit_code'] == expected
    log_check(a)
    for n,s in a['helper_sha256_before'].items():
        assert a['helper_sha256_after'][n] == s == sha(n)
    history.append(ref(name))

expected_counts = {'core':(9,88),'foundations':(3,39),'applied':(0,0),'modules':(6,64)}
all_new = {}
owners = {}
for owner,row in b['owners'].items():
    assert row['ready'] is True
    assert row['held22_ledger_sha256'] == baseline['working_inputs_sha256'][row['held22_ledger']] == sha(row['held22_ledger'])
    offer = check(row['reviewed_final_offer']); candidate = check(row['candidate_ledger']); peer = check(row['independent_candidate_mapping_peer'])
    assert 'pass' in peer['status'] and peer.get('errors',[]) == []
    key = row['offer_candidate_path_pointer'][0]
    assert offer[key] == row['candidate_ledger']['file'] and offer[key+'_sha256'] == row['candidate_ledger']['sha256']
    pkey = row['peer_candidate_path_pointer'][0]
    assert peer[pkey] == row['candidate_ledger']
    assert offer.get('coverage_complete') is False
    assert offer.get('current_inventory_sha256',offer.get('inventory_sha256')) == b['inventory_sha256']
    for n,s in offer['source_sha256'].items():
        assert sha(n) == s
        if n in inventory['source_sha256']: assert s == inventory['source_sha256'][n]
    for n,s in candidate['source_sha256'].items():
        assert sha(n) == s
        if n in inventory['source_sha256']: assert s == inventory['source_sha256'][n]
    builder = check(row['actual_candidate_builder']); actual0(builder)
    log_check(builder, {r['file']:r['sha256'] for r in row['additional_exact_provenance']})
    semantics = []
    for r in row['original_full_source_semantic_reviews']:
        original = check(r)
        assert original['status'] == r['original_review_status']
        assert original.get('reviewed_at_utc',original.get('checked_at_utc')) == r['original_review_time']
        assert r['original_review_time'] and original.get('errors',[]) == []
        semantics.append(r)
    evidence = {r['file']:r['sha256'] for r in row['additional_exact_provenance']}
    assert len(evidence) == len(row['additional_exact_provenance'])
    for n,s in evidence.items(): assert sha(n) == s
    proof_rows = {}
    count = 0
    assert set(row['new_immutable_proof_sources']) == set(offer['proof_files'])
    for n,pr in row['new_immutable_proof_sources'].items():
        assert n not in baseline['proof_files'] and n not in all_new
        digest = sha(n)
        assert digest == pr['sha256'] == offer['proof_files'][n]['sha256']
        decls = declarations(path(n).read_text())
        public = [d['name'] for d in decls if d['kind'] in ('theorem','lemma')]
        count += len(public)
        all_new[n] = digest
        assert len(pr['actual_pair']) == 2
        kinds = set()
        snapshots = []
        for pair in pr['actual_pair']:
            a = check(pair); actual0(a)
            assert a['source'] == pair['actual_source'] == n
            assert a['source_sha256_before'] == a['source_sha256_after'] == digest
            assert a.get('source_unchanged',True) is True
            cmd = a['command']
            assert cmd == pair['actual_command'] and a['actual_workdir'] == pair['actual_workdir'] == str(ROOT/'verification/lean')
            module = 'SafeLearning.'+Path(n).stem
            if cmd == ['lake','env','lean','SafeLearning/'+Path(n).name]: kinds.add('standalone')
            elif cmd == ['lake','build',module]: kinds.add('named')
            else: raise AssertionError((n,cmd))
            lr = pair['canonical_raw_log']
            assert sha(lr['file']) == lr['sha256'] == a['log_sha256']
            snapshot = a.get('source_snapshot',a.get('preserved_source'))
            if snapshot:
                sh = a.get('source_snapshot_sha256',a.get('preserved_source_sha256'))
                assert sh == digest
                if snapshot.startswith('/'):
                    copies = [f for f,s in offer['proof_files'][n]['evidence_sha256'].items() if s == sh and f.endswith('.lean')]
                    assert copies, (n,snapshot)
                    for f in copies: assert sha(f) == sh
                    snapshots.extend(copies)
                else:
                    assert sha(snapshot) == sh
                    snapshots.append(snapshot)
            assert a.get('checked_at_utc',a.get('started_at_utc',a.get('started_at')))
        assert kinds == {'standalone','named'}
        proof_rows[n] = {'sha256':digest,'public_theorem_or_lemma_count':len(public),'public_names':public,'actual_pair':pr['actual_pair'],'source_snapshot_aliases_checked':sorted(set(snapshots))}
    assert (len(proof_rows),count) == expected_counts[owner]
    for companion in row['companion_candidates']:
        assert sha(companion['held22_asset']) == companion['held22_asset_sha256'] == baseline['working_inputs_sha256'][companion['held22_asset']]
        check(companion['candidate'])
    owners[owner] = {'candidate':row['candidate_ledger'],'offer':row['reviewed_final_offer'],'peer':row['independent_candidate_mapping_peer'],'actual_candidate_builder':row['actual_candidate_builder'],'original_full_source_semantic_reviews':semantics,'new_proof_sources':proof_rows,'additional_exact_provenance_count':len(evidence)}

assert len(all_new) == 18 and sum(v[1] for v in expected_counts.values()) == 191
available = set(baseline['proof_files']) | set(all_new)
imports = {}
for n in all_new:
    local = re.findall(r'^import\s+(SafeLearning\.[A-Za-z0-9_.]+)\s*$',path(n).read_text(),re.M)
    deps = ['verification/lean/'+module.replace('.','/')+'.lean' for module in local]
    assert set(deps) <= available, (n,set(deps)-available)
    imports[n] = deps
for n,r in baseline['proof_files'].items(): assert sha(n) == r['sha256']
print('All 18 new sources/191 exports, 36 original pairs, four candidates and 1113 baseline sources checked.',flush=True)
snapshot = baseline['snapshot']
for n,s in baseline['frozen_inputs_sha256'].items(): assert sha(snapshot+'/'+n) == s, n
for owner,row in b['owners'].items():
    assert sha(row['held22_ledger'],True) == row['held22_ledger_sha256']
    assert sha(row['candidate_ledger']['file'],True) == row['candidate_ledger']['sha256']
assert sha(BINDING,True) == '4b6dd0eb2bae622be47e0fd96adf12a4b3c2dc10cc44baf1b34703c6cca8b054'
ref_tmp_failure = {'checker':'/tmp/modules-root23-concrete-four-owner-binding-peer-v1.py','actual_execution':'/tmp/modules-root23-concrete-four-owner-binding-peer-actual-v1.json','raw_log':'/tmp/modules-root23-concrete-four-owner-binding-peer-actual-v1.log','reason':'The first reader required started_at_utc/checked_at_utc; five exact original Core-selected Applied sources use started_at. The new reader admits that original field without changing execution evidence.'}
out = {'status':'independent_complete_four_owner_current51_reviewed_candidate_binding_confirmation_passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),'binding':ref(BINDING),'preparation_helper':b['preparation_helper'],'preparation_actual_history':history,'integration_helper':b['helper'],'original_code_peer':b['independent_helper_review'],'current_inventory':ref('book/coverage/inventory-after-correction51.json'),'baseline22_manifest':b['baseline22_manifest'],'owners':owners,'new_source_count':18,'new_public_theorem_or_lemma_count':191,'actual_paired_record_count':36,'local_import_closure':imports,'protected_baseline_proof_count':1113,'protected_frozen22_input_count':34051,'current_asset_count':31,'errors':[],'preserved_first_reader_failure':ref_tmp_failure,'preserved_second_reader_failure':{'checker':'/tmp/modules-root23-concrete-four-owner-binding-peer-v2.py','actual_execution':'/tmp/modules-root23-concrete-four-owner-binding-peer-actual-v2.json','raw_log':'/tmp/modules-root23-concrete-four-owner-binding-peer-actual-v2.log','reason':'The second reader required every original source map entry to occur in the inventory page map. Foundation also records book/chapters fragments. V3 checks every recorded byte digest, and exact inventory identity for actual page entries, preserving the distinct original fragment scope.'},'scope':'Read-only actual binding confirmation. Original complete semantic review JSON bodies, statuses, hypotheses and review times are hash-bound without rewriting. Existing candidate mapping peers remain the mapping decisions; no live installation, mathematical proof execution, aggregate23 verification or full-book completion is inferred.'}
OUTPUT.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'report':str(OUTPUT),'sha256':hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}))
