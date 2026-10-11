"""Close the independently reviewed, isolated source52 Foundation24 offer only."""
from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, copy
ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'book/coverage/checks/foundations-future24/source52'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
J = lambda p: json.loads(Path(p).read_text())
def path(n):
    p = Path(n)
    return p if p.is_absolute() else ROOT / p
def ref(p):
    p = Path(p)
    return {'file': p.relative_to(ROOT).as_posix(), 'sha256': H(p)}
def bind(r):
    p = path(r['file'])
    assert p.is_file() and not p.is_symlink() and H(p) == r['sha256'], r
    return p
def copy_exact(p):
    p = Path(p)
    target = BASE / 'original-module-source52-identity-peer-v1' / p.name
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert target.read_bytes() == p.read_bytes()
    else:
        with target.open('xb') as f:
            f.write(p.read_bytes())
    return {'original_file': str(p), 'original_sha256': H(p), 'canonical_alias': ref(target)}

draft = BASE / 'foundations-audit24-candidate-source52-additions-draft-v1.json'
assert H(draft) == '292e8d48c1f612502373a3da83187dbc77529def0cbb4631289a06f574d13585'
o = J(draft)
peer_path = Path('/tmp/owner24-foundations-applied-source52-identities-independent-modules-confirmation-v1.json')
assert H(peer_path) == 'd7abb956d75cea878e89cc49001a611dfa9ee0a6c39ee117c992abf8ce6ef40d'
peer = J(peer_path)
assert 'passed' in peer['status'] and peer['errors'] == []
r = peer['owners']['foundations']
assert 'passed' in r['status'] and r['errors'] == [] and r['source52_offer'] == ref(draft)
assert r['source52_candidate'] == {'file': o['mapped_ledger'], 'sha256': o['mapped_ledger_sha256']}
candidate = J(bind(r['source52_candidate']))
assert o['mapped_ledger_sha256'] == 'e3ff8460281d2a745c6def2d007b6465a1b5c352a1e14d90d486dec64835982b'
side = J(bind(o['current52_identity_rebase']['identity_sidecar']))
old_offer = J(bind(r['original_source51_offer']))
old_candidate = J(bind(r['original_source51_candidate']))
rev = copy.deepcopy(candidate)
rev.pop('current52_owner_identity')
assert rev == old_candidate
rev = copy.deepcopy(o)
rev.pop('current52_identity_rebase')
rev.update(o['current52_identity_rebase']['original_source51_outer_fields'])
assert rev == old_offer
assert r['owned_entire_literal_counts'] == {'exercises': 119, 'material_source_units': 1756}
assert r['candidate_and_offer_inverse_exact'] and r['mathematical_bodies_hypotheses_reasons_decisions_times_proofs_and_compiler_records_unchanged']
assert o['new_proof_file_count'] == 5 and o['new_theorem_or_lemma_count'] == 37
assert o['proof_files'] == old_offer['proof_files']
assert H(ROOT/'book/coverage/inventory.json') == H(ROOT/o['current_inventory']) == o['current_inventory_sha256'] == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for n,h in peer['held_live_owner_sha256'].items():
    assert H(ROOT/n) == h
for n,h in o['source_sha256'].items():
    assert H(ROOT/n) == h
for n,h in candidate['proof_sha256'].items():
    assert H(ROOT/n) == h
for n,row in o['proof_files'].items():
    assert H(ROOT/n) == row['sha256']
    for f,h in row['evidence_sha256'].items():
        assert H(ROOT/f) == h
for field in ['exact_source_reviews_sha256', 'actual_canonical_execution_records_sha256', 'canonical_readiness_sha256', 'canonical_source_peer_bindings_sha256']:
    for n,h in o[field].items():
        assert H(ROOT/n) == h

execution = Path('/tmp/owner24-source52-identity-independent-modules-actual-v3.json')
checker = Path('/tmp/check-owner24-source52-identities-independent-modules-v3.py')
ea = J(execution)
assert ea['actual_exit_code'] == 0 and ea['actual_command'] == ['python3', str(checker), 'unused_core', str(peer_path)] and ea['actual_workdir'] == str(ROOT)
assert ea['actual_helper_sha256_before'] == ea['actual_helper_sha256_after'] == H(checker)
assert H(path(ea['raw_log'])) == ea['raw_log_sha256']
owner_peer_path = ROOT/'book/coverage/checks/future24-core/source52-independent-owner-identity-peer/foundations24-source52-identity-independent-modules-confirmation-v1.json'
owner_peer = J(owner_peer_path)
assert owner_peer['entire_original_batch_review_body_and_time'] == peer
assert owner_peer['source52_candidate'] == r['source52_candidate'] and owner_peer['source52_offer'] == r['source52_offer']
assert owner_peer['checked_at_utc'] == peer['checked_at_utc'] and owner_peer['errors'] == [] and 'passed' in owner_peer['status']
outer_runner = ROOT/'book/coverage/checks/modules-future24/source51/modules-isolated-candidate-actual-runner24-v1.py'
assert H(outer_runner) == '953860d41ba6958488a90589923536873022fe05d660d7bc9ba00953a31e22cc'
assert bind(owner_peer['actual_outer_measured_runner']) == outer_runner
originals = [peer_path, owner_peer_path, outer_runner]
for v in [1,2,3]:
    cp = Path(f'/tmp/check-owner24-source52-identities-independent-modules-v{v}.py')
    ap = Path(f'/tmp/owner24-source52-identity-independent-modules-actual-v{v}.json')
    a = J(ap)
    assert a['actual_exit_code'] == (0 if v == 3 else 1)
    assert a['actual_helper_sha256_before'] == a['actual_helper_sha256_after'] == H(cp)
    assert H(path(a['raw_log'])) == a['raw_log_sha256']
    originals += [cp, ap, path(a['raw_log'])]
aliases = [copy_exact(p) for p in originals]
alias_path = BASE / 'module-source52-identity-peer-original-byte-aliases-v1.json'
assert not alias_path.exists()
alias_doc = {'status': 'passed_exact_closed_original_byte_aliases', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'originals': aliases, 'scope': 'Exact passing peer and all three original readers/executions/logs, retaining both genuine failures as failures. No new semantic decision or compiler execution.'}
with alias_path.open('x') as f:
    f.write(json.dumps(alias_doc, ensure_ascii=False, indent=2)+'\n')
lookup = {a['original_file']: a['canonical_alias'] for a in aliases}

ba = bind(r['actual_identity_execution']['actual_record'])
b = J(ba)
assert b == r['actual_identity_execution']['entire_original_record_body_and_time']
assert b['actual_exit_code'] == 0 and b['actual_workdir'] == str(ROOT)
helper = ROOT/o['current_owner_builder']
assert b['actual_command'] == ['python3',str(helper),'--inventory-sha256',o['current_inventory_sha256'],'--root-authorized-source52-identity-rebase']
assert H(helper) == o['current_owner_builder_sha256'] == b['actual_helper_sha256_before'] == b['actual_helper_sha256_after']
assert H(ROOT/b['raw_log']) == b['raw_log_sha256'] and H(ROOT/b['actual_runner']) == b['actual_runner_sha256']

f = copy.deepcopy(o)
changed = ['status','actual_builder_record','actual_builder_record_sha256','actual_builder_raw_log','final_independent_candidate_mapping_peer','original_final_independent_peer_body_and_time','final_independent_peer_actual_execution','final_independent_peer_raw_log','final_independent_peer_checker','final_independent_peer_exact_original_provenance','finalizer','scope']
f['status'] = 'passed_reviewed_isolated_source52_foundation24_identity_candidate_five_sources37_exports_six_complete_literals'
f['actual_builder_record'] = ref(ba)['file']
f['actual_builder_record_sha256'] = H(ba)
f['actual_builder_raw_log'] = ref(ROOT/b['raw_log'])
f['final_independent_candidate_mapping_peer'] = lookup[str(owner_peer_path)]
f['original_final_independent_peer_body_and_time'] = owner_peer
f['final_independent_peer_actual_execution'] = lookup[str(execution)]
f['final_independent_peer_raw_log'] = lookup[ea['raw_log']]
f['final_independent_peer_checker'] = lookup[str(checker)]
f['final_independent_peer_exact_original_provenance'] = aliases
f['finalizer'] = ref(Path(__file__))
f['scope'] = 'FINAL independently reviewed isolated Foundation24 source52 unchanged-literal identity candidate. Original six whole decisions, five immutable actual paired sources/37 exports, 119 exercises/1756 owned entire literals and all source51 semantic bodies/times are retained exactly. Genuine identity preparation is separate from future live installation, selection, aggregate audit and publication.'
f['current52_identity_rebase'].update({'finalized_at_utc':datetime.now(timezone.utc).isoformat(),'original_source52_draft':ref(draft),'entire_original_source52_draft_body_and_time':o,'finalization_original_outer_fields':{k:copy.deepcopy(o[k]) for k in changed},'actual_identity_builder_record_pending':False,'independent_source52_identity_delta_peer_pending':False,'actual_identity_builder':r['actual_identity_execution'],'independent_source52_identity_peer':lookup[str(peer_path)],'independent_source52_identity_peer_owner_row':r,'closed_original_peer_byte_aliases':ref(alias_path)})
rev = copy.deepcopy(f)
for k in changed:
    rev[k] = copy.deepcopy(o[k])
rev['current52_identity_rebase'] = copy.deepcopy(o['current52_identity_rebase'])
assert rev == o
assert f['prepared_at_utc'] == old_offer['prepared_at_utc'] and f['finalized_at_utc'] == old_offer['finalized_at_utc']
out = BASE/'foundations-audit24-candidate-source52-additions-v1-reviewed.json'
assert not out.exists()
with out.open('x') as file:
    file.write(json.dumps(f,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':f['status'],'offer':ref(out),'candidate':r['source52_candidate'],'final_peer':f['final_independent_candidate_mapping_peer']}))
