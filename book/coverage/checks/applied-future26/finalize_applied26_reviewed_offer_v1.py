from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, shutil

ROOT = Path('/home/oxrexkevin/SafetyBased')
BASE = ROOT / 'book/coverage/checks/applied-future26/source52-v2'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
ref = lambda p: {'file': str(Path(p).relative_to(ROOT)), 'sha256': H(p)}
def put(p, obj):
    with p.open('x') as f:
        f.write(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

draftpath = BASE / 'applied-audit26-candidate-source52-additions-v1.json'
assert H(draftpath) == '4e41448a66d7f5b970fc1ec296588eff9ec453e70e2836b3a966068ec9c96325'
draft = read(draftpath)
peerpath = Path('/tmp/applied26-canonical-and-whole371-candidate-independent-foundations-review-v1.json')
assert H(peerpath) == 'a9f36319ac8879ffb61afa9033ccb7e22c24a0f98acf020dcc27f0ad293ee2f5'
peer = read(peerpath)
assert peer['errors'] == [] and peer['status'].startswith('passed')
originals = [peerpath,
    Path('/tmp/check-applied26-canonical-and-whole371-candidate-independent-foundations-v1.py'),
    Path('/tmp/applied26-canonical-and-whole371-candidate-independent-foundations-actual-v1.json'),
    Path('/tmp/applied26-canonical-and-whole371-candidate-independent-foundations-actual-v1.log'),
    Path('/tmp/run-applied26-canonical-and-candidate-independent-foundations-v1.py')]
archive = BASE / 'original-independent-canonical-candidate-peer'
archive.mkdir(exist_ok=False)
aliases = {}
for original in originals:
    dest = archive / original.name
    shutil.copyfile(original, dest)
    assert H(dest) == H(original)
    aliases[str(original)] = ref(dest)
actual = read(originals[2])
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
logpath = actual.get('raw_log', actual.get('log'))
logsha = actual.get('raw_log_sha256', actual.get('log_sha256'))
assert logpath == str(originals[3]) and H(originals[3]) == logsha
candidate = {'file': draft['mapped_ledger'], 'sha256': draft['mapped_ledger_sha256']}
promotions = {'file': draft['mapped_promotions'], 'sha256': draft['mapped_promotions_sha256']}
assert peer['candidate_ledger'] == candidate and peer['candidate_promotions'] == promotions
for row in [candidate, promotions]:
    assert H(ROOT / row['file']) == row['sha256']
interface = {
    'status': 'passed_independent_read_only_applied26_candidate_mechanics_preserved_original_review_interface',
    'errors': [], 'reviewer': peer['reviewer'], 'reviewed_at_utc': peer['reviewed_at_utc'],
    'candidate': candidate, 'candidate_promotions': promotions,
    'original_independent_review': aliases[str(peerpath)],
    'entire_original_independent_review_body_and_time': peer,
    'original_closed_byte_aliases': aliases,
    'actual_read_only_checker': aliases[str(originals[2])],
    'actual_checker_raw_log': aliases[str(originals[3])],
    'interface_prepared_by': 'applied_next',
    'interface_prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'normalization_scope': 'Canonical pointers and candidate key aliases only; entire original independent body, status, decisions, reviewer and review time preserved. No new semantic decision or compiler result.'}
ip = BASE / 'applied26-canonical-candidate-independent-foundations-interface-v1.json'
put(ip, interface)
catalog = BASE / 'original-independent-canonical-candidate-peer-byte-aliases-v1.json'
put(catalog, {'status': 'all_five_closed_original_independent_reader_artifacts_byte_identically_archived',
              'original_closed_byte_aliases': aliases, 'original_review_body_and_time_unchanged': True,
              'genuine_reader_exit_code': 0, 'reader_failures': []})
out = copy.deepcopy(draft)
out.update(status='independently_reviewed_isolated_applied26_source52_material_candidate_ready_for_root_selection', errors=[],
           original_draft_offer=ref(draftpath), candidate=candidate, candidate_promotions=promotions,
           final_independent_candidate_mapping_peer=ref(ip),
           original_final_independent_candidate_mapping_peer=aliases[str(peerpath)],
           independent_review_original_byte_aliases=ref(catalog))
prep = ROOT / 'book/coverage/checks/applied-future26/applied26-isolated-joint-density-candidate-actual-v2.json'
execution = read(prep)
assert type(execution['actual_exit_code']) is int and execution['actual_exit_code'] == 0
raw = ROOT / execution['raw_log']
assert H(raw) == execution['raw_log_sha256']
out['actual_isolated_candidate_preparation'] = ref(prep)
out['actual_isolated_candidate_raw_log'] = ref(raw)
required = {r['file']: r['sha256'] for r in aliases.values()}
for r in [ref(draftpath), ref(ip), ref(catalog), ref(prep), ref(raw), draft['original_review_bindings'], draft['canonical_path_aliases']]:
    required[r['file']] = r['sha256']
for n, row in draft['proof_files'].items():
    required[n] = row['sha256']
    required.update(row['evidence_sha256'])
for row in read(ROOT / draft['canonical_path_aliases']['file'])['aliases'].values():
    required[row['file']] = row['sha256']
for row in draft['preserved_initial_builder_failure']:
    required[row['file']] = row['sha256']
for row in draft['baseline25_owner_assets']:
    r = row['exact_byte_copy']; required[r['file']] = r['sha256']
for n, h in required.items():
    p = Path(n)
    assert not p.is_absolute() and '..' not in p.parts and H(ROOT / p) == h, n
out['required_evidence_artifacts_sha256'] = required
out['additional_frozen_inputs'] = sorted(required)
out['finalization_scope'] = 'Independent canonical/body/pair/candidate mechanics and five exact closed reader originals added only. Entire draft semantics/review times, candidate/promotions, three sources/23 theorem exports/six executions unchanged. Only whole371 promoted in isolated candidate; CVaR8 supplied explicitly cross-owner. No live owner, global26, aggregate or fixed25 change.'
restored = copy.deepcopy(out)
for key in set(out) - set(draft):
    restored.pop(key)
restored['status'] = draft['status']
assert restored == draft
final = BASE / 'applied-audit26-candidate-source52-additions-v2-reviewed.json'
put(final, out)
print(json.dumps({'offer': ref(final), 'peer_interface': ref(ip), 'candidate': candidate,
                  'archived_originals': len(aliases), 'required_closed_artifacts': len(required), 'counts': out['counts']}))
