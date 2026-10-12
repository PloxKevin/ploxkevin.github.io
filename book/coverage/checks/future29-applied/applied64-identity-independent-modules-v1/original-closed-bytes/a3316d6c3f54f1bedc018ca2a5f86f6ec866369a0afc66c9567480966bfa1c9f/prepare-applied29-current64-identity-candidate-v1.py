"""Prepare only Applied's Source64 identity overlay in an unused TMP directory."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/applied29-current64-identity-v1')
CTX = Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
CONTEXT_SHA = '442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def path(n): return Path(n) if Path(n).is_absolute() else ROOT / n
def ref(p):
    p = Path(p)
    return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256':sha(p)}
def put(p, obj):
    with Path(p).open('x') as f: f.write(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')
def strict_zero(obj):
    codes = [obj[k] for k in ('actual_exit_code', 'exit_code') if k in obj]
    assert codes and all(type(v) is int and v == 0 for v in codes)

assert sha(CTX) == CONTEXT_SHA
ctx = read(CTX)
assert ctx['status'] == 'actual_current64_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'
held = {}
for mapping in (ctx['pins_sha256'], ctx['held_current_source_sha256'], ctx['owners_sha256']):
    for n, h in mapping.items():
        assert n not in held or held[n] == h, n
        held[n] = h
assert len(ctx['owners_sha256']) == 5
SELECT = path(ctx['selection']['file']); assert sha(SELECT) == ctx['selection']['sha256']
selected = read(SELECT)
assert selected['proof_file_count'] == len(selected['proof_files']) == 1186
for n, row in selected['proof_files'].items(): assert held[n] == row['sha256'], n
AUDIT = path(ctx['actual_audit']['file']); assert sha(AUDIT) == ctx['actual_audit']['sha256']
assert len(read(AUDIT)['declarations']) == 9896

LEDGER = ROOT / 'book/coverage/applied.json'
PROMOTIONS = ROOT / 'book/coverage/applied-promotions.json'
assert sha(LEDGER) == ctx['owners_sha256']['book/coverage/applied.json'] == '447a97e920f8155b64067a4db0d3a785f3fe1d14e8154f05943f70d085c9f31e'
assert sha(PROMOTIONS) == ctx['owners_sha256']['book/coverage/applied-promotions.json'] == 'fd6cee003ac36731f99ac5d2db20354f798c83f991c4c02710588eaa6a94100d'
ledger, promotions = read(LEDGER), read(PROMOTIONS)
PRIOR = ROOT / 'book/coverage/checks/applied-future28/current60-identity-v1/applied28-current60-identity-offer-canonical-v2.json'
assert sha(PRIOR) == '88ad2de6dcd03bc01186c0803bb165746886227e9e06e654bf9ff7357e9f4d4f'
prior = read(PRIOR)
assert prior['status'] == 'independently_reviewed_isolated_applied28_current60_identity_offer' and prior['errors'] == []
assert sha(path(prior['candidate']['file'])) == prior['candidate']['sha256'] == sha(LEDGER)
assert sha(path(prior['candidate_promotions']['file'])) == prior['candidate_promotions']['sha256'] == sha(PROMOTIONS)
assert read(path(prior['candidate']['file'])) == ledger
assert read(path(prior['candidate_promotions']['file'])) == promotions
inherited = dict(prior['required_evidence_artifacts_sha256'])
assert len(inherited) == 235
for n, h in inherited.items(): assert sha(path(n)) == h, n
for original, alias in prior['original_closed_byte_aliases'].items():
    assert set(alias) == {'file', 'sha256'} and sha(path(alias['file'])) == alias['sha256'], original

OLD = ROOT / 'book/coverage/inventory-after-correction60.json'
NEW = ROOT / 'book/coverage/inventory-after-correction64.json'
assert sha(OLD) == '6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert sha(NEW) == sha(ROOT / 'book/coverage/inventory.json') == '11136add476e6b5be58f4bc6ea038602d51016a7e8370eeb67e17e9358893f98'
old, new = read(OLD), read(NEW)
scope = set(ledger['scope_pages']); assert len(scope) == 3
assert ledger['source_sha256'] == {n:old['source_sha256'][n] for n in scope} == {n:new['source_sha256'][n] for n in scope}
for section, count in [('exercises',128), ('material_source_units',2059)]:
    a = {row['key']:row for row in old[section] if row['source'] in scope}
    b = {row['key']:row for row in new[section] if row['source'] in scope}
    assert a == b and len(a) == count, section
assert len(ledger['exercises']) == 128 and sum(len(e['claims']) for e in ledger['exercises']) == 468
assert len(ledger['material_claims']) == 1954 and len(ledger['proof_files']) == 312
assert 'current64_owner_identity' not in ledger and 'current64_owner_identity' not in promotions
APP = path(ctx['actual_source61_to64_application']['file']); ACT = path(ctx['actual_application_native']['file'])
assert sha(APP) == ctx['actual_source61_to64_application']['sha256']
assert sha(ACT) == ctx['actual_application_native']['sha256']
app, actual = read(APP), read(ACT)
assert app['status'] == 'passed_actual_source61_to64_corrections_full29_inventory_owner_identity_rebase_pending'
assert [r['correction_id'] for r in app['applications']] == [61,62,63,64]
assert app['selected28_proof_sources_unchanged'] == 1186 and app['five_installed28_owner_ledgers_unchanged'] is True
assert all(r['source_after']['file'] not in scope for r in app['applications'])
strict_zero(actual); assert actual['status'] == 'passed'
assert actual['actual_command'] == ['python3','book/coverage/checks/root_apply_source61_64_v1.py','apply','--contract-sha256',app['contract']['sha256']]
assert actual['actual_workdir'] == str(ROOT)
assert actual['helper_sha256_before'] == actual['helper_sha256_after']
assert sha(path(actual['log'])) == actual['log_sha256']
for n,h in actual['helper_sha256_after'].items(): assert sha(path(n)) == h

SELF = Path(__file__); self_sha = sha(SELF)
def guard():
    assert sha(SELF) == self_sha and sha(CTX) == CONTEXT_SHA
    for n,h in held.items(): assert sha(path(n)) == h, n
    for n,h in inherited.items(): assert sha(path(n)) == h, n
guard()
OUT.mkdir(exist_ok=False); originals = OUT / 'original-installed28'; originals.mkdir()
for source in (LEDGER, PROMOTIONS):
    with (originals / source.name).open('xb') as f: f.write(source.read_bytes())
    assert sha(originals / source.name) == sha(source)
side = OUT / 'applied29-current64-entire-owned-literal-identity-v1.json'
put(side, {
    'status':'passed_actual_applied_source60_to64_entire_owned_literal_identity', 'errors':[],
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'historical_inventory':ref(OLD), 'current_inventory':ref(NEW), 'actual_source61_to64_application':ref(APP),
    'actual_application_execution':ref(ACT), 'original_reviewed_current60_offer':ref(PRIOR),
    'original_installed28_ledger':ref(originals / LEDGER.name), 'original_installed28_promotions':ref(originals / PROMOTIONS.name),
    'owned_source_sha256_unchanged':copy.deepcopy(ledger['source_sha256']),
    'entire_equal_owned_inventory_records':{'exercises':128, 'material_source_units':2059},
    'unchanged_original_ledger_records':{'exercise_claims':468,'material_claims':1954,'proof_metadata_rows':312},
    'changed_owned_literals':[], 'new_proof_sources':0, 'new_mathematical_decisions':0,
    'inverse_recipe':'Delete only the added current64_owner_identity top-level field from both candidates. Every remaining key, array, record, semantic body, hypothesis, review time and generated time is the entire installed28 original. Original bytes are retained separately.',
    'coverage_complete':False, 'semantic_review_redecided':False,
    'scope':'Identity-only metadata overlay. The actual Source61–64 edits are on other owners pages; all three Applied pages and all original mathematics remain unchanged.'
})
overlay = {'inventory':str(NEW.relative_to(ROOT)), 'inventory_sha256':sha(NEW), 'identity_sidecar':ref(side),
    'original_installed28_ledger':ref(originals / LEDGER.name), 'original_installed28_promotions':ref(originals / PROMOTIONS.name),
    'original_reviewed_current60_offer':ref(PRIOR), 'actual_source61_to64_application':ref(APP),
    'changed_owned_literals':[], 'new_proof_sources':0, 'new_mathematical_decisions':0,
    'scope':'Current64 identity only. All installed28 mathematical fields, proofs, statuses, semantic review bodies and review times remain entire and unchanged.'}
candidate, candidate_promotions = copy.deepcopy(ledger), copy.deepcopy(promotions)
candidate['current64_owner_identity'] = copy.deepcopy(overlay)
candidate_promotions['current64_owner_identity'] = copy.deepcopy(overlay)
reverse, reverse_promotions = copy.deepcopy(candidate), copy.deepcopy(candidate_promotions)
reverse.pop('current64_owner_identity'); reverse_promotions.pop('current64_owner_identity')
assert reverse == ledger and reverse_promotions == promotions
assert json.dumps(reverse,indent=2,ensure_ascii=False)+'\n' == LEDGER.read_text()
assert json.dumps(reverse_promotions,indent=2,ensure_ascii=False)+'\n' == PROMOTIONS.read_text()
CAND = OUT / 'applied29-current64-identity-candidate-v1.json'; PROM = OUT / 'applied-promotions29-current64-identity-candidate-v1.json'
put(CAND,candidate); put(PROM,candidate_promotions)
integrity = OUT / 'applied29-current64-identity-candidate-integrity-v1.json'
put(integrity, {'status':'passed_actual_isolated_applied29_current64_identity_candidate_mechanics','errors':[],
    'candidate':ref(CAND), 'candidate_promotions':ref(PROM), 'identity_sidecar':ref(side),
    'exact_inverse_recovers_both_entire_installed28_original_bytes':True,
    'new_proof_sources':0,'new_mathematical_decisions':0,'coverage_complete':False,'live_owner_written':False,
    'guard_counts':{'actual_selected_proofs':1186,'actual_public_declarations':9896,'current_assets':31,'installed28_owner_ledgers':5}})
refs = dict(inherited)
for p in (PRIOR,OLD,NEW,APP,ACT,path(actual['log']),SELECT,AUDIT,CTX,SELF,side,integrity,originals/LEDGER.name,originals/PROMOTIONS.name):
    r = ref(p); assert r['file'] not in refs or refs[r['file']] == r['sha256']; refs[r['file']] = r['sha256']
for n,h in actual['helper_sha256_after'].items(): assert n not in refs or refs[n] == h; refs[n] = h
offer = OUT / 'applied29-current64-identity-offer-draft-v1.json'
put(offer, {'schema_version':1,'status':'isolated_applied29_current64_identity_candidate_awaiting_independent_mechanics','errors':[],
    'inventory':str(NEW.relative_to(ROOT)),'inventory_sha256':sha(NEW), 'base_selection':ref(SELECT),
    'candidate':ref(CAND),'candidate_promotions':ref(PROM),'mapped_ledger':str(CAND),'mapped_ledger_sha256':sha(CAND),
    'mapped_promotions':str(PROM),'mapped_promotions_sha256':sha(PROM),'source_sha256':copy.deepcopy(ledger['source_sha256']),
    'candidate_builder':ref(SELF),'identity_sidecar':ref(side),'identity_integrity':ref(integrity),
    'original_reviewed_current60_offer':ref(PRIOR),'original_complete_independent_peer':copy.deepcopy(prior['original_complete_independent_peer']),
    'proof_files':{},'new_actual_paired_records':[],'new_material_keys':[],'new_exercises':[], 'counts':copy.deepcopy(ledger['counts']),
    'required_evidence_artifacts_sha256':refs,'original_closed_byte_aliases':copy.deepcopy(prior['original_closed_byte_aliases']),
    'actual_isolated_candidate_preparation':None,'final_independent_candidate_mapping_peer':None,
    'coverage_complete':False,'scope':'TMP-only Applied identity candidate; no new proofs, exercise/material decisions or canonical/PUB/installed owner writes.'})
guard()
print(json.dumps({'candidate':ref(CAND),'candidate_promotions':ref(PROM),'offer':ref(offer),'identity_sidecar':ref(side),
    'integrity':ref(integrity),'inherited_evidence_count':len(inherited),'closed_evidence_count':len(refs),'new_proofs':0,'new_decisions':0}))
