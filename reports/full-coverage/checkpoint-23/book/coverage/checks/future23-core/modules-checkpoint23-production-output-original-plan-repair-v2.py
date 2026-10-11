"""Prepare a new plan for four strictly authorized historical evidence aliases.

This helper writes only a distinct plan. Root executes it only after independent
review; it never selects proofs or changes sources, ledgers or original plans.
"""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book/coverage'))
from retain_baseline_inputs23_v2 import validate_owner_evidence_aliases

OLD_PLAN = 'book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v1.json'
NEW_PLAN = 'book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v2.json'
OLD_SELECTOR = 'book/coverage/prepare_checkpoint23_selection_v1.py'
OLD_RETAINER = 'book/coverage/retain_baseline_inputs23.py'
NEW_SELECTOR = 'book/coverage/prepare_checkpoint23_selection_v2.py'
NEW_RETAINER = 'book/coverage/retain_baseline_inputs23_v2.py'
BASELINE = 'reports/full-coverage/checkpoint-22-selection.json'
MANIFEST = 'reports/full-coverage/checkpoint-22-manifest.json'
FAILED_EXECUTION = 'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json'

def safe(name):
    p = Path(name)
    assert isinstance(name, str) and name and not p.is_absolute() and '..' not in p.parts and str(p) == name
    assert (ROOT/p).resolve().is_relative_to(ROOT.resolve())
    return ROOT/p
def sha(name): return hashlib.sha256(safe(name).read_bytes()).hexdigest()
def read(name): return json.loads(safe(name).read_text())
def ref(name): return {'file':name,'sha256':sha(name)}

def prepare():
    assert not safe(NEW_PLAN).exists()
    assert not safe('reports/full-coverage/checkpoint-23-selection.json').exists()
    assert not safe('book/coverage/checks/frozen22-input-content-bindings23-v1.json').exists()
    original = read(OLD_PLAN)
    assert original['status'] == 'independently_reviewed_installed_owner23_selection_plan'
    assert original['inventory']['sha256'] == sha('book/coverage/inventory.json') == sha(original['inventory']['file']) == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
    for name,digest in original['helpers_sha256'].items(): assert sha(name) == digest
    assert original['helpers_sha256'][OLD_SELECTOR] == '5811fc10687074862bfbb273017eb72c2f8990b4e44a18a4f2cf05c7037a8f67'
    failed = read(FAILED_EXECUTION)
    assert type(failed['actual_exit_code']) is int and failed['actual_exit_code'] == 1
    assert failed['actual_command'] == ['python3',OLD_SELECTOR,'--plan',OLD_PLAN]
    assert failed['helper_sha256_before'] == failed['helper_sha256_after']
    for name,digest in failed['helper_sha256_after'].items(): assert sha(name) == digest
    assert sha(failed['log']) == failed['log_sha256']
    assert 'AssertionError: book/coverage/foundations.json' in safe(failed['log']).read_text()
    manifest = read(MANIFEST)
    integration_ref = original['owners']['modules']['integration_result']
    actual_ref = original['owners']['modules']['actual_builder']
    integration = read(integration_ref['file'])
    assert sha(integration_ref['file']) == integration_ref['sha256']
    rows = {row['destination']:row for row in integration['exact_replacements']}
    aliases = {}
    for owner in ('core','foundations','applied','modules'):
        name = 'book/coverage/'+owner+'.json'
        row = rows[name]
        old_sha = manifest['working_inputs_sha256'][name]
        assert row['before_sha256'] == old_sha
        aliases[name] = {'original_sha256':old_sha,'immutable_byte_copy':{'file':row['original22_byte_copy'],'sha256':old_sha}}
    authorization = {'actual_integration_execution':actual_ref,'integration_result':integration_ref,'aliases':aliases}
    validate_owner_evidence_aliases(ROOT,BASELINE,MANIFEST,authorization)
    out = copy.deepcopy(original)
    helpers = dict(out['helpers_sha256'])
    assert set(helpers) == {OLD_SELECTOR,OLD_RETAINER}
    out['helpers_sha256'] = {NEW_SELECTOR:sha(NEW_SELECTOR),NEW_RETAINER:sha(NEW_RETAINER)}
    additions = {
        'authorized_baseline_owner_evidence_aliases':authorization,
        'original_failed_selector_v1_provenance':{'original_plan':ref(OLD_PLAN),'original_selector':ref(OLD_SELECTOR),'original_retainer':ref(OLD_RETAINER),'actual_failed_execution':ref(FAILED_EXECUTION),'actual_failed_raw_log':ref(failed['log'])},
        'baseline_owner_evidence_alias_plan_preparation_helper':ref(str(Path(__file__).relative_to(ROOT))),
        'baseline_owner_evidence_alias_plan_prepared_at_utc':datetime.now(timezone.utc).isoformat(),
        'requires_independent_narrow_v2_alias_helper_review':True,
        'baseline_owner_evidence_alias_scope':'Only the four original working-owner evidence paths may use their genuine pre-integration archive bytes. All original baseline proof sources, original row bodies/path hashes, other evidence names, original candidate math/review times and prior plans remain unchanged; no production selection or new aggregate audit is claimed.'}
    assert not set(additions)&set(original)
    out.update(additions)
    reverse=copy.deepcopy(out)
    for key in additions: reverse.pop(key)
    reverse['helpers_sha256']=original['helpers_sha256']
    assert reverse == original
    with safe(NEW_PLAN).open('x') as output: output.write(json.dumps(out,indent=2)+'\n')
    return {'plan':ref(NEW_PLAN),'authorized_old_owner_evidence_path_count':4,'original_plan_entire_body_reversible_exact':True}

if __name__ == '__main__': print(json.dumps(prepare()))
