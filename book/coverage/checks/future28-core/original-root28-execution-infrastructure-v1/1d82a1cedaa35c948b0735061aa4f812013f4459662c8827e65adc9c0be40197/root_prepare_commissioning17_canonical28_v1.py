"""Prepare the separate reviewed commissioning17 compiler batch, after ten pairs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQUEST = Path('/tmp/modules-sensor-commissioning17-full-literal-request28-v1.json')
PEER = Path('/tmp/modules-sensor-commissioning17-independent-foundations28-v2.json')
PLAN = Path('/tmp/root28-current60-commissioning17-canonical-plan-v1.json')
HELPER = ROOT/'book/coverage/checks/run_root28_current60_commissioning17_canonical_pair_v1.py'
PREVIOUS = ROOT/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json'
ACTUAL = ROOT/'reports/full-coverage/current60-canonical-pairs28-execution-v1.json'
ORIGINAL = ROOT/'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file':p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p), 'sha256':sha(p)}
def checked(r):
    p = Path(r['file']); p = p if p.is_absolute() else ROOT/p
    assert p.is_file() and not p.is_symlink() and sha(p) == r['sha256']
    return p
def new(p, data):
    assert not p.exists(); p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(data)

assert sha(ORIGINAL) == '69a8eab0c5710ea143dde3c72ecf08c5c6811fa87536cec688c3fe2ea7afbe83'
assert sha(REQUEST) == '703127795cfdd8b5f924d0b74932796c31e3a6d926d7771db6dbcf9698a447c3'
assert sha(PEER) == 'c9b176bd7619152f68fe1437ba5ebdcffa0595b1da2947412b63030c2be19d09'
prior = json.loads(PREVIOUS.read_bytes()); actual = json.loads(ACTUAL.read_bytes())
assert prior['status'] == 'passed_actual10_current60_canonical_standalone_and_named_pairs_unselected_future28'
assert prior['errors'] == [] and prior['actual_compiler_command_count'] == 20
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
assert actual['helper_sha256_before'] == actual['helper_sha256_after'] == {ref(ORIGINAL)['file']:sha(ORIGINAL)}
checked({'file':actual['log'], 'sha256':actual['log_sha256']})
request = json.loads(REQUEST.read_bytes()); peer = json.loads(PEER.read_bytes())
source_ref = {k:request['source'][k] for k in ('file','sha256')}
source = checked(source_ref)
assert peer['status'] == 'passed_independent_full17_source_two_whole_commissioning_literals_review' and peer['errors'] == []
assert peer['source'] == source_ref
assert all(r['whole_unit_approved'] is True and r['missing_clauses'] == [] for r in peer['material_units'])
assert {r['inventory_key'] for r in peer['material_units']} == {'lipsdp.html::node-972','lipsdp.html::node-974'}
names = request['public_theorem_names']
bare = re.findall(r'^(?:theorem|lemma)\s+([A-Za-z0-9_]+)',source.read_text(),re.M)
assert len(bare) == len(names) == 17 and [n.rsplit('.',1)[1] for n in names] == bare
trial_ref = {k:request['actual_current60_tmp_trial'][k] for k in ('file','sha256')}
trial = json.loads(checked(trial_ref).read_bytes())
assert type(trial['actual_exit_code']) is int and trial['actual_exit_code'] == 0
assert trial['source_sha256_before'] == trial['source_sha256_after'] == source_ref['sha256']
destination = 'verification/lean/SafeLearning/CompleteModulesSensorCommissioning28.lean'
assert not (ROOT/destination).exists()

text = ORIGINAL.read_text()
replacements = {
    'current60-canonical-pairs-v1':'current60-commissioning17-canonical-pair-v1',
    'actual-current60-canonical-paired-readiness28-v1.json':'actual-current60-commissioning17-canonical-paired-readiness28-v1.json',
    'root28-canonical-pair-readonly-unused-v1.json':'root28-commissioning17-readonly-unused-v1.json',
    'exact_reviewed_current60_new_source_canonical_pair_plan_only':'exact_reviewed_current60_commissioning17_canonical_pair_plan_only',
    "len(rows) == plan['source_count'] == 10":"len(rows) == plan['source_count'] == 1",
    "len(exported) == plan['public_theorem_count'] == 235":"len(exported) == plan['public_theorem_count'] == 17",
    "'ready_exact10_new_canonical_sources_only'":"'ready_exact1_commissioning17_new_canonical_source_only'",
    "'source_count':10,'public_theorems':235":"'source_count':1,'public_theorems':17",
    'len(pairs) == 20':'len(pairs) == 2',
    'passed_actual10_current60_canonical_standalone_and_named_pairs_unselected_future28':'passed_actual1_current60_commissioning17_canonical_standalone_and_named_pair_unselected_future28',
    "'source_count':10,'public_theorem_count':235":"'source_count':1,'public_theorem_count':17",
    "'actual_compiler_command_count':20":"'actual_compiler_command_count':2",
    "'sources':10,'public_theorems':235,'actual_commands':20":"'sources':1,'public_theorems':17,'actual_commands':2",
}
for old, new_text in replacements.items():
    assert text.count(old) == 1, old
    text = text.replace(old,new_text)
marker = '    names, exported = set(), set()\n'
assert text.count(marker) == 1
prefix = '''    # Hold the ten completed new modules and every native paired receipt too.
    prior_p = checked(plan['prior_completed_pairs']); prior = json.loads(prior_p.read_bytes())
    assert prior['status'] == 'passed_actual10_current60_canonical_standalone_and_named_pairs_unselected_future28'
    assert prior['errors'] == [] and prior['source_count'] == 10 and prior['actual_compiler_command_count'] == 20
    actual_p = checked(plan['prior_completed_pair_execution']); actual = json.loads(actual_p.read_bytes()); zero(actual)
    assert actual['actual_command'] == ['python3','book/coverage/checks/run_root28_current60_canonical_pairs_v2.py','--plan','/tmp/root28-current60-canonical-pair-plan-v1.json','--plan-sha256','64fe57b1296bf5d016eaf3da375a382454ea8c310c23c3421220000f0565533b','--apply']
    assert actual['actual_workdir'] == str(ROOT) and actual['helper_sha256_before'] == actual['helper_sha256_after']
    for n,h in actual['helper_sha256_after'].items(): originals[str(locate(n))] = h
    prior_log = checked({'file':actual['log'],'sha256':actual['log_sha256']})
    for p in [prior_p,actual_p,prior_log]: originals[str(p)] = sha(p)
    assert len(prior['actual_paired_records']) == 20
    for row in prior['sources']:
        p = locate(row['canonical_source']); assert sha(p) == row['original_tmp_source']['sha256']
        protected[row['canonical_source']] = sha(p)
    for row in prior['actual_paired_records']:
        assert type(row['actual_exit_code']) is int and row['actual_exit_code'] == 0
        for key in ('actual_record','raw_log','source_snapshot'):
            p = checked(row[key]); originals[str(p)] = sha(p)
'''
text = text.replace(marker,prefix+marker)
compile(text,str(HELPER),'exec')
plan = {'status':'exact_reviewed_current60_commissioning17_canonical_pair_plan_only',
        'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':1,'public_theorem_count':17,
        'sources':[{'canonical_source':destination,'original_tmp_source':source_ref,'public_theorem_count':17,
                    'public_declarations':names,'original_actual_tmp_trial':trial_ref,
                    'independent_whole_scope_peer':ref(PEER),'expected_peer_status':peer['status'],
                    'original_semantic_review_time_unchanged':True,'canonical_compiler_records_pending':True}],
        'original_scope_plans':[ref(REQUEST)],'prior_completed_pairs':ref(PREVIOUS),
        'prior_completed_pair_execution':ref(ACTUAL), 'prepared_by':ref(Path(__file__)),
        'current60_inventory':ref(ROOT/'book/coverage/inventory.json'),
        'canonical_installation_or_coverage_promotion_claimed':False}
new(HELPER,text.encode()); new(PLAN,(json.dumps(plan,indent=2)+'\n').encode())
print(json.dumps({'helper':ref(HELPER),'plan':ref(PLAN),'source_count':1,'public_theorems':17}))
