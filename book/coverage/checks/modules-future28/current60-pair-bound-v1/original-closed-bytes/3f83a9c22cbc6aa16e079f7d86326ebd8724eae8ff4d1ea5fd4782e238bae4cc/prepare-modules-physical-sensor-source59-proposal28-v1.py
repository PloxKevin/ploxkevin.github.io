from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, importlib.util, json, sys, tempfile

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/modules-physical-sensor-source59-proposal28-v1')
SOURCE = 'SafeLearning/lipsdp.html'
INVENTORY_SHA = '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
SOURCE_SHA = '5e7c877f192c0d42ec5e725d10c1dd07ec4fbcb1d6ab1abf0e4f9c5744ce3471'
PARSER_SHA = 'b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
OLD = r'0.06/0.065320\approx0.918559'
NEW = r'0.06/(2\sqrt{4/3}\sqrt2(0.02))\approx0.918559'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def ref(p):
    return {'file': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}

def write(p, value):
    with p.open('x') as f:
        f.write(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

assert not OUT.exists()
source = ROOT / SOURCE
invpath = ROOT / 'book/coverage/inventory.json'
parser = ROOT / 'book/inventory_claims.py'
ownerpath = ROOT / 'book/coverage/modules.json'
assert sha(source) == SOURCE_SHA and sha(invpath) == INVENTORY_SHA and sha(parser) == PARSER_SHA
inventory = json.loads(invpath.read_bytes())
ledger = json.loads(ownerpath.read_bytes())
text = source.read_text()
assert text.count(OLD) == 1 and NEW not in text
candidate = text.replace(OLD, NEW, 1).encode()
assert candidate.count(b'\n') == source.read_bytes().count(b'\n')
assert candidate.decode().replace(NEW, OLD, 1).encode() == source.read_bytes()
OUT.mkdir()
candidatepath = OUT / 'lipsdp-proposed-source59.html'
with candidatepath.open('xb') as f:
    f.write(candidate)
with tempfile.TemporaryDirectory(prefix='modules-source59-full29-parser-') as td:
    isolated = Path(td)
    (isolated / 'SafeLearning').mkdir()
    for page in (ROOT / 'SafeLearning').glob('*.html'):
        target = isolated / 'SafeLearning' / page.name
        target.write_bytes(candidate if page == source else page.read_bytes())
    sys.path.insert(0, str(ROOT / 'book'))
    spec = importlib.util.spec_from_file_location('modules_source59_isolated_full29_parser', parser)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = isolated
    module.OUT = isolated / 'book/coverage'
    assert module.ROOT.resolve().is_relative_to(Path('/tmp'))
    assert module.OUT.resolve().is_relative_to(module.ROOT)
    assert module.ROOT != ROOT and module.OUT != ROOT / 'book/coverage'
    module.inventory()
    parsed_bytes = (module.OUT / 'inventory.json').read_bytes()
parsed = json.loads(parsed_bytes)
proposed_inventory = OUT / 'inventory-proposed-source59-v1.json'
with proposed_inventory.open('xb') as f:
    f.write(parsed_bytes)
assert parsed['counts'] == inventory['counts'] and len(parsed['source_sha256']) == 29
assert parsed['source_sha256'] == {**inventory['source_sha256'], SOURCE: sha(candidatepath)}
changes = {}
records = {}
for field in ['exercises', 'material_source_units']:
    old = {u['key']: u for u in inventory[field]}
    new = {u['key']: u for u in parsed[field]}
    assert old.keys() == new.keys()
    changes[field] = []
    for key in old:
        a = copy.deepcopy(old[key])
        b = copy.deepcopy(new[key])
        if a['source'] == SOURCE:
            assert b['source_sha256'] == sha(candidatepath)
            a.pop('source_sha256')
            b.pop('source_sha256')
        if a != b:
            assert {k: v for k, v in a.items() if k not in ['source_text', 'text_sha256']} == {
                k: v for k, v in b.items() if k not in ['source_text', 'text_sha256']}
            changes[field].append(key)
            records[key] = {'entire_original_inventory_record': old[key], 'entire_proposed_inventory_record': new[key]}
assert changes == {'exercises': ['lipsdp.html#book-m12-b1'], 'material_source_units': ['lipsdp.html::node-998']}
keys = ['lipsdp.html::node-' + str(n) for n in (964, 965, 969, 971, 987, 994, 998)]
units = {u['key']: u for u in inventory['material_source_units'] if u['key'] in keys}
exercise = next(e for e in ledger['exercises'] if e['key'] == 'lipsdp.html#book-m12-b1')
claims = {k: [{'id': c['id'], 'status': c['status'], 'kind': c['kind'],
               'statement_in_prose': c['statement_in_prose'], 'remaining_gaps': c['remaining_gaps']}
              for c in ledger['material_claims'] if k in c.get('source_unit_keys', [])] for k in keys}
packet = {
    'status': 'tmp_only_source59_exact_denominator_proposal_requires_independent_review',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'author': '/root/modules_finish28',
    'prospective_source_batch': 59,
    'source_batch_order': 'After Root planned 56, 57, 58. No canonical application in this preparation.',
    'before_inventory': ref(invpath), 'source': ref(source), 'parser': ref(parser),
    'current_modules_owner': ref(ownerpath),
    'before_raw_fragment': OLD, 'after_raw_fragment': NEW,
    'proposed_source': ref(candidatepath), 'proposed_full29_inventory': ref(proposed_inventory),
    'fresh_parser_changed_text_keys': changes,
    'full_current_context_lines796_to802': ''.join(text.splitlines(keepends=True)[795:802]),
    'full_proposed_context_lines796_to802': ''.join(candidate.decode().splitlines(keepends=True)[795:802]),
    'current_material_units': units, 'current_pending_claims': claims,
    'entire_original_exercise_owner_row': exercise, 'entire_changed_records': records,
    'rationale': 'The literal quotient uses the rounded certificate value 0.065320 as an exact denominator, which rounds to 0.918555 at six decimals. The intended exact certificate denominator gives 3 sqrt(6)/8, which rounds to the existing target 0.918559. Replacing only the denominator retains the exact intended threshold and numerical target.',
    'exact_certificate_denominator': r'2\sqrt{4/3}\sqrt2(0.02)',
    'exact_threshold': r'3\sqrt6/8',
    'formal_draft_reference_only': ref(Path('/tmp/CompleteModulesPhysicalSensorBox28-draft-v2.lean')),
    'exact_reverse_to_entire_current_source_bytes': True,
    'all_other28_pages_and_all_other_literal_records_unchanged': True,
    'both_parser_ROOT_and_OUT_isolated': True,
    'coverage_or_lean_compiler_or_live_write_claimed': False,
    'limits': [
        'The current full exercise and node998 contain the inconsistent rounded denominator; neither is proposed whole complete under current55.',
        'The source wording fix needs independent full-literal and isolated parser review before Root applies it.',
        'Actual SDP matrix, scalar ReLU incremental constraints, raw unit normalization, Euclidean radius, exact attained box error, actual region derivatives, and scaled hardware bound are separate required proof evidence.',
        'A TMP parser result is not mathematical coverage or an installed proof.',
        'Root alone handles canonical source/owner/selection/publication/Git changes.'
    ]
}
write(OUT / 'modules-physical-sensor-source59-proposal28-v1.json', packet)
assert sha(source) == SOURCE_SHA and sha(invpath) == INVENTORY_SHA and sha(parser) == PARSER_SHA
print(json.dumps({'status': packet['status'], 'proposal': ref(OUT / 'modules-physical-sensor-source59-proposal28-v1.json'), 'changed': changes}))
