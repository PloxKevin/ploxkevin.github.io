"""Run the unchanged ledger validator on an external temporary symlink tree."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys, tempfile

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def exact(r):
    p = Path(r['file'])
    p = p if p.is_absolute() else ROOT / p
    assert not p.is_symlink() and sha(p) == r['sha256'], str(p)
    return p

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--binding', type=Path, required=True)
ap.add_argument('--binding-sha256', required=True)
ap.add_argument('--tag', required=True)
args = ap.parse_args()
binding = args.binding.resolve()
assert binding.is_relative_to(BASE) and sha(binding) == args.binding_sha256
data = json.loads(binding.read_bytes())
inventory = exact(data['inventory'])
sources = {r['destination']: exact(r['candidate']) for r in data['replacements']}
assert set(sources) == {'book/coverage/'+d+'.json' for d in ['foundations', 'applied', 'modules', 'core']}
spec = importlib.util.spec_from_file_location('owner34_unchanged_ledger_validator', ROOT/'book/coverage/validate.py')
validator = importlib.util.module_from_spec(spec)
sys.path.insert(0, str(ROOT/'book/coverage'))
spec.loader.exec_module(validator)
with tempfile.TemporaryDirectory(prefix='safetybased-owner34-ledger-') as name:
    isolated = Path(name)
    assert not isolated.is_relative_to(ROOT)
    (isolated/'book/coverage').mkdir(parents=True)
    (isolated/'verification').mkdir()
    (isolated/'SafeLearning').symlink_to(ROOT/'SafeLearning', target_is_directory=True)
    (isolated/'verification/lean').symlink_to(ROOT/'verification/lean', target_is_directory=True)
    (isolated/'book/coverage/inventory.json').symlink_to(inventory)
    for n,p in sources.items():
        (isolated/n).symlink_to(p)
    validator.ROOT = isolated
    report = validator.validate()
    report['actual_candidate_validation_context'] = {
        'temporary_ROOT_outside_workspace': True, 'candidate_owners_are_exact_symlinks': True,
        'old_owner_snapshot_or_cache_copied': False, 'binding': {'file': str(binding.relative_to(ROOT)), 'sha256': sha(binding)},
        'inventory': data['inventory'], 'live_Source90_site_and_canonical_Lean_are_read_only_symlinks': True,
    }
output = BASE/('isolated-ledger-audit-'+args.tag+'.json')
assert not output.exists()
with output.open('x') as out:
    out.write(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
output.chmod(0o444)
summary = {k:report[k] for k in ['integrity_status', 'mathematical_coverage_complete', 'counts', 'errors']}
print(json.dumps(summary), flush=True)
passed = report['integrity_status'] == 'passed' and report['errors'] == [] and report['mathematical_coverage_complete'] is False
raise SystemExit(0 if passed else 1)
