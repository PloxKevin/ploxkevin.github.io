"""Preserve reviewed trials and run two real, uniquely named compiler checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[3]
TMP = Path('/tmp')
BASE = ROOT / 'book/coverage/checks/future24-core/barrier-intro'
NAME = 'CompleteBarrierIntroMaterial24'
SOURCE = TMP / 'root-barrier-intro-material24-trial2.lean'
DIGEST = '600e2c860622dcb5f132453deb00a4025d5ec2fd27033cfd42e412fe72604c89'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def rel(p): return p.relative_to(ROOT).as_posix()
def exact_copy(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists(): assert sha(target) == sha(source), str(target)
    else:
        with target.open('xb') as f: f.write(source.read_bytes())
    assert sha(target) == sha(source)

selection = read(ROOT / 'reports/full-coverage/checkpoint-23-selection.json')
manifest = read(ROOT / 'reports/full-coverage/checkpoint-23-manifest.json')
assert len(selection['proof_files']) == 1131
protected = {n:r['sha256'] for n,r in selection['proof_files'].items()}
owners = {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules']}
owners.add('book/coverage/applied-promotions.json')
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items()
                  if n.startswith('SafeLearning/') or n in owners or n == 'book/coverage/inventory.json'})
def guard():
    for n,h in protected.items(): assert sha(ROOT/n) == h,n

guard()
assert sha(SOURCE) == DIGEST
peer = TMP / 'root-barrier-intro24-three-literals-independent-applied-review-v1.json'
assert sha(peer) == 'ad7ed9ea70ee14d4871ff861c2e5fa3b5868e661f88d9cd0025984735a2a225f'
canonical = ROOT / 'verification/lean/SafeLearning' / (NAME+'.lean')
assert not canonical.exists()
for suffix in ['-standalone.json','.log','-named-build.json','-named-build.log']:
    assert not (ROOT/'book/coverage/checks'/(NAME+suffix)).exists()
originals = {p for pattern in ['root-barrier-intro*','root_barrier_intro24*',
            'CompleteBarrierIntroMaterial24*','root-core24-seven*']
            for p in TMP.glob(pattern) if p.is_file()}
assert SOURCE in originals and peer in originals and len(originals) > 10
archived = {}
for p in sorted(originals):
    target = BASE/'original-tmp'/p.name
    exact_copy(p,target)
    archived[str(p)] = {'file':rel(target),'sha256':sha(target)}
exact_copy(SOURCE,canonical)
snapshot = BASE/(NAME+'-original-source-v1.lean')
exact_copy(SOURCE,snapshot)
assert len(re.findall(r'^theorem ',canonical.read_text(),re.M)) == 4
for helper in ['book/coverage/check_core_standalone.py','book/coverage/check_core_named_build.py']:
    result = subprocess.run(['python3',helper,NAME],cwd=ROOT)
    guard()
    assert sha(canonical) == DIGEST
    if result.returncode: raise SystemExit(result.returncode)
pairs = []
for suffix in ['-standalone.json','-named-build.json']:
    p = ROOT/'book/coverage/checks'/(NAME+suffix)
    d = read(p)
    assert d['exit_code'] == 0 and d['source_sha256_before'] == d['source_sha256_after'] == DIGEST
    assert sha(ROOT/d['log']) == d['log_sha256']
    pairs.append({'file':rel(p),'sha256':sha(p),'log':{'file':d['log'],'sha256':d['log_sha256']},'actual_exit_code':0})
out = BASE/'root-barrier-intro24-canonical-readiness-v1.json'
assert not out.exists()
out.write_text(json.dumps({'status':'passed_actual_canonical_pair_unselected_future24',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'source':{'file':rel(canonical),'sha256':DIGEST},
    'source_snapshot':{'file':rel(snapshot),'sha256':DIGEST},
    'public_theorem_count':4,'actual_canonical_pair':pairs,
    'original_TMP_byte_copies':archived,'protected_selected23_source_count':1131,
    'scope':'Exact original trial, failed compilation, mathematical review and execution time bytes retained. These are real compiler checks, with no inferred kernel replay, selection, whole-ledger promotion or complete coverage.',
    'coverage_complete':False},indent=2)+'\n')
guard()
print(json.dumps({'status':'passed','public_theorems':4,'archived_originals':len(archived),'readiness':rel(out)}))
