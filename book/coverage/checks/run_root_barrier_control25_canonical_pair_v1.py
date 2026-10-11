"""Preserve reviewed trials and run two real, uniquely named compiler checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parents[3]
TMP = Path('/tmp')
BASE = ROOT / 'book/coverage/checks/future25-core/barrier-control'
NAME = 'CompleteBarrierControlMaterial25'
SOURCE = TMP / 'root-barrier-control-material25-trial2.lean'
DIGEST = 'b76e4f44209d8a75da1d3fd62aae6402ccf0e6d78e2a5c3e7e97507c71e517a8'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def rel(p): return p.relative_to(ROOT).as_posix()
def exact_copy(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists(): assert sha(target) == sha(source), str(target)
    else:
        with target.open('xb') as f: f.write(source.read_bytes())
    assert sha(target) == sha(source)

selection = read(ROOT / 'reports/full-coverage/checkpoint-24-selection.json')
manifest = read(ROOT / 'reports/full-coverage/checkpoint-24-manifest.json')
assert len(selection['proof_files']) == 1144
protected = {n:r['sha256'] for n,r in selection['proof_files'].items()}
owners = {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules']}
owners.add('book/coverage/applied-promotions.json')
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items()
                  if n.startswith('SafeLearning/') or n in owners or n == 'book/coverage/inventory.json'})
def guard():
    for n,h in protected.items(): assert sha(ROOT/n) == h,n

assert (ROOT/'reports/full-coverage/cache-checkpoint24-execution-v1.json').exists()
assert read(ROOT/'reports/full-coverage/cache-checkpoint24-execution-v1.json')['actual_exit_code'] == 0
guard()
assert sha(SOURCE) == DIGEST
peer = TMP / 'root-barrier-control-material25-two-literals-independent-applied-review-v1.json'
assert sha(peer) == '76e1758db4acca9f756742e630a66a69f7cd604a7380e4e6370e183f583162a5'
canonical = ROOT / 'verification/lean/SafeLearning' / (NAME+'.lean')
assert not canonical.exists()
for suffix in ['-standalone.json','.log','-named-build.json','-named-build.log']:
    assert not (ROOT/'book/coverage/checks'/(NAME+suffix)).exists()
originals = {p for pattern in ['root-barrier-control-material25*','root_compile_tmp_core25*',
            'CompleteBarrierControlMaterial25*','root-core25-case-study-guidance*']
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
assert len(re.findall(r'^theorem ',canonical.read_text(),re.M)) == 7
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
out = BASE/'root-barrier-control25-canonical-readiness-v1.json'
assert not out.exists()
out.write_text(json.dumps({'status':'passed_actual_canonical_pair_unselected_future25',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'source':{'file':rel(canonical),'sha256':DIGEST},
    'source_snapshot':{'file':rel(snapshot),'sha256':DIGEST},
    'public_theorem_count':7,'actual_canonical_pair':pairs,
    'original_TMP_byte_copies':archived,'protected_selected24_source_count':1144,
    'scope':'Exact original trial, failed compilation, mathematical review and execution time bytes retained. These are real compiler checks, with no inferred kernel replay, selection, whole-ledger promotion or complete coverage.',
    'coverage_complete':False},indent=2)+'\n')
guard()
print(json.dumps({'status':'passed','public_theorems':7,'archived_originals':len(archived),'readiness':rel(out)}))
