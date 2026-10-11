"""Run only two NEW, independently reviewed Foundation26 canonical proof pairs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'book/coverage/checks/foundations-future26/metric-isometry'
SELF = Path(__file__).relative_to(ROOT).as_posix()
def path(n): return Path(n) if Path(n).is_absolute() else ROOT / n
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n): return json.loads(path(n).read_text())
def ref(n):
    p = path(n)
    return {'file': p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p)}
def write(p, value):
    assert not p.exists()
    with p.open('x') as f: json.dump(value, f, indent=2); f.write('\n')

assert not BASE.exists(); BASE.mkdir(parents=True)
selection_name = 'reports/full-coverage/checkpoint-25-selection.json'
selection = read(selection_name); assert selection['proof_file_count'] == 1156
protected = {n:r['sha256'] for n,r in selection['proof_files'].items()}
binding = read('book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json')
assets = binding['exact_current52_safelearning_assets_sha256']; assert len(assets) == 31
protected.update(assets)
owner_hashes = {
 'book/coverage/core.json':'4e96c717055187cfc24e9e60a19a7d183499336570d99fbf9954ff199ff49572',
 'book/coverage/foundations.json':'9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada',
 'book/coverage/applied.json':'0a4ee34e6e3b55391a596c90ea92591eaa6bb3f6a103016c1c01635d225e0a9b',
 'book/coverage/modules.json':'9f3736a26e2c729b138fd4cc10b3376d67d475b1e759e4fe56fb393c27e08a63',
 'book/coverage/applied-promotions.json':'2b70fcbd1536285b8c51a62de7f99d2fae4368ff06d0aeed61b3d97dfccc193a'}
protected.update(owner_hashes)
for n in ['book/coverage/inventory.json','book/coverage/inventory-after-correction52.json']:
    protected[n] = '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
protected[selection_name] = sha(selection_name)
def guard():
    for n,h in protected.items(): assert sha(n) == h,n
guard()
specs = [
 {'name':'CompleteFoundationsIsometricEmbeddings26', 'original_source':'/tmp/CompleteFoundationsIsometricEmbeddings26.lean',
  'source_sha256':'9fa11c77a8888ed6a9a7bfcee461187ed529b91af84e6ef2cb39b27f80bff87e',
  'peer':'/tmp/foundations-isometric-embeddings26-independent-modules-full-literal-review-v1.json',
  'peer_sha256':'02c24f133ace002d7f6d79c2cd245100c74d7bbf61f4bc9412d27671f5a83fa5',
  'keys':['primer-linalg.html::node-209'], 'theorem_count':7},
 {'name':'CompleteFoundationsMetricAndSetDistance26', 'original_source':'/tmp/foundations-metric-set-distance26-trial2.lean',
  'source_sha256':'384f240ed945930c1173f90b3c92c8c9e5cd366f01786291aa356c0bb09ddc29',
  'peer':'/tmp/foundations-metric-set-distance26-independent-modules-two-full-literal-review-v1.json',
  'peer_sha256':'10dc737deff1ae0763a10177553cf8a5d1a26a18215f00a8bf140905875204b7',
  'keys':['primer-linalg.html::node-197','primer-linalg.html::node-199'], 'theorem_count':8}]
originals = {str(Path('/tmp/foundations26-isometry-metric-independent-modules-actual-v1.json'))}
def collect(x):
    if isinstance(x,dict):
        for v in x.values(): collect(v)
    elif isinstance(x,list):
        for v in x: collect(v)
    elif isinstance(x,str) and x.startswith('/tmp/') and Path(x).is_file(): originals.add(x)
sys.path.insert(0, str(ROOT / 'book/coverage')); from lean_names import declarations
rows = []
for spec in specs:
    assert sha(spec['original_source']) == spec['source_sha256']
    assert sha(spec['peer']) == spec['peer_sha256']
    peer = read(spec['peer']); assert 'passed' in peer['status'] and peer['errors'] == [] and peer['missing_clauses'] == []
    assert peer['whole_literal_keys'] == spec['keys']
    request = read(peer['original_request']['file']); collect(peer); collect(request); originals.add(spec['peer']); originals.add(spec['original_source'])
    assert request['full_source_body'] == path(spec['original_source']).read_text()
    source = 'verification/lean/SafeLearning/' + spec['name'] + '.lean'
    assert source not in protected and not path(source).exists()
    with path(source).open('xb') as f: f.write(path(spec['original_source']).read_bytes())
    assert sha(source) == spec['source_sha256']
    snapshot = BASE / (spec['name'] + '-source-v1.lean')
    with snapshot.open('xb') as f: f.write(path(source).read_bytes())
    ds = declarations(path(source).read_text()); names = [d['name'] for d in ds if d['kind'] in ['theorem','lemma']]
    assert len(names) == spec['theorem_count']
    rows.append({'source':ref(source),'source_snapshot':ref(snapshot),'original_source':ref(spec['original_source']),
       'original_semantic_peer':ref(spec['peer']),'entire_original_semantic_body_and_time':peer,
       'whole_literal_keys':spec['keys'],'public_theorems':names})
actual_peer_record = read('/tmp/foundations26-isometry-metric-independent-modules-actual-v1.json'); collect(actual_peer_record)
alias_dir = BASE / 'original-tmp'; alias_dir.mkdir(); aliases = {}
for original in sorted(originals):
    src = Path(original); dst = alias_dir / src.name
    if dst.exists(): assert dst.read_bytes() == src.read_bytes()
    else:
        with dst.open('xb') as f: f.write(src.read_bytes())
    assert sha(dst) == sha(src); aliases[original] = ref(dst)
preparation = {'status':'prepared_exact_original_three_whole_literals_and_two_immutable_sources_for_new_canonical_pairs',
 'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(SELF),'proof_sources':rows,
 'canonical_original_byte_aliases':aliases,'protected_current_inputs_sha256':protected,'coverage_complete':False,
 'scope':'New unselected Foundation26 files and exact original TMP history copies only. Original semantic body/time/decisions preserved; no live owner, HTML, inventory or selected25 change.'}
prep_path = BASE / 'two-source15-canonical-source-and-original-history-preparation-v1.json'; write(prep_path,preparation)
records = []
for row in rows:
    src = row['source']['file']; digest = row['source']['sha256']; module = src.removeprefix('verification/lean/').removesuffix('.lean').replace('/','.')
    pairs = []
    for kind, command in [('standalone',['lake','env','lean',src.removeprefix('verification/lean/')]),('named-build',['lake','build',module])]:
        guard(); assert sha(src) == digest
        stem = 'book/coverage/checks/' + Path(src).stem + '-' + kind + '-v1'
        record_name = stem + '.json'; log_name = stem + '.log'
        assert not path(record_name).exists() and not path(log_name).exists()
        start = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
        with path(log_name).open('xb') as log: result = subprocess.run(command,cwd=ROOT/'verification/lean',stdout=log,stderr=subprocess.STDOUT)
        errors = []
        try: guard(); assert sha(src) == digest
        except Exception as e: errors.append(str(e))
        record = {'status':'passed' if result.returncode == 0 and not errors else 'failed',
          'source':src,'source_sha256_before':digest,'source_sha256_after':sha(src),'source_unchanged':sha(src)==digest,
          'exit_code':result.returncode,'command':command,'actual_workdir':str(ROOT/'verification/lean'),
          'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
          'log':log_name,'log_sha256':sha(log_name),'protection_errors':errors,
          'scope':'Genuine new canonical ' + kind + ' execution only; formal aggregate/kernel/axiom audit and live mapping remain separate.'}
        write(path(record_name),record); records.append(ref(record_name)); pairs.append({'record':ref(record_name)})
        assert type(result.returncode) is int and result.returncode == 0 and not errors
    row['actual_canonical_pair'] = pairs
guard()
readiness = {'status':'passed_genuine_two_source15_canonical_standalone_and_named_pairs_unselected_future26',
 'completed_at_utc':datetime.now(timezone.utc).isoformat(),'canonical_preparation':ref(prep_path),'proof_sources':rows,
 'public_theorem_count':15,'actual_canonical_execution_count':4,'protected_selected25_source_count':1156,
 'current_source_asset_count':31,'installed25_owner_count':5,'coverage_complete':False,
 'scope':'Four genuine new actual canonical compiler executions. Original complete three literal decisions, bodies, review times, actual failed/pass trial history and warnings remain exact. No aggregate26, installation, Pages or fixed25 amendment.'}
ready_path = BASE / 'two-source15-canonical-paired-readiness-v1.json'; write(ready_path,readiness)
print(json.dumps({'status':'passed','readiness':ref(ready_path),'proof_sources':2,'public_theorems':15,'actual_pairs':4,'named_slot_released':True}))
