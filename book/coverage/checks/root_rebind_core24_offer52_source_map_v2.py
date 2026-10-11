"""Repair the isolated Core offer's unrelated NN source map, preserving v1."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OLD = 'book/coverage/checks/future24-core/source52/core-audit24-candidate-source52-material-additions-v1.json'
NEW = OLD.replace('-v1.json', '-v2.json')
def sha(name): return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
def read(name): return json.loads((ROOT/name).read_text())
def ref(name): return {'file': name, 'sha256': sha(name)}
old = read(OLD)
name = 'SafeLearning/nn-in-the-loop.html'
assert old['source_sha256'][name] == '413846b5ffc2a5fd70f74fb6f4a24e96b7983b6a745f50340c9d2d25c75d7049'
assert sha(name) == '1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
assert read('reports/full-coverage/source52-apply-execution-v1.json')['actual_exit_code'] == 0
candidate = old['candidate_ledger']
assert sha(candidate['file']) == candidate['sha256']
assert name not in read(candidate['file'])['source_sha256']
guards = {n:sha(n) for n in ['book/coverage/core.json', 'book/coverage/foundations.json', 'book/coverage/applied.json', 'book/coverage/modules.json', 'book/coverage/applied-promotions.json']}
new = copy.deepcopy(old)
new['source_sha256'][name] = sha(name)
new['unrelated_source52_offer_map_binding'] = {
    'status':'passed_only_unrelated_NN_offer_source_map_updated_to_actual_source52',
    'checked_at_utc':datetime.now(timezone.utc).isoformat(),
    'helper':ref(str(Path(__file__).relative_to(ROOT))),
    'original_source52_offer_v1':ref(OLD),
    'entire_original_source52_offer_v1_body_and_time':old,
    'original_source_sha256':old['source_sha256'],
    'actual_source52_apply':ref('reports/full-coverage/source52-apply-execution-v1.json'),
    'candidate_and_owned_literal_identity_unchanged':True,
    'scope':'Only the top-level all-page offer map changes for NN. Original source51 semantic reviews, source52 v1 body/time, candidate ledger and held live owners remain exact.'}
inverse = copy.deepcopy(new)
inverse.pop('unrelated_source52_offer_map_binding')
inverse['source_sha256'] = old['source_sha256']
assert inverse == old
assert all(sha(n)==s for n,s in new['source_sha256'].items())
assert not (ROOT/NEW).exists()
with (ROOT/NEW).open('x') as f: f.write(json.dumps(new,indent=2)+'\n')
assert all(sha(n)==s for n,s in guards.items())
assert sha(candidate['file']) == candidate['sha256']
print(json.dumps({'status':'passed_isolated_map_only_update','offer':ref(NEW),'candidate':candidate}))
