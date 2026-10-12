"""Bind ten original approved proof bodies to a new canonical compiler plan."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/root28-current60-canonical-pair-plan-v1.json')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def checked(r):
    p = Path(r['file']); assert p.is_file() and not p.is_symlink() and sha(p) == r['sha256']; return p
def short(r): return {k:r[k] for k in ['file','sha256']}
refs = [
    {'file':'/tmp/foundations-owner28-approved21-scope-plan-v2.json','sha256':'1e58d5cce1dcd200015a67e241cab118849dc2de218e2ac3272446898df74b86'},
    {'file':'/tmp/modules-owner28-approved-scope-plan-v1.json','sha256':'e7dd4b6488bd1ec796bf9289655b1e49f4a7fcf60c85dc48e046ec3c79a3a440'},
]
assert not OUT.exists()
f,m = [json.loads(checked(r).read_bytes()) for r in refs]
assert sha(ROOT/'book/coverage/inventory.json') == '6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
module_peers = dict(zip([r['proposed_root_canonical_destination'] for r in m['proof_source_scope']], [r['whole_peer'] for r in m['exercise_scope']]))
rows = []
for original in f['proof_source_scope']+m['proof_source_scope']:
    source = checked(original['original_tmp_proof']); text = source.read_text()
    bare = re.findall(r'^(?:theorem|lemma)\s+([A-Za-z0-9_]+)',text,re.M)
    if 'public_theorem_names' in original:
        by_suffix = {n.rsplit('.',1)[1]:n for n in original['public_theorem_names']}
        assert len(by_suffix) == len(original['public_theorem_names']) == len(bare)
        assert set(by_suffix) == set(bare)
        full = [by_suffix[n] for n in bare]
        peer_ref = original['whole_peer']
    else:
        namespaces = set(re.findall(r'^namespace\s+(\S+)',text,re.M)); assert len(namespaces) == 1
        full = [next(iter(namespaces))+'.'+n for n in bare]
        peer_ref = module_peers[original['proposed_root_canonical_destination']]
    peer = json.loads(checked(peer_ref).read_bytes())
    assert peer['errors'] == []
    trial = json.loads(checked(original['original_tmp_trial']).read_bytes())
    codes = [trial[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in trial]
    assert codes and all(type(c) is int and c == 0 for c in codes)
    assert trial['source_sha256_before'] == trial['source_sha256_after'] == sha(source)
    dest = original['proposed_root_canonical_destination']; assert not (ROOT/dest).exists()
    rows.append({'canonical_source':dest,'original_tmp_source':short(original['original_tmp_proof']),
        'public_theorem_count':len(bare),'public_declarations':full,
        'original_actual_tmp_trial':short(original['original_tmp_trial']),
        'independent_whole_scope_peer':short(peer_ref),'expected_peer_status':peer['status'],
        'original_semantic_review_time_unchanged':True,'canonical_compiler_records_pending':True})
assert len(rows) == 10 and sum(r['public_theorem_count'] for r in rows) == 235
record = {'status':'exact_reviewed_current60_new_source_canonical_pair_plan_only',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':10,'public_theorem_count':235,
    'sources':rows,'original_scope_plans':refs,'current60_inventory':{'file':'book/coverage/inventory.json','sha256':sha(ROOT/'book/coverage/inventory.json')},
    'prepared_by':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'canonical_installation_or_coverage_promotion_claimed':False}
with OUT.open('x') as f: f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'plan':str(OUT),'sha256':sha(OUT),'source_count':10,'public_theorems':235}))
