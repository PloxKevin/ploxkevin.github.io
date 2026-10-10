from pathlib import Path
import hashlib
import json

sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=Path('/tmp/modules-landscape-explorer-implementation-review19-v1.json')
assert sha(old)=='4e16da3b89ff7443f9c79f2b06de5be783f01ec7ac8ab6791f082eab4d1d2168'
r=json.loads(old.read_text())
r['predecessor_preserved']={'file':str(old),'sha256':sha(old),
    'v2_reason':'Exact numerical-implementation line references corrected after direct rg verification; no source or evidence bytes changed.'}
r['cancellation_and_underflow']['source_lines']=[929,930,931,950,955,969,970,973,734,735]
for item in r['evidence_files']+r['harness_source_files']:
    assert sha(Path(item['file']))==item['sha256']
assert sha(Path(r['source_binding']['file']))==r['source_binding']['sha256']
assert sha(Path(r['source_binding']['inventory_file']))==r['source_binding']['inventory_sha256']
for item in r['implementation']['read_only_assets']:
    assert sha(Path(item['file']))==item['sha256']
r['v2_generator']={'file':str(Path(__file__)),'sha256':sha(Path(__file__))}
target=Path('/tmp/modules-landscape-explorer-implementation-review19-v2.json')
with target.open('x') as handle:
    handle.write(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'review_file':str(target),'review_sha256':sha(target),'all_source_assets_evidence_freshly_match':True}))
