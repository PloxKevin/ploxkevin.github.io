"""Synchronize the exact reviewed source59 formula into its chapter source."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[3]
FRAGMENT = ROOT/'book/chapters/lipsdp.html'
HISTORY = ROOT/'reports/full-coverage/source-history/correction59-author-fragment-sync-20261011'
RESULT = ROOT/'book/coverage/checks/future28-core/correction59-author-fragment-sync-v1.json'
READINESS = ROOT/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def new(p, data):
    assert not p.exists(); p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f: f.write(data)
def checked(r):
    p=ROOT/r['file']; assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256']; return p

assert sha(READINESS) == '209f306bc9c9b70b51a4eca063f453d546353bd9860ac3a96c6a3e4e037cc453'
readiness=json.loads(READINESS.read_bytes())
assert readiness['status']=='passed_actual10_current60_canonical_standalone_and_named_pairs_unselected_future28'
held=dict(readiness['protected_inputs_sha256'])
held[READINESS.relative_to(ROOT).as_posix()]=sha(READINESS)
for row in readiness['sources']: held[row['canonical_source']]=row['original_tmp_source']['sha256']
helper_sha=sha(Path(__file__))
def guard():
    assert sha(Path(__file__))==helper_sha
    for n,h in held.items(): assert sha(ROOT/n)==h,n
guard()
assert sha(FRAGMENT)=='be462cac4eeb1d90551afd4db8b6bb4c60d91d3ef7843d29d276901aae87b2a4'
assert not HISTORY.exists() and not RESULT.exists()
corrections=json.loads((ROOT/'book/coverage/material-corrections.json').read_bytes())['corrections']
assert len(corrections)==60
correction=next(c for c in corrections if c.get('correction_id')==59)
assert correction['source']=='SafeLearning/lipsdp.html' and len(correction['replacements'])==1
replacement=correction['replacements'][0]
assert replacement=={'before':'0.06/0.065320\\approx0.918559','after':'0.06/(2\\sqrt{4/3}\\sqrt2(0.02))\\approx0.918559'}
peer_p=checked(correction['independent_semantic_review']); peer=json.loads(peer_p.read_bytes())
assert 'passed' in peer['status'] and peer['errors']==[]
original=FRAGMENT.read_bytes(); original_text=original.decode()
assert original_text.count(replacement['before'])==1 and original_text.count(replacement['after'])==0
candidate=original_text.replace(replacement['before'],replacement['after'],1)
page=(ROOT/'SafeLearning/lipsdp.html').read_text()
blocks=re.findall(r'<!-- BOOK APPLICATION START -->\n?(.*?)\n?<!-- BOOK APPLICATION END -->',page,re.S)
assert len(blocks)==1 and blocks[0].strip()==candidate.strip()
assert candidate.replace(replacement['after'],replacement['before'],1)==original_text
guard()
copy=HISTORY/'book/chapters/lipsdp.html'; new(copy,original)
assert sha(copy)==sha(FRAGMENT)
with FRAGMENT.open('wb') as f: f.write(candidate.encode())
assert FRAGMENT.read_bytes()==candidate.encode()
guard()
report={'status':'passed_exact_reviewed_source59_author_fragment_synchronized_current60_unchanged',
        'synchronized_at_utc':datetime.now(timezone.utc).isoformat(),
        'original_author_fragment':ref(copy),'current_author_fragment':ref(FRAGMENT),
        'correction_id':59,'exact_replacement':replacement,
        'existing_independent_source59_semantic_peer':ref(peer_p),
        'current60_inventory':ref(ROOT/'book/coverage/inventory.json'),
        'all1175_selected27_and_ten_new_canonical_sources_unchanged':True,
        'all31_current60_reader_assets_and_five_installed_owner27_ledgers_unchanged':True,
        'source_correction_count':60,'new_mathematical_coverage_claimed':False,
        'helper':ref(Path(__file__))}
new(RESULT,(json.dumps(report,indent=2)+'\n').encode())
print(json.dumps({'result':ref(RESULT),'author_fragment':ref(FRAGMENT),'reader_source_and_inventory_unchanged':True}))
