from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, shutil, sys, time

ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=Path('/tmp/applied-finish31-conditional387-qualifiers-unnumbered-v1')
PREVIOUS=BASE/'conditional387-two-exact-qualifiers-unnumbered-author-proposal31-v1.json'
start=datetime.now(timezone.utc).isoformat()
tick=time.monotonic()
d=json.loads(PREVIOUS.read_bytes())
assert hashlib.sha256(PREVIOUS.read_bytes()).hexdigest()=='afc9c9c4b4d1787617bff73b97e5e7506e26ccb52f4c7389090eb1a170034ec4'
raw=Path(d['source']).read_bytes()
assert hashlib.sha256(raw).hexdigest()==d['source_sha256']
replacements=[dict(x) for x in d['exact_replacements']]
assert replacements[0]['after'].count('not determined by the law')==1
replacements[0]['after']=replacements[0]['after'].replace('not determined by the law','not determined by the joint law')
text=raw.decode()
for r in replacements:
    assert text.count(r['before'])==1
    text=text.replace(r['before'],r['after'])
candidate=BASE/'primer-probability-conditional387-qualifiers-proposed-unnumbered-v2.html'
with candidate.open('x') as f:f.write(text)
assert text.count('\n')==raw.decode().count('\n')
clone=BASE/'full29-prospective-v2-root'
(clone/'SafeLearning').mkdir(parents=True)
for p in (ROOT/'SafeLearning').glob('*.html'):
    shutil.copyfile(p,clone/'SafeLearning'/p.name)
shutil.copyfile(candidate,clone/'SafeLearning/primer-probability.html')
sys.path.insert(0,str(ROOT/'book'))
import inventory_claims
inventory_claims.ROOT=clone
inventory_claims.OUT=BASE/'full29-prospective-v2-inventory'
inventory_claims.inventory()
old=json.loads((ROOT/'book/coverage/inventory-after-correction81.json').read_bytes())
inventory=inventory_claims.OUT/'inventory.json'
new=json.loads(inventory.read_bytes())
changes={}
for field in ['exercises','material_source_units']:
    a={r['key']:r for r in old[field]};b={r['key']:r for r in new[field]}
    assert a.keys()==b.keys()
    changes[field]=[k for k in a if a[k]['text_sha256']!=b[k]['text_sha256']]
    for k in a:
        omit=['source_text','text_sha256','source_sha256']
        assert {q:v for q,v in a[k].items() if q not in omit}=={q:v for q,v in b[k].items() if q not in omit},k
assert changes=={'exercises':[],'material_source_units':['primer-probability.html::node-387']}
d.update({'status':'prepared_TMP_only_conditional387_two_exact_qualifiers_v2_with_joint_law_wording_requires_independent_review',
          'candidate':str(candidate),'candidate_sha256':hashlib.sha256(candidate.read_bytes()).hexdigest(),
          'exact_replacements':replacements,'full_prospective_inventory':str(inventory),
          'full_prospective_inventory_sha256':hashlib.sha256(inventory.read_bytes()).hexdigest(),
          'exact_full29_fresh_parser_changed_keys':changes,
          'entire_prospective387':next(r for r in new['material_source_units'] if r['key']=='primer-probability.html::node-387'),
          'previous_original_v1':{'file':str(PREVIOUS),'sha256':hashlib.sha256(PREVIOUS.read_bytes()).hexdigest()},
          'actual_preparation_execution':{'command':['python3',str(Path(__file__))],
            'actual_helper':str(Path(__file__)),'actual_helper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
            'elapsed_seconds':time.monotonic()-tick,'actual_exit_code':0},
          'current_source_and_all_other_page_literals_mutated':False})
p=BASE/'conditional387-two-exact-qualifiers-unnumbered-author-proposal31-v2.json'
with p.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'request':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                  'candidate_sha256':d['candidate_sha256'],'changed_keys':changes}))
