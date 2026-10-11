from pathlib import Path
from datetime import datetime,timezone
import importlib.util,sys,tempfile,json,hashlib
root=Path('/home/oxrexkevin/SafetyBased')
out=Path('/tmp/root-source54-55-full29-parser-application-contract27-v1.json')
assert not out.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
p54=Path('/tmp/root-source54-continuity-and-domain-proposal-v3.json');p55=Path('/tmp/modules-conformal-source55-precision-proposal-v1.json')
drafts=[(54,p54,read(p54)),(55,p55,read(p55))]
old=read(root/'book/coverage/inventory.json');initial=sha(root/'book/coverage/inventory.json')
assert initial=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
parser=root/'book/inventory_claims.py';assert sha(parser)=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
sys.path.insert(0,str(root/'book'))
changed_sources={};steps=[]
for num,p,d in drafts:
 source=d['current_source53']['file'];candidate=Path(d['candidate_only']['file'])
 assert sha(root/source)==d['current_source53']['sha256'] and sha(candidate)==d['candidate_only']['sha256']
 changed_sources[source]=candidate
 with tempfile.TemporaryDirectory(prefix='root-source54-55-plan-') as td:
  isolated=Path(td);(isolated/'SafeLearning').mkdir()
  for page in (root/'SafeLearning').glob('*.html'):
   n=page.relative_to(root).as_posix();target=isolated/n
   if n in changed_sources:target.write_bytes(changed_sources[n].read_bytes())
   else:target.symlink_to(page)
  spec=importlib.util.spec_from_file_location('parser54_55_plan',parser);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
  m.ROOT=isolated;m.OUT=isolated/'book/coverage';m.inventory();new=read(m.OUT/'inventory.json')
 assert new['counts']==old['counts'] and len(new['source_sha256'])==29
 assert new['source_sha256']=={**old['source_sha256'],source:sha(candidate)}
 changed={}
 for field in ['exercises','material_source_units']:
  a={r['key']:r for r in old[field]};b={r['key']:r for r in new[field]};assert a.keys()==b.keys();changed[field]=[]
  for k in a:
   x=dict(a[k]);y=dict(b[k])
   if x['source']==source:
    assert y['source_sha256']==sha(candidate);x.pop('source_sha256');y.pop('source_sha256')
   if x!=y:
    assert {t:v for t,v in x.items() if t not in {'source_text','text_sha256'}}=={t:v for t,v in y.items() if t not in {'source_text','text_sha256'}}
    changed[field].append(k)
  assert changed[field]
 steps.append({'correction_id':num,'proposal':{'file':str(p),'sha256':sha(p)},'source':source,'source_sha256_before':d['current_source53']['sha256'],'candidate':d['candidate_only'],'exact_changed_text_keys':changed,'counts':new['counts']})
 old=new
assert sha(root/'book/coverage/inventory.json')==initial
result={'status':'planned_two_sequential_full29_parser_applications_no_current_source_or_inventory_write','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'before_inventory':{'file':'book/coverage/inventory.json','sha256':initial},'parser':{'file':'book/inventory_claims.py','sha256':sha(parser)},'steps':steps,'final_page_sources_sha256':old['source_sha256'],'scope':'Fresh isolated full29 parser planning only; no source/registry/owner mutation or actual application claimed. Each step changes only exact listed source text/hash fields and that page source identity, preserving all keys/counts/lines/tags and other current source units.'}
with out.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed_planning_only','contract_sha256':sha(out),'steps':steps},indent=2))
