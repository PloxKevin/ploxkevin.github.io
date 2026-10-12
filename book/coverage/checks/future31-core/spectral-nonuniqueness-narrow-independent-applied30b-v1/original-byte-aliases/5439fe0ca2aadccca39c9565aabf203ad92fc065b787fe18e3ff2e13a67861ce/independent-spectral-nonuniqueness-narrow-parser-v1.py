from pathlib import Path
import json,hashlib,sys,importlib.util,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');P=Path('/tmp/applied31b-spectral11-reviews-v1')
REQUEST=Path('/tmp/foundations-spectral11-source80-offline-review31-v1/foundations-spectral-nonuniqueness-source80-offline-one-phrase-full29-narrow-review-request31-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert sha(p)==r['sha256'],str(p)
 if 'bytes'in r:assert p.stat().st_size==r['bytes'],str(p)
 return p
assert sha(REQUEST)=='668ad62aa18e5973182bc0fbba7dcd109cfab359fe8563e49759ec1d21282363'
D=json.loads(REQUEST.read_text());C=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
assert sha(C)=='73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
ctx=json.loads(C.read_text());guards={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():return {n:h for n,h in guards.items() if sha(ROOT/n)!=h}
assert not guard()
for n,h in D['all_physical_original_inputs_sha256'].items():assert sha(Path(n))==h,n
for r in D['all_original_byte_aliases'].values():ref(r)
current=ref(D['source']).read_text();proposed=ref(D['prospective_source']).read_text()
sub=D['exact_literal_substitutions'];assert len(sub)==1
assert current.count(sub[0]['before'])==proposed.count(sub[0]['after'])==1
assert current.replace(sub[0]['before'],sub[0]['after'])==proposed
assert proposed.replace(sub[0]['after'],sub[0]['before'])==current
assert sha(ROOT/'SafeLearning/primer-linalg.html')==D['source']['sha256']
sys.dont_write_bytecode=True;sys.path.insert(0,str(ROOT/'book'))
from validate import Document
cd=Document(current);pd=Document(proposed)
assert [(n.tag,n.attrs,n.line)for n in cd.nodes]==[(n.tag,n.attrs,n.line)for n in pd.nodes]
spec=importlib.util.spec_from_file_location('independent_spectral_parser',ROOT/'book/inventory_claims.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
trial=Path(tempfile.mkdtemp(prefix='applied31b-spectral-narrow-parser-'));(trial/'SafeLearning').mkdir()
for path in sorted((ROOT/'SafeLearning').glob('*.html')):
 dest=trial/'SafeLearning'/path.name
 if path.name=='primer-linalg.html':dest.write_bytes(ref(D['prospective_source']).read_bytes())
 else:dest.symlink_to(path)
m.ROOT=trial;m.OUT=trial/'book/coverage'
assert m.ROOT!=ROOT and m.OUT!=ROOT/'book/coverage' and str(m.ROOT).startswith('/tmp/') and str(m.OUT).startswith('/tmp/')
m.inventory()
fresh=json.loads((m.OUT/'inventory.json').read_text());old=json.loads(ref(D['current_inventory']).read_text())
assert fresh['counts']==old['counts'] and len(fresh['material_source_units'])==12774 and len(fresh['exercises'])==556
for kind in ['exercises','material_source_units']:
 a={r['key']:r for r in old[kind]};b={r['key']:r for r in fresh[kind]};assert a.keys()==b.keys()
 changed=[]
 for key,row in a.items():
  rr=b[key];assert {k:v for k,v in row.items()if k not in ['source_sha256','source_text','text_sha256']}=={k:v for k,v in rr.items()if k not in ['source_sha256','source_text','text_sha256']},key
  if row['source']=='SafeLearning/primer-linalg.html':assert rr['source_sha256']==D['prospective_source']['sha256']
  else:assert row['source_sha256']==rr['source_sha256']
  if row['source_text']!=rr['source_text']:changed.append(key)
  else:assert row['text_sha256']==rr['text_sha256']
 assert changed==(['primer-linalg.html::node-421']if kind=='material_source_units'else[]),changed
assert [k for k in old['source_sha256']if old['source_sha256'][k]!=fresh['source_sha256'][k]]==['SafeLearning/primer-linalg.html']
key='primer-linalg.html::node-421';pair=D['entire_current_and_prospective_literal_records'][key]
assert next(r for r in fresh['material_source_units']if r['key']==key)==pair['entire_prospective']
assert next(r for r in old['material_source_units']if r['key']==key)==pair['entire_current']
assert ''.join(current.splitlines(keepends=True)[425:559])==D['full_current_Section3_lines426_559']
assert ''.join(proposed.splitlines(keepends=True)[425:559])==D['full_prospective_Section3_lines426_559']
assert not guard()
result={'status':'passed_independent_spectral_nonuniqueness_full29_narrow_parser','parser_ROOT':str(m.ROOT),'parser_OUT':str(m.OUT),'actual_fresh_inventory':str(m.OUT/'inventory.json'),'actual_fresh_inventory_sha256':sha(m.OUT/'inventory.json'),'changed_material_keys':[key],'all556_exercise_texts_unchanged':True,'all12774_keys_unchanged':True,'all28_other_pages_byte_exact':True,'all_node_tags_attrs_lines_unchanged':True,'exact_forward_and_inverse':True,'protection_errors':[],'current421_whole_approved':False,'source_application_performed':False,'ordinal_reserved':False,'compiler_or_producer_invoked':False}
(P/'narrow-parser-findings-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
