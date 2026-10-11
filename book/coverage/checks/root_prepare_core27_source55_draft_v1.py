"""Prepare a reversible current55 Core candidate with eleven reviewed components.

This is isolated preparation. Canonical sources and paired executions remain
pending; no installed owner, publication, or aggregate verification is changed.
"""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
from copy import deepcopy
import hashlib, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/core27-current55-eleven-component-draft-v1')
OLD = 'book/coverage/core.json'
OLD_SHA = '1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38'
INV = 'book/coverage/inventory-after-correction55.json'
INV_SHA = '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
SOURCE = Path('/tmp/CompleteCoreMPCFirstSuccessor27-draft-v1.lean')
SOURCE_SHA = '09fc59984a9e53f86e8ddfa82b2bee79f163aeffd5dc173b88eb6d8fc9c8000c'
CANONICAL = 'verification/lean/SafeLearning/CompleteCoreMPCFirstSuccessor27.lean'
PEERS = {
 'bootstrap3': ('/tmp/root-mpc-local-bootstrap27-independent-modules-full-component-review-v1.json','bee0502eede172581a4ebe30a07b8e3c3d21940cf56516f12ac991f1344c5c9e'),
 'norm5': ('/tmp/root-mpc-normbridge5-source54-proposal3-independent-modules-full-component-review27-v1.json','0f5d29c601d50295c4c17879dc7af4d0cf141d554ee38683fdf5b689b5399d30'),
 'norm2': ('/tmp/root-mpc-normbridge-two-new-components-independent-foundations-review27-v1.json','4d14116582983c67038608af8b12fd1b142c85d39ff27fea103e03248331a9c7'),
 'successor1': ('/tmp/root-mpc-first-successor11-independent-applied-full-component-review27-v1.json','d72fbd3ccc7f59bc42cd2f554f097a896c1a505154c3a6e9221502c50a90a2d4'),
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file':str(p),'sha256':sha(p)}
def write(p,d):
 with p.open('x') as f: f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
assert not OUT.exists()
assert sha(ROOT/OLD)==OLD_SHA and sha(ROOT/INV)==INV_SHA
assert sha(ROOT/'book/coverage/inventory.json')==INV_SHA
assert sha(SOURCE)==SOURCE_SHA and not (ROOT/CANONICAL).exists()
old=json.loads((ROOT/OLD).read_bytes()); inv=json.loads((ROOT/INV).read_bytes())
oldinv=json.loads((ROOT/'book/coverage/inventory-after-correction53.json').read_bytes())
assert old['current_inventory_sha256']==sha(ROOT/'book/coverage/inventory-after-correction53.json')
assert len(old['exercises'])==92 and len(old['proof_files'])==181
assert len(old['material_claims'])==4177
units={u['key']:u for u in inv['material_source_units']}
oldunits={u['key']:u for u in oldinv['material_source_units']}
exs={u['key']:u for u in inv['exercises']}
oldexs={u['key']:u for u in oldinv['exercises']}
data=deepcopy(old)
data['current_inventory']=INV; data['current_inventory_sha256']=INV_SHA
for name,digest in data['source_sha256'].items():
 if name.startswith('SafeLearning/'):
  assert sha(ROOT/name)==inv['source_sha256'][name]
  data['source_sha256'][name]=inv['source_sha256'][name]
changed_material=[]
for row in data['exercises']:
 key=row['inventory_key']; assert {k:v for k,v in oldexs[key].items() if k!='source_sha256'}=={k:v for k,v in exs[key].items() if k!='source_sha256'}
 assert row['source_text']==exs[key]['source_text'] and row['text_sha256']==exs[key]['text_sha256']
 row['source_sha256']=inv['source_sha256'][row['source']]
for row in data['material_claims']:
 if row.get('source') in inv['source_sha256']:
  row['source_sha256']=inv['source_sha256'][row['source']]
 keys=row['source_unit_keys']
 changed=[k for k in keys if oldunits[k]['source_text']!=units[k]['source_text']]
 if changed:
  assert len(keys)==1 and keys[0] in {'lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739'}
  assert row['status']=='pending' and not row['lean_declarations']
  assert row['source_text']==row['statement_in_prose']==oldunits[keys[0]]['source_text']
  row['source_text']=row['statement_in_prose']=units[keys[0]]['source_text']
  row['text_sha256']=units[keys[0]]['text_sha256']; changed_material.append(row['id'])
assert set(changed_material)=={'lyapunov-mpc.html::node-737::semantic-review','lyapunov-mpc.html::node-739::semantic-review'}
peers={}
for key,(name,digest) in PEERS.items():
 p=Path(name);assert sha(p)==digest
 peers[key]=json.loads(p.read_bytes()); assert peers[key]['errors']==[]
 assert peers[key]['whole_exercise_approved'] is False and peers[key]['whole_material_unit_approved'] is False
assert peers['successor1']['entire_source']==SOURCE.read_text()
components=[]
for key,rows in [('bootstrap3',peers['bootstrap3']['components']),('norm5',peers['norm5']['components']),('norm2',peers['norm2']['two_new_precise_components']),('successor1',[peers['successor1']['new_component']])]:
 for r in rows:
  assert r['missing_clauses']==[]
  decls=r.get('lean_declarations',r.get('declarations'))
  reason=r.get('per_component_reason',r.get('reason'))
  cid=r.get('component_id',r.get('id'))
  assert decls and reason and cid
  components.append({'id':'core27-mpc-precise-component-'+cid,
    'kind':'independently_reviewed_precise_mathematical_component','status':'proved',
    'statement_in_prose':cid,'lean_declarations':decls,'hypotheses':r['hypotheses'],
    'correspondence':reason,'remaining_gaps':[],
    'independent_review':{'source':PEERS[key][0],'sha256':PEERS[key][1],'original_review_time':peers[key]['reviewed_at_utc']},
    'original_review_component':deepcopy(r),
    'scope_limits':['Exact reviewed components only. Whole Assumptions1–4 robust replanning, Exercise18(d), and source units737/739/1387 remain pending.']})
assert len(components)==11
decls=[d for r in components for d in r['lean_declarations']]
assert len(decls)==len(set(decls))==11 and set(decls)==set(peers['successor1']['all_public_theorem_names'])
target=next(r for r in data['exercises'] if r['inventory_key']=='lyapunov-mpc.html::exercise-18')
assert target['status']=='partial';oldclaims=deepcopy(target['claims'])
target['claims'].extend(deepcopy(components));assert target['claims'][:len(oldclaims)]==oldclaims
for key in ['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739','lyapunov-mpc.html::node-1387']:
 assert any(key in r['source_unit_keys'] and r['status']=='pending' for r in data['material_claims'])
 u=units[key]
 for c in components:
  row=deepcopy(c);row['id']=key+'::'+row['id']
  row.update(source_unit_keys=[key],source=u['source'],source_sha256=u['source_sha256'],text_sha256=u['text_sha256'],source_text=u['source_text'])
  data['material_claims'].append(row)
data['counts']['material_claims']=len(data['material_claims'])
assert len(data['material_claims'])==4210
assert data['proof_files']==old['proof_files'] and data['generated_at_utc']==old['generated_at_utc']
assert Counter(r['status'] for r in data['exercises'])==Counter(r['status'] for r in old['exercises'])

# Store an exact field inverse plus the immutable raw original. Full previous
# bodies and review times are recoverable, without replacing them with decisions.
patches=[]
def diff(a,b,keys=[]):
 if a==b: return
 if isinstance(a,dict) and isinstance(b,dict):
  for k in sorted(set(a)|set(b)):
   if k not in a or k not in b: patches.append({'path':keys+[k],'before_present':k in a,'after_present':k in b,'before':a.get(k),'after':b.get(k)})
   else: diff(a[k],b[k],keys+[k])
 elif isinstance(a,list) and isinstance(b,list) and len(a)<=len(b):
  for i,v in enumerate(a):diff(v,b[i],keys+[i])
  if len(b)>len(a):patches.append({'path':keys,'operation':'append','original_length':len(a),'appended':b[len(a):]})
 else:patches.append({'path':keys,'before_present':True,'after_present':True,'before':a,'after':b})
diff(old,data)
restored=deepcopy(data)
for r in reversed(patches):
 d=restored
 for k in r['path'][:-1]:d=d[k]
 k=r['path'][-1]
 if r.get('operation')=='append':d[k]=d[k][:r['original_length']]
 elif r['before_present']:d[k]=r['before']
 else:del d[k]
assert restored==old
OUT.mkdir()
original=OUT/'core26-entire-original-source53-ledger.json'
with original.open('xb') as f:f.write((ROOT/OLD).read_bytes())
assert sha(original)==OLD_SHA
candidate=OUT/'core27-current55-eleven-component-candidate-draft-v1.json';write(candidate,data)
identity=OUT/'core27-source53-to55-exact-field-inverse-v1.json'
write(identity,{'status':'passed_isolated_exact_reversible_identity_and_eleven_component_mapping','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original':ref(original),'candidate':ref(candidate),'exact_field_changes':patches,'inverse_restores_entire_original_body_and_all_times':True,'changed_pending_literal_rows':changed_material,'canonical_pair_execution_count':0,'canonical_or_owner_write_claimed':False})
readiness=OUT/'core27-current55-eleven-component-readiness-draft-v1.json'
write(readiness,{'status':'isolated_current55_core_candidate_awaiting_canonical_pair_and_independent_mechanics','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(candidate),'identity':ref(identity),'entire_original_ledger':ref(original),'current_inventory':{'file':INV,'sha256':INV_SHA},'planned_canonical_source':CANONICAL,'exact_tmp_source':ref(SOURCE),'new_public_theorem_count':11,'original_full_component_peers':[{'file':n,'sha256':h,'entire_original_body_and_time':peers[k]} for k,(n,h) in PEERS.items()],'canonical_pair_execution_count':0,'eligible_for_owner_integration_or_selection':False,'all92_exercise_statuses_unchanged':True,'old181_proof_mapping_unchanged':True,'whole_exercise18_and_material737_739_1387_pending':True,'coverage_complete':False,'prepared_by':ref(Path(__file__))})
assert sha(ROOT/OLD)==OLD_SHA and sha(ROOT/INV)==INV_SHA and not (ROOT/CANONICAL).exists()
print(json.dumps({'status':'passed_isolated_preparation','candidate':ref(candidate),'identity':ref(identity),'readiness':ref(readiness),'new_precise_components':11,'new_material_component_rows':33,'canonical_execution_count':0}))
