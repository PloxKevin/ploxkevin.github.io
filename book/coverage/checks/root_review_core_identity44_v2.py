"""Independently check exact pointer-only core source44 identity versions."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,collections
R=Path(__file__).resolve().parents[3];H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();L=lambda n:json.loads((R/n).read_text())
name='book/coverage/checks/core-source44-unchanged-review-identity-manifest-v2.json';m=L(name);assert H(name)=='8bb22f58ad16cc386033149e888bb93d1d8555d0e9eeb164b0a6e68e670eaf90'
I=L(m['immutable_inventory_after']);oldI=L(m['immutable_inventory_before'])
assert H(m['immutable_inventory_after'])==m['immutable_inventory_after_sha256']==H('book/coverage/inventory.json')
assert H(m['immutable_inventory_before'])==m['immutable_inventory_before_sha256']
oldunits={x['key']:x for s in ['exercises','material_source_units'] for x in oldI[s]};units={x['key']:x for s in ['exercises','material_source_units'] for x in I[s]};count=collections.Counter();keys=set()
def walk(v):
 if isinstance(v,list):
  for x in v:walk(x)
 elif isinstance(v,dict):
  key=v.get('source_unit_key',v.get('exercise_key'))
  if key in units:
   u=units[key]
   for field,actual in [('unit_text_sha256','text_sha256'),('exercise_text_sha256','text_sha256'),('source_text','source_text'),('exercise_text','source_text')]:
    if field in v and ((field.startswith('unit') or field=='source_text')==('source_unit_key' in v)):assert v[field]==u[actual],(key,field)
   if 'source_sha256' in v and isinstance(v['source_sha256'],str):assert v['source_sha256']==u['source_sha256'],key
   keys.add(key)
  for f in ['proof_source_sha256','definition_dependency_source_sha256']:
   if isinstance(v.get(f),dict):
    for n,h in v[f].items():assert H(n)==h,n
  for x in v.values():walk(x)
for row in m['records']:
 assert H(row['original_review'])==row['original_review_sha256'] and H(row['rebased_review'])==row['rebased_review_sha256']
 a=L(row['original_review']);b=L(row['rebased_review']);normalized=copy.deepcopy(b);provenance=normalized.pop(row['provenance_field']);assert provenance
 for delta in reversed(row['changed_current_identity_fields']):
  path=delta['path'];v=normalized
  for k in path[:-1]:v=v[k]
  k=path[-1];assert v[k]==delta['after']
  shape=tuple(x for x in path if not isinstance(x,int));count[shape]+=1
  assert shape in {('records','source_sha256'),('material_units','source_sha256'),('inventory_sha256',),('inventory',),('source_sha256','SafeLearning/policy-optimization.html'),('source_sha256',),('candidate_manifest',),('candidate_manifest_sha256',),('candidate_source',),('candidate_sha256',)},shape
  if 'source_sha256' in shape:assert delta['after'] in I['source_sha256'].values()
  if shape==('inventory_sha256',):assert delta['after']==m['immutable_inventory_after_sha256']
  if shape==('inventory',):assert delta['after']==m['immutable_inventory_after']
  if shape==('candidate_source',):assert (R/delta['after']).is_file()
  if shape==('candidate_sha256',):assert delta['after']==H(b['candidate_source'])
  if shape==('candidate_manifest',):assert (R/delta['after']).is_file()
  if shape==('candidate_manifest_sha256',):assert delta['after']==H(b['candidate_manifest'])
  v[k]=delta['before']
 assert normalized==a and b.get('reviewed_at_utc')==a.get('reviewed_at_utc')
 walk(b)
 for k in row['unchanged_literal_keys']:
  assert k in units and k in oldunits
  for field in ['source_text','text_sha256','line','source_unit_key','id','exercise_key']:
   if field in oldunits[k]:assert units[k][field]==oldunits[k][field],(k,field)
  keys.add(k)
for p,h in I['source_sha256'].items():assert H(p)==h
assert H(m['immutable_source33_core_ledger'])==m['immutable_source33_core_ledger_sha256']
assert len(m['records'])==42 and len(m['review_path_aliases'])==39 and len(m['candidate_path_aliases'])==3
c=L('reports/full-coverage/checkpoint-18-manifest.json');protected={}
for n,r in c['proof_files'].items():protected[n]=r['sha256'];protected.update(r['evidence_sha256'])
for n,h in protected.items():assert H(n)==h
for n,h in c['frozen_inputs_sha256'].items():assert H(c['snapshot']+'/'+n)==h
out=dict(schema_version=1,status='independent_exact_inventory_identity_rebase_confirmation_passed',reviewer='/root',reviewed_at_utc=datetime.now(timezone.utc).isoformat(),actual_command=['python3','book/coverage/checks/root_review_core_identity44_v2.py'],actual_exit_code=0,rebase_manifest=name,rebase_manifest_sha256=H(name),immutable_inventory_after=m['immutable_inventory_after'],immutable_inventory_after_sha256=m['immutable_inventory_after_sha256'],unchanged_identity_versions=42,review_versions=39,candidate_versions=3,literal_keys_checked=len(keys),normalized_all_original_review_bodies_and_times_exact=True,allowed_changed_field_shapes={str(k):v for k,v in count.items()},helper_source_sha256={n:H(n) for n in ['book/coverage/core_identity44.py','book/coverage/core_path_reviews.py','book/coverage/core_labels19.py','book/coverage/build_core.py']},protected_paths=len(protected),frozen18_inputs=len(c['frozen_inputs_sha256']),limits=['Unchanged literals only; no fresh semantic approval or whole promotion follows from page/inventory identity updates.','Changed9.2/9.4/9.5 use their separate fresh literal correspondence reviews; historical parent mathematics must still pass the runtime guard.'])
p=R/'book/coverage/checks/core-source44-unchanged-review-identity-independent-root-confirmation-v2.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'sha256':H(str(p.relative_to(R))),'literal_keys_checked':len(keys)}))
