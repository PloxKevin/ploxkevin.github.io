"""Prepare isolated Core23 from exact current literals and independent decisions.

Original mathematical bodies, hypotheses, declarations and review times are
retained. Changed literal metadata is explicitly rebound; fresh full decisions
alone close physical units. No live ledger or aggregate verification is written.
"""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json
from lean_names import declarations
R=Path(__file__).resolve().parents[2]
B='book/coverage/checks/future23-core'
PACKET=B+'/core23-reviewed-source51-packet-v1.json'
OUT=B+'/core23-source51-candidate-v1.json'
INTEGRITY=B+'/core23-source51-candidate-integrity-v1.json'
IDENTITY=B+'/core23-source48-to51-literal-identity-v1.json'
BASE='reports/full-coverage/checkpoint-22/book/coverage/core.json'
BASE_SHA='3e7c69fb9a0978c914df20835bed3b2aee2b742702bb07caa6d9d582a16251f7'
INV='book/coverage/inventory-after-correction51.json'
INV_SHA='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
OLD_INV='book/coverage/inventory-after-correction48.json'
sha=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
read=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':sha(n)}
now=lambda:datetime.now(timezone.utc).isoformat()
def write(n,d):
 p=R/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def checked(p):
 assert sha(p['file'])==p['sha256'],p['file'];return read(p['file'])
def atom(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def peer(p):
 d=checked(p);assert 'passed' in d['status'] and d.get('errors',[])==[];assert d.get('reviewer',d.get('reviewed_by'))!='/root';return d
assert sha(BASE)==sha('book/coverage/core.json')==BASE_SHA
assert sha(INV)==sha('book/coverage/inventory.json')==INV_SHA
assert read('reports/full-coverage/source51-apply-execution-v1.json')['actual_exit_code']==0
pkt=read(PACKET);assert pkt['baseline_ledger']==ref(BASE) and pkt['inventory']==ref(INV)
ready=checked(pkt['actual_proof_readiness']);assert ready['new_proof_source_count']==9 and ready['public_theorem_count']==88
base=read(BASE);out=copy.deepcopy(base);inv=read(INV);oldinv=read(OLD_INV)
held=ready['held22_working_owner_sha256']
def guard():
 assert sha(INV)==sha('book/coverage/inventory.json')==INV_SHA
 for n,h in held.items():assert sha(n)==h,n
 for n,h in inv['source_sha256'].items():assert sha(n)==h,n
 for n,p in read('reports/full-coverage/checkpoint-22-selection.json')['proof_files'].items():assert sha(n)==p['sha256'],n
 for n,p in ready['proof_files'].items():
  assert sha(n)==p['sha256'],n
  for e,h in p['evidence_sha256'].items():assert sha(e)==h,e
guard()
idx={k:{u['key']:u for u in inv[k]} for k in ['exercises','material_source_units']}
old={k:{u['key']:u for u in oldinv[k]} for k in idx}
scope=set(base['scope_pages']);identities={};changed={}
for kind in idx:
 assert idx[kind].keys()==old[kind].keys()
 identities[kind]=[];changed[kind]=[]
 for key,u in old[kind].items():
  if u['source'] not in scope:continue
  v=idx[kind][key]
  if {k:x for k,x in u.items() if k!='source_sha256'}=={k:x for k,x in v.items() if k!='source_sha256'}:
   identities[kind].append({'key':key,'old_entire_record_sha256':atom(u),'current_entire_record_sha256':atom(v),'old_source_sha256':u['source_sha256'],'current_source_sha256':v['source_sha256'],'text_sha256':u['text_sha256']})
  else:changed[kind].append(key)
assert set(changed['exercises'])=={'cmdp.html::exercise-21','lyapunov-mpc.html::exercise-19'}
assert set(changed['material_source_units'])=={'cmdp.html::node-1138','cmdp.html::node-1141','lyapunov-mpc.html::node-1397','lyapunov-mpc.html::node-1401','lyapunov-mpc.html::node-1403'}
monitor=peer(pkt['monitoring_review']);binding=peer(pkt['lyapunov_identity_component_review']);numeric=peer(pkt['lyapunov_whole_review'])
mc={x['original_claim_id']:x for x in monitor['historical41_material_row_compatibility']}
ec={x['original_claim_id']:x for x in monitor['historical46_exercise_claim_compatibility']}
originalexercise=next(e for e in base['exercises'] if e['inventory_key']=='cmdp.html::exercise-21')
assert len(mc)==41 and len(ec)==46 and set(ec)=={c['id'] for c in originalexercise['claims']}
for c in originalexercise['claims']:
 x=ec[c['id']];assert x['entire_original_claim']==c and x['entire_current_exercise']==idx['exercises'][originalexercise['inventory_key']]
 assert x['old_status_hypotheses_declarations_reasons_gaps_review_body_and_time_preserved'] is True
for c in base['material_claims']:
 if c['id'] in mc:
  x=mc[c['id']];assert x['entire_original_claim']==c and x['entire_current_inventory_record']==idx['material_source_units'][c['source_unit_keys'][0]]
  assert x['old_body_status_hypotheses_declarations_reason_gaps_and_time_preserved'] is True
write(IDENTITY,{'status':'exact_unchanged_core_literals_and_explicit_fresh_changed_source_bindings','prepared_at_utc':now(),'historical_inventory':ref(OLD_INV),'current_inventory':ref(INV),'unchanged_owned_literals':identities,'changed_literal_keys':changed,'fresh_monitoring_review':pkt['monitoring_review'],'fresh_lyapunov_binding':pkt['lyapunov_identity_component_review'],'scope':'Full old semantic bodies and times stay original. Page fingerprints alone do not certify changed literal correspondence.'})
identity=ref(IDENTITY)
allnames=set()
for n,p in read('reports/full-coverage/checkpoint-22-selection.json')['proof_files'].items():allnames.update(d['name'] for d in declarations((R/n).read_text()))
for n,p in ready['proof_files'].items():
 assert n not in base['proof_files'];out['proof_files'][n]=p['sha256'];allnames.update(d['name'] for d in p['declarations'])
def component(c,cid,r):
 names=c['lean_declarations'];assert names and set(names)<=allnames and c.get('missing_clauses',[])==[]
 reason=c.get('per_component_reason',c.get('reason'));assert isinstance(reason,str) and reason
 time=c.get('original_reviewed_at_utc',r.get('reviewed_at_utc',r.get('checked_at_utc')))
 return {'id':cid,'kind':'independently_reviewed_precise_source_components','status':'proved','statement_in_prose':c.get('component_id',c.get('component',reason)),'lean_declarations':names,'hypotheses':c.get('hypotheses',[]),'correspondence':reason,'remaining_gaps':[],'independent_review':{'source':r['_file'],'sha256':r['_sha256'],'original_review_time':time},'original_review_component':copy.deepcopy(c),'scope_limits':copy.deepcopy(c.get('original_scope_limits_retained',[]))}
reviews=[(monitor,pkt['monitoring_review']),(binding,pkt['lyapunov_identity_component_review']),(numeric,pkt['lyapunov_whole_review'])]
whole={};material_additions=[];exrecords={}
for i,(r,rref) in enumerate(reviews):
 r['_file']=rref['file'];r['_sha256']=rref['sha256']
 for u in r.get('material_units',[]):
  key=u['source_unit_key'];assert u['entire_inventory_record']==idx['material_source_units'][key],key
  if u.get('whole_unit_approved'):
   assert u['material_status']=='proved' and u['missing_clauses']==[] and u['lean_declarations'] and set(u['lean_declarations'])<=allnames and key not in whole
   whole[key]=(u,rref,r)
  if i==2:continue # The separate whole peer retains existing components without duplicating their rows.
  for j,c in enumerate(u.get('components',[])):
   a=component(c,f'{key}::proof23-review{i}-component{j}',r);v=idx['material_source_units'][key]
   a.update(source_unit_keys=[key],source=v['source'],source_sha256=v['source_sha256'],text_sha256=v['text_sha256'],source_text=v['source_text'],parent_remaining_gaps=copy.deepcopy(u.get('missing_clauses',[])))
   material_additions.append(a)
 er=r.get('records',[]) if i==0 else [r['exercise']] if i==1 else []
 for e in er:
  key=e['exercise_key'];assert e['entire_inventory_record']==idx['exercises'][key] and e['whole_exercise_approved'] is False
  assert key not in exrecords;exrecords[key]=(e,r)
assert set(whole)=={'cmdp.html::node-1138','lyapunov-mpc.html::node-1399','lyapunov-mpc.html::node-1401','lyapunov-mpc.html::node-1403'}
assert set(exrecords)==set(changed['exercises'])
for e in out['exercises']:
 key=e['inventory_key'];v=idx['exercises'][key]
 assert e['source_text']==old['exercises'][key]['source_text'] and e['text_sha256']==old['exercises'][key]['text_sha256']
 e['source_sha256']=v['source_sha256'];e['source51_literal_identity']=identity
 if key not in exrecords:continue
 e['original_source48_entire_exercise_row']=copy.deepcopy(next(a for a in base['exercises'] if a['inventory_key']==key))
 e['source_text']=v['source_text'];e['text_sha256']=v['text_sha256'];record,r=exrecords[key]
 gaps=record.get('remaining_gaps',record.get('missing_clauses'));assert gaps
 for c in e['claims']:
  if c['status']=='pending':
   c['original_source48_entire_pending_claim']=copy.deepcopy(c);c['statement_in_prose']=v['source_text'];c['remaining_gaps']=gaps
   c['correspondence']='Exact current51 whole exercise retained with fresh independent component review and explicit remaining parent gaps.'
 components=record.get('reviewed_components',record.get('approved_component_groups',[]));assert components
 for j,c in enumerate(components):e['claims'].append(component(c,f'{key}::proof23-component{j}',r))
 e['status']='partial';e['fresh_source51_review']={'file':r['_file'],'sha256':r['_sha256']}
changed_wholes=[]
for c in out['material_claims']:
 key=c['source_unit_keys'][0];assert len(c['source_unit_keys'])==1
 v=idx['material_source_units'][key];c['source51_literal_identity']=identity
 assert c['source_text']==old['material_source_units'][key]['source_text'] and c['text_sha256']==old['material_source_units'][key]['text_sha256']
 if key in changed['material_source_units'] or key in whole:c['original_source48_entire_material_row']=copy.deepcopy(next(a for a in base['material_claims'] if a['id']==c['id']))
 c.update(source_sha256=v['source_sha256'],source_text=v['source_text'],text_sha256=v['text_sha256'])
 if c['id'] in mc:c['fresh_source51_historical_semantic_compatibility']=pkt['monitoring_review']
 if key in whole and c['status']=='pending':
  u,rref,r=whole[key];c.update(kind='independently_reviewed_literal_material_unit',status='proved',lean_declarations=u['lean_declarations'],hypotheses=u.get('hypotheses',[]),correspondence=u['per_unit_reason'],remaining_gaps=[],independent_review={'source':rref['file'],'sha256':rref['sha256'],'original_review_time':r.get('reviewed_at_utc')},original_complete_literal_review_record=copy.deepcopy(u));changed_wholes.append(key)
assert set(changed_wholes)==set(whole) and len(changed_wholes)==4
out['material_claims'].extend(material_additions)
out['source_sha256']={n:inv['source_sha256'][n] for n in base['source_sha256']}
out['generated_at_utc']=now();out['counts']['exercise_statuses']=dict(sorted(Counter(e['status'] for e in out['exercises']).items()));out['counts']['material_claims']=len(out['material_claims'])
out['current_inventory']=INV;out['current_inventory_sha256']=INV_SHA;out['source51_core_identity_binding']=identity
out['limits'].append('Core23 adds nine exact paired sources and fresh scoped source51 reviews. Four physical units are independently complete; the monitoring and scenario parent exercises remain partial pending their general theorem gaps. Fresh aggregate23/kernel/axiom checks remain required.')
assert all(out['proof_files'][n]==h for n,h in base['proof_files'].items())
assert out['counts']['exercise_statuses']=={'complete_math':88,'partial':4}
# Reconstruct every baseline row exactly, including original pending statements.
for olde,e in zip(base['exercises'],out['exercises']):
 if olde['inventory_key'] in changed['exercises']:assert e['original_source48_entire_exercise_row']==olde
 else:
  z=copy.deepcopy(e);del z['source51_literal_identity'];z['source_sha256']=olde['source_sha256'];assert z==olde
 for oldc,newc in zip(olde['claims'],e['claims']):
  if oldc['status']!='pending':assert newc==oldc
for oldc,c in zip(base['material_claims'],out['material_claims']):
 if 'original_source48_entire_material_row' in c:assert c['original_source48_entire_material_row']==oldc
 else:
  z=copy.deepcopy(c);del z['source51_literal_identity'];z['source_sha256']=oldc['source_sha256'];assert z==oldc
write(OUT,out)
guard()
write(INTEGRITY,{'status':'passed_isolated_exact_original_core22_rows_and_fresh_source51_reviews','created_at_utc':now(),'candidate':ref(OUT),'packet':ref(PACKET),'baseline':ref(BASE),'identity':identity,'added_proof_sources':9,'added_public_theorems':88,'baseline166_proof_rows_exact':True,'old46_monitoring_claims_and41_material_rows_exact_in_original_records':True,'whole_material_units':sorted(whole),'added_component_material_claims':len(material_additions),'changed_exercises':changed['exercises'],'counts':out['counts'],'held22_working_owner_sha256':held,'live_owner_written':False,'coverage_complete':False})
print(json.dumps({'status':'passed','candidate':ref(OUT),'integrity':ref(INTEGRITY),'whole_material_units':len(whole),'added_components':len(material_additions),'counts':out['counts']}))
