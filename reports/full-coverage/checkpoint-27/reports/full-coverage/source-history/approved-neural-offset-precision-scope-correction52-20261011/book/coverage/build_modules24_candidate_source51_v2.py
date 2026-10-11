"""Construct an isolated, precisely reviewed tanh candidate; never install it.

The original review bodies, dates, and remaining whole-source gaps are retained.
The original twelve-body TMP source supplies only three new companion bodies:
its first nine are already present in the separate original canonical source.
"""
from pathlib import Path
from datetime import datetime, timezone
import collections, copy, hashlib, json, re
from lean_names import declarations

R=Path(__file__).resolve().parents[2]
B='book/coverage/checks/modules-future24/source51'
READY='book/coverage/checks/modules-future24/tanh-offset/three-source16-export-canonical-original-peer-binding-readiness24-v1.json'
READY_SHA='d173dbc40dcce01de6d473948fefc78b61d990cbfe21f5787e784e0c086b7651'
INV='book/coverage/inventory-after-correction51.json'
INV_SHA='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
LIVE='book/coverage/modules.json'
LIVE_SHA='448b83324829b136ef9745977e10f397086b6872f6d3141854d96504dfd53367'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest()
J=lambda n:json.loads((R/n).read_text())
ref=lambda n:{'file':n,'sha256':H(n)}
def put(n,d):
 p=R/n;assert not p.exists(),n;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def archive(old):
 p=Path(old);assert p.is_absolute() and p.is_file(),old
 n=B+'/original-canonical-binding-peer/'+p.name;q=R/n;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 assert H(n)==hashlib.sha256(p.read_bytes()).hexdigest()
 return ref(n)
def main():
 assert H(LIVE)==LIVE_SHA and H(INV)==INV_SHA==H('book/coverage/inventory.json')
 assert H(READY)==READY_SHA
 ready=J(READY);old=J(LIVE);selection=J('reports/full-coverage/checkpoint-23-selection.json')
 assert selection['proof_file_count']==1131
 for n,p in selection['proof_files'].items():assert H(n)==p['sha256'],n
 first=ready['canonical_proofs'][0]['actual_paired_records'][0]['entire_original_actual_record_body_and_time']
 protected={**first['held23_owner_and_inventory_sha256'],**first['exact_current51_assets_sha256']}
 for n,h in protected.items():assert H(n)==h,n
 baseline=B+'/pre-candidate23/modules.json';q=R/baseline;q.parent.mkdir(parents=True,exist_ok=True)
 
 if q.exists():assert q.read_bytes()==(R/LIVE).read_bytes()
 else:q.write_bytes((R/LIVE).read_bytes())
 assert H(baseline)==LIVE_SHA
 aliases=copy.deepcopy(ready['original_path_byte_aliases'])
 for original,a in aliases.items():assert H(a['file'])==a['sha256'],original
 binding_paths=[
  '/tmp/modules-tanh16-canonical-original-body-binding-independent-foundations-review-v1.json',
  '/tmp/modules-tanh16-canonical-original-body-binding-independent-foundations-v1.py',
  '/tmp/modules-tanh16-canonical-original-body-binding-independent-foundations-actual-v1.json',
  '/tmp/modules-tanh16-canonical-original-body-binding-independent-foundations-actual-v1.log',
  '/tmp/run-modules-tanh16-canonical-original-body-binding-independent-foundations-v1.py']
 for p in binding_paths:aliases[p]=archive(p)
 br=aliases[binding_paths[0]];binding=J(br['file'])
 assert br['sha256']=='b21a89b29b00165cc8af7f6c1f07091ecb218026183f2c0a38ea5fa38effa205'
 assert binding['errors']==[] and binding['new_public_export_count']==16
 original_reviews=[ready['original_nine_body_peer'],ready['original_seven_bridge_peer']]
 reviews=[];review_refs=[]
 for i,r in enumerate(original_reviews):
  a=r;assert H(a['file'])==a['sha256']
  rv=J(a['file']);assert rv['errors']==[]
  assert rv==ready[['entire_original_nine_body_peer_and_time','entire_original_seven_bridge_peer_and_time'][i]]
  reviews.append(rv);review_refs.append({**a,'reviewer':rv['reviewer'],'original_review_time':rv['reviewed_at_utc']})
 assert binding['entire_original_nine_body_semantic_review_and_time']==reviews[0]
 assert binding['entire_original_seven_bridge_semantic_review_and_time']==reviews[1]
 aliasfile=B+'/tanh24-original-path-byte-aliases-v1.json'
 put(aliasfile,{'status':'exact_original_trial_review_failure_and_canonical_binding_byte_aliases','aliases':aliases,'original_absolute_refs_bodies_commands_and_times_unchanged':True})
 inv=J(INV);es={r['key']:r for r in inv['exercises']};us={r['key']:r for r in inv['material_source_units']}
 key='nn-in-the-loop.html::exercise-20'
 for rv in reviews:
  assert rv['exercise']['entire_inventory_record']==es[key]
  assert not rv['exercise']['whole_exercise_approved']
  for u in rv['material_units']:assert u['entire_inventory_record']==us[u['source_unit_key']]
 out=copy.deepcopy(old);e=next(r for r in out['exercises'] if r['inventory_key']==key)
 assert e['status']=='pending';original_claims=copy.deepcopy(e['claims'])
 names_alias=ready['explicit_old_to_new_three_declaration_names']
 def mapped(names):return [names_alias.get(n,n) for n in names]
 groups=[]
 for index,rv in enumerate(reviews):
  cs=rv['exercise']['reviewed_components'] if index==0 else rv['approved_components']
  for c in cs:
   assert c['missing_clauses']==[] and c['remaining_gaps']==[]
   rr=review_refs[index]
   unitkeys=[u['source_unit_key'] for u in rv['material_units'] if
             (index==1 or any(x['component_id']==c['component_id'] for x in u.get('components',[])))]
   atom={'id':key+'::source51-reviewed24-component-'+c['component_id'],
    'statement_in_prose':c['per_component_reason'],'kind':'independently_reviewed_precise_mathematical_component',
    'status':'proved','lean_declarations':mapped(c['lean_declarations']),
    'hypotheses':copy.deepcopy(c['hypotheses']),'correspondence':c['per_component_reason'],
    'remaining_gaps':[],'source_unit_keys':unitkeys,'independent_source_review':rr,
    'entire_original_component_body':copy.deepcopy(c),'explicit_declaration_namespace_aliases':names_alias,
    'canonical_source_binding_peer':br,'scope_limits':copy.deepcopy(rv['scope'])}
   e['claims'].append(atom);groups.append(atom)
 assert len(groups)==12 and e['claims'][:len(original_claims)]==original_claims
 e['status']='partial';e['independent_component_source_reviews24']=review_refs
 e['remaining_whole_source_gaps24']=copy.deepcopy(reviews[1]['exercise']['remaining_gaps'])
 units={c['id']:c for c in out['material_claims']}
 whole=next(u for u in reviews[0]['material_units'] if u['whole_unit_approved'])
 assert whole['source_unit_key']=='nn-in-the-loop.html::node-1258' and whole['missing_clauses']==[]
 for unitkey in ['nn-in-the-loop.html::node-'+str(n) for n in [1254,1258,1260,1262]]:
  target=units[unitkey+'::claim-review'];prior=copy.deepcopy(target);assert target['status']=='pending'
  rvindex=1 if unitkey.endswith(('1254','1262')) else 0
  u=next(u for u in reviews[rvindex]['material_units'] if u['source_unit_key']==unitkey)
  if unitkey==whole['source_unit_key']:
   target.update(status='proved',kind='independently_reviewed_mathematical_source_unit',
    lean_declarations=mapped(whole['lean_declarations']),hypotheses=copy.deepcopy(whole['hypotheses']),
    correspondence=whole['per_unit_reason'],remaining_gaps=[],independent_source_review=review_refs[0])
  else:
   target['remaining_gaps']=copy.deepcopy(u['missing_clauses'])
   target['independent_source_review']=review_refs[rvindex]
   target['reviewed_precise_component_ids24']=[g['id'] for g in groups if unitkey in g['source_unit_keys']]
  target['prior_source51_claim_body_preserved']=prior
  target['canonical_source_binding_peer']=br
 for g in groups:
  atom=copy.deepcopy(g);atom['id']=key+'::material-source51-reviewed24-component-'+g['entire_original_component_body']['component_id']
  out['material_claims'].append(atom)
 newpaths=[];publics=[];imports={};proof_rows={}
 for p in ready['canonical_proofs']:
  n=p['canonical_source']['file'];assert H(n)==p['canonical_source']['sha256'] and n not in old['proof_files']
  text=(R/n).read_text();decls=declarations(text);public=[d['name'] for d in decls if d['kind'] in ('theorem','lemma')]
  assert public==p['public_theorem_names'];pairs=p['actual_paired_records']
  for pair,kind in zip(pairs,['lean_standalone','named_lean_module_build']):
   ar=pair['actual_record'];assert H(ar['file'])==ar['sha256'];a=J(ar['file'])
   assert a==pair['entire_original_actual_record_body_and_time'] and a['actual_exit_code']==0 and a['kind']==kind
   assert a['source']==n and a['source_sha256_before']==a['source_sha256_after']==H(n)
   assert H(pair['raw_log']['file'])==pair['raw_log']['sha256']==a['raw_log_sha256']
   assert H(pair['source_snapshot']['file'])==pair['source_snapshot']['sha256']==a['source_snapshot_sha256']==H(n)
  st=pairs[0]
  row={'sha256':H(n),'selection_scope':'independently_reviewed_precise_tanh24_component_source',
   'proof_selection_owner':'Modules24','standalone_compile_status':'passed',
   'standalone_compile_evidence':{'file':n,'sha256':H(n),'exit_code':0,'source_unchanged':True,
    'log':st['raw_log']['file'],'log_sha256':st['raw_log']['sha256'],
    'compiler_manifest':st['actual_record']['file'],'compiler_manifest_sha256':st['actual_record']['sha256']},
   'actual_paired_records':copy.deepcopy(pairs),'declarations':public}
  out['proof_files'][n]=row
  proof_rows[n]={'sha256':H(n),'declarations':public,'actual_paired_records':copy.deepcopy(pairs),
   'evidence_sha256':{r['file']:r['sha256'] for pair in pairs for r in [pair['actual_record'],pair['raw_log'],pair['source_snapshot']]}}
  for name in public:
   m=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert m
   out['declarations'].append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip()})
  for module in re.findall(r'^import\s+(SafeLearning\.\S+)',text,re.M):
   path='verification/lean/'+module.replace('.','/')+'.lean';imports[path]=H(path)
  newpaths.append(n);publics+=public
 assert len(newpaths)==3 and len(publics)==len(set(publics))==16
 for g in groups:assert set(g['lean_declarations'])<=set(publics)
 for n,h in imports.items():
  if n not in newpaths:
   assert n in selection['proof_files'] and selection['proof_files'][n]['sha256']==h
   out['required_external_import_dependencies'][n]=h
 inp=B+'/tanh24-source51-input-bindings-v1.json'
 put(inp,{'schema_version':1,'current_inventory':ref(INV),'baseline23_module_ledger':ref(baseline),
  'baseline23_live_module_ledger':ref(LIVE),'readiness':ref(READY),'canonical_binding_peer':br,
  'canonical_original_path_aliases':ref(aliasfile),'entire_original_nine_body_review_and_time':reviews[0],
  'entire_original_seven_bridge_review_and_time':reviews[1],'original_source_reviews':review_refs,
  'explicit_old_to_new_three_declaration_names':names_alias,'protected_owner_inventory_and31_asset_sha256':protected,
  'partial_exercise_key':key,'whole_material_unit_keys':[whole['source_unit_key']],
  'partial_material_unit_keys':['nn-in-the-loop.html::node-'+str(n) for n in [1254,1260,1262]],
  'precise_component_groups':12,'proof_files':proof_rows,'required_safelearning_import_sha256':imports,
  'scope':'Original source51 literal scope only. Six false decimal equalities, temporal and general multiplier clauses remain pending. No temporal future25 sources are selected here.'})
 out['generated_at_utc']=datetime.now(timezone.utc).isoformat()
 out['reviewed_work_integration24_tanh_candidate']={'input_bindings':ref(inp),'baseline23_module_ledger':ref(baseline),
  'fresh_whole_exercises':[],'fresh_partial_exercise':key,'fresh_whole_material_units':[whole['source_unit_key']],
  'reviewed_partial_material_units':['nn-in-the-loop.html::node-'+str(n) for n in [1254,1260,1262]],
  'original_source_reviews':review_refs,'canonical_binding_peer':br,'new_source_files':newpaths,
  'distinct_new_public_exports':16,'approved_component_groups':12,'scope':'Isolated candidate only; original statuses/times/bodies retained as history. Whole Exercise14.6 and answer(b)/(c) remain pending.'}
 out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in out['exercises'])),
  'exercise_claim_status':dict(collections.Counter(c['status'] for e in out['exercises'] for c in e['claims'])),
  'material_claim_status':dict(collections.Counter(c['status'] for c in out['material_claims'])),
  'new_declarations':len(out['declarations'])}
 olde={x['inventory_key']:x for x in old['exercises']};oldu={x['id']:x for x in old['material_claims']}
 for x in out['exercises']:
  if x['inventory_key']!=key:assert x==olde[x['inventory_key']]
 changed={k+'::claim-review' for k in ['nn-in-the-loop.html::node-'+str(n) for n in [1254,1258,1260,1262]]}
 for x in out['material_claims'][:len(old['material_claims'])]:
  if x['id'] not in changed:assert x==oldu[x['id']]
 for n,r in old['proof_files'].items():assert out['proof_files'][n]==r
 assert out['declarations'][:len(old['declarations'])]==old['declarations']
 for n,h in protected.items():assert H(n)==h,n
 target=B+'/modules24-candidate-source51-v1.json';put(target,out)
 guard=B+'/modules24-source51-candidate-integrity-v1.json';put(guard,{'status':'passed_exact_isolated_static_tanh_component_candidate_construction',
  'candidate_ledger':ref(target),'input_bindings':ref(inp),'baseline23_module_ledger':ref(baseline),
  'original_source_reviews':review_refs,'canonical_binding_peer':br,'original_component_bodies_times_and_namespace_aliases_preserved':True,
  'new_whole_exercises':0,'new_partial_exercises':1,'new_whole_material_units':1,'approved_component_groups':12,
  'new_sources':3,'new_distinct_public_exports':16,'new_actual_paired_records':6,
  'old_exercise_bodies_preserved':216,'old_material_bodies_preserved':len(old['material_claims'])-4,
  'old_proof_rows_preserved':len(old['proof_files']),'old_declaration_prefix_exact':True,
  'live_owner_or_html_mutated':False,'temporal_future25_sources_selected':False,'errors':[]})
 print(json.dumps({'candidate':ref(target),'integrity':ref(guard),'input_bindings':ref(inp),'counts':out['counts']}))
if __name__=='__main__':main()
