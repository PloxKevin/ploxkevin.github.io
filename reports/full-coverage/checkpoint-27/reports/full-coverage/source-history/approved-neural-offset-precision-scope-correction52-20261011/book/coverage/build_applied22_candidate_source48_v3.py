"""Build only NEW isolated Applied22 artifacts, preserving all held21 assets."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,shutil,collections,sys
ROOT=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/applied-future22/source48'
INV='book/coverage/inventory-after-correction48.json'
INV_SHA='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
REVIEWS=[
 ('book/coverage/checks/applied-future21/applied-nine-elementary-material21-independent-foundations-source-review-v1.json','16980feb5a01af7baf6955f93760dd47ee8d64721a90160c4d9a79f7ce6539dc'),
 ('book/coverage/checks/applied-future21/applied-sixteen-existing-hints21-independent-foundations-source-review-v1.json','e6e9e336c1768ae8de5e35da74006b74161e9aa70ae95a81611d1a9d27903467'),
 ('book/coverage/checks/applied-future22/systems-material/systems-nine-literals-independent-foundations-source-review22-v2.json','ece08993a867c8873f3db9f132571bdfba78990b9b82fb0be758278b6dd88842')]
PAIRS={
 'verification/lean/SafeLearning/CompleteAppliedElementaryMaterial21.lean':['book/coverage/checks/applied-future21/CompleteAppliedElementaryMaterial21-standalone.json','book/coverage/checks/applied-future21/CompleteAppliedElementaryMaterial21-named-build.json'],
 'verification/lean/SafeLearning/CompleteAppliedSystemsMaterial22.lean':['book/coverage/checks/applied-future22/systems-material/standalone.json','book/coverage/checks/applied-future22/systems-material/named-build.json'],
 'verification/lean/SafeLearning/CompleteAppliedSystemsMaterialConsequences22.lean':['book/coverage/checks/applied-future22/systems-material/consequences-standalone.json','book/coverage/checks/applied-future22/systems-material/consequences-named-build.json']}
OLD_ASSETS=['book/coverage/applied.json','book/coverage/applied-promotions.json','book/coverage/applied-audit21-source48-additions-v1.json','book/coverage/build_applied21_source48_v2.py']
def path(p):
 p=Path(p);return p if p.is_absolute() else ROOT/p
cache={}
def sha(p):
 p=path(p);s=p.stat();key=(str(p),s.st_size,s.st_mtime_ns)
 if key not in cache:cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[key]
def read(p):return json.loads(path(p).read_text())
def write(p,r):
 p=path(p);assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
def build():
 assert sha(INV)==sha('book/coverage/inventory.json')==INV_SHA
 inv=read(INV);us={z['key']:z for z in inv['material_source_units']}
 old=read(OLD_ASSETS[0]);oldp=read(OLD_ASSETS[1]);oldoffer=read(OLD_ASSETS[2]);ledger=copy.deepcopy(old);prom=copy.deepcopy(oldp)
 assert sha(OLD_ASSETS[0])==oldoffer['mapped_ledger_sha256'] and sha(OLD_ASSETS[1])==oldoffer['mapped_promotions_sha256']
 history=[]
 for p in OLD_ASSETS:
  q=BASE+'/baseline21/'+Path(p).name;path(q).parent.mkdir(parents=True,exist_ok=True)
  if not path(q).exists():shutil.copyfile(path(p),path(q))
  assert sha(q)==sha(p)
  history.append({'original':p,'sha256':sha(p),'byte_exact_copy':q})
 claims={k:c for c in ledger['material_claims'] for k in c['source_unit_keys']};reviewobjs=[];rows=[];aliases={}
 def archive(p):
  if not path(p).is_file():return
  ext=Path(p).suffix
  if ext not in ['.json','.log','.py','.lean','.txt']:return
  h=sha(p);q=BASE+'/objects/'+h+ext
  if not path(q).exists():path(q).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path(p),path(q))
  assert sha(q)==h;aliases[str(p)]={'path':q,'sha256':h}
 def scan(r):
  if isinstance(r,str):
   if '\n' not in r and (r.startswith('/tmp/') or r.startswith('book/coverage/') or r.startswith('verification/lean/') or r.startswith('reports/full-coverage/')):archive(r)
  elif isinstance(r,dict):
   for k,v in r.items():scan(k);scan(v)
  elif isinstance(r,list):
   for v in r:scan(v)
 for f,h in REVIEWS:
  assert sha(f)==h;r=read(f);assert r['inventory_sha256']==INV_SHA;scan(r);archive(f)
  ref={'file':f,'sha256':h,'original_review_time':r['reviewed_at_utc'],'reviewer':r['reviewer'],'byte_exact_original_copy':aliases[f]['path']}
  reviewobjs.append({'reference':ref,'exact_original_body':r})
  for u in r['material_units']:
   k=u['source_unit_key'];z=us[k];exact=u.get('entire_inventory_record',u.get('exact_current48_inventory_record'));assert exact==z
   assert u['missing_clauses']==[] and u['material_status'] in ['proved','not_a_formal_claim']
   c=claims[k];assert c['source_unit_keys']==[k] and c['status']=='pending'
   assert z['source_sha256']==sha(z['source']) and z['text_sha256']==u['unit_text_sha256'] and hashlib.sha256(z['source_text'].encode()).hexdigest()==z['text_sha256']
   c.update(kind='independently_reviewed_mathematical_source_unit' if u['material_status']=='proved' else 'individually_reviewed_instruction_or_nominal_label',status=u['material_status'],lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_unit_reason'],remaining_gaps=[],source_review={**ref,'source_unit_key':k,'unit_text_sha256':z['text_sha256'],'inventory':INV,'inventory_sha256':INV_SHA,'classification_scope':u['per_unit_reason']})
   prom['material'][k]={'source_text_sha256':c['text_sha256'],'claim':{a:copy.deepcopy(b) for a,b in c.items() if a not in ['source','source_unit_keys','source_sha256','text_sha256']},'source_review':copy.deepcopy(c['source_review'])}
   rows.append({'source_unit_key':k,'entire_current48_inventory_record':z,'original_complete_reviewed_row':u,'original_source_review':ref,'normalized_exact_ledger_claim':copy.deepcopy(c)})
 assert len(rows)==len({z['source_unit_key'] for z in rows})==34
 assert collections.Counter(z['original_complete_reviewed_row']['material_status'] for z in rows)=={'proved':26,'not_a_formal_claim':8}
 sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
 new={};actual=[];exports=[];selection=read('reports/full-coverage/checkpoint-21-manifest.json')
 for src,ps in PAIRS.items():
  h=sha(src);assert src not in old['proof_files'] and src not in selection['proof_files'];ledger['proof_files'][src]=h
  names=[d['name'] for d in declarations(path(src).read_text()) if d['kind'] in ['theorem','lemma']];exports+=names
  ev={src:h};refs=[]
  for p in ps:
   r=read(p);assert r['exit_code']==0 and r['source_sha256_before']==r['source_sha256_after']==h and r['source']==src
   assert sha(r['log'])==r['log_sha256']
   if 'source_snapshot' in r:assert sha(r['source_snapshot'])==h
   archive(p);scan(r)
   for a in [p,r['log']]+([r['source_snapshot']] if 'source_snapshot' in r else []):ev[a]=sha(a)
   refs.append({'file':p,'sha256':sha(p),'actual_original_record':r});actual.append(refs[-1])
  for z in reviewobjs:
   if any(n in u['lean_declarations'] for n in names for u in z['exact_original_body']['material_units']):ev[z['reference']['file']]=z['reference']['sha256']
  new[src]={'sha256':h,'evidence_sha256':ev,'standalone_evidence':ps[0],'standalone_evidence_sha256':sha(ps[0]),'named_evidence':ps[1],'named_evidence_sha256':sha(ps[1]),'theorem_count':len(names),'mapped_named_declarations':names,'ownership':'Applied22 immutable actual paired source supplied for exact individually reviewed material units; no new whole exercise claim.'}
 assert len(exports)==16 and len(new)==3 and len(actual)==6
 allnames=set()
 for src,z in selection['proof_files'].items():assert sha(src)==z['sha256'];allnames.update(d['name'] for d in declarations(path(src).read_text()))
 for src in new:allnames.update(d['name'] for d in declarations(path(src).read_text()))
 for z in rows:assert set(z['normalized_exact_ledger_claim']['lean_declarations'])<=allnames
 changed={r['source_unit_key'] for r in rows}
 for a,b in zip(old['material_claims'],ledger['material_claims']):
  if not set(a['source_unit_keys'])&changed:assert a==b
 assert ledger['exercises']==old['exercises'] and prom['exercises']==oldp['exercises']
 for k,v in oldp['material'].items():
  if k not in changed:assert prom['material'][k]==v
 assert {k:v for k,v in ledger['proof_files'].items() if k not in new}==old['proof_files']
 now=datetime.now(timezone.utc).isoformat();integration={'inventory':INV,'inventory_sha256':INV_SHA,'baseline21_history':history,'exact_source_reviews':[z['reference'] for z in reviewobjs],'fresh_material_keys':list(changed),'new_proof_files':new,'scope':'Isolated source48 candidate:34 individually reviewed passages only,26 proved/8nonformal.128 old whole exercises remain exact; old21 owner assets stay held.'}
 ledger['current22_candidate_integration']=integration;prom['current22_candidate_integration']=integration;ledger['generated_at_utc']=now
 write(BASE+'/original-review-and-exact-row-bindings-v1.json',{'status':'exact_original_review_bodies_times_current48_records_and_actual_pair_bindings_ready','created_at_utc':now,'inventory':INV,'inventory_sha256':INV_SHA,'exact_owned_exercise_records':[e for e in inv['exercises'] if e['source'] in old['scope_pages']],'exact_owned_material_records':[u for u in inv['material_source_units'] if u['source'] in old['scope_pages']],'source_sha256':old['source_sha256'],'baseline21_history':history,'reviews':reviewobjs,'material_rows':rows,'new_proof_files':new,'actual_paired_records':actual,'canonical_original_path_aliases':aliases,'counts':{'material_rows':34,'proved':26,'nonformal':8,'new_sources':3,'new_public_exports':16,'actual_zero_records':6},'coverage_complete':False,'preserved_second_builder_failure':{'file':'/tmp/build-applied22-candidate-source48-v2-failed.json','sha256':sha('/tmp/build-applied22-candidate-source48-v2-failed.json'),'helper_copy':'/tmp/build-applied22-candidate-source48-v2-failed.py','helper_sha256':sha('/tmp/build-applied22-candidate-source48-v2-failed.py')},'preserved_initial_builder_failure':{'file':'/tmp/build-applied22-candidate-source48-v1-failed.json','sha256':sha('/tmp/build-applied22-candidate-source48-v1-failed.json'),'helper_copy':'/tmp/build-applied22-candidate-source48-v1-failed.py','helper_sha256':sha('/tmp/build-applied22-candidate-source48-v1-failed.py')}})
 write(BASE+'/canonical-path-aliases-v1.json',{'status':'byte_exact_original_review_checker_execution_and_history_aliases','aliases':aliases})
 write(BASE+'/applied22-candidate-v1.json',ledger);write(BASE+'/applied-promotions22-candidate-v1.json',prom)
 for z in history:assert sha(z['original'])==sha(z['byte_exact_copy'])==z['sha256']
 offered={'schema_version':1,'status':'isolated_source48_applied22_candidate_ready_for_independent_mechanics_no_live_mapping_claim','created_at_utc':now,'inventory':INV,'inventory_sha256':INV_SHA,'base_selection':'reports/full-coverage/checkpoint-21-manifest.json','base_selection_sha256':sha('reports/full-coverage/checkpoint-21-manifest.json'),'actual_passing_base_aggregate':'reports/full-coverage/lean-checkpoint-21/verification.json','actual_passing_base_aggregate_sha256':sha('reports/full-coverage/lean-checkpoint-21/verification.json'),'mapped_ledger':BASE+'/applied22-candidate-v1.json','mapped_ledger_sha256':sha(BASE+'/applied22-candidate-v1.json'),'mapped_promotions':BASE+'/applied-promotions22-candidate-v1.json','mapped_promotions_sha256':sha(BASE+'/applied-promotions22-candidate-v1.json'),'candidate_builder':'book/coverage/build_applied22_candidate_source48_v3.py','candidate_builder_sha256':sha('book/coverage/build_applied22_candidate_source48_v3.py'),'original_review_bindings':BASE+'/original-review-and-exact-row-bindings-v1.json','original_review_bindings_sha256':sha(BASE+'/original-review-and-exact-row-bindings-v1.json'),'canonical_path_aliases':BASE+'/canonical-path-aliases-v1.json','canonical_path_aliases_sha256':sha(BASE+'/canonical-path-aliases-v1.json'),'source_sha256':old['source_sha256'],'proof_files':new,'new_actual_paired_records':actual,'original_independent_review_references':[z['reference'] for z in reviewobjs],'retained_previous_offer':history[2],'baseline21_owner_assets':history,'new_material_keys':[z['source_unit_key'] for z in rows],'counts':{'old_whole_exercises_unchanged':128,'old_exercise_claims_unchanged':468,'owned_physical_units':2059,'new_material_units':34,'new_proved_material_units':26,'new_nonformal_material_units':8,'new_whole_exercises':0,'new_proof_sources':3,'new_public_exports':16,'actual_zero_paired_records':6,'prior_ledger_proof_rows_preserved':len(old['proof_files'])},'coverage_complete':False,'limits':['Original three mathematical review bodies/times and all old21 live metadata remain unchanged. This candidate is not a live global22 validation or aggregate execution.','New elementary and systems proof source names retain their original21/22 suffixes; explicit offer ownership and exact source hash control selection. Monitoring/Module candidate proof rows are not selected here.','The source proof corpus and canonical paired records are genuinely actual0. Original failed source/checker trials and dependency output stay unchanged through explicit immutable aliases.']}
 write(BASE+'/applied-audit22-candidate-source48-additions-v1.json',offered)
 print(json.dumps({'offer':BASE+'/applied-audit22-candidate-source48-additions-v1.json','offer_sha256':sha(BASE+'/applied-audit22-candidate-source48-additions-v1.json'),'candidate_sha256':sha(BASE+'/applied22-candidate-v1.json'),'promotions_sha256':sha(BASE+'/applied-promotions22-candidate-v1.json'),'counts':offered['counts']}))
if __name__=='__main__':build()
