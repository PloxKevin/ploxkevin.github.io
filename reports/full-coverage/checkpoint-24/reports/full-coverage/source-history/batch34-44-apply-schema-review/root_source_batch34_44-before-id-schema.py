"""Prepare and apply the exact independently approved eleven-page source batch."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, importlib.util, sys, subprocess
R=Path(__file__).resolve().parents[3]
D=R/'book/coverage/checks/root-source-batch34-44'
PLAN=D/'prewrite-plan-v1.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=lambda:datetime.now(timezone.utc).isoformat()
def load(p):return json.loads((R/p).read_text())
def write(p,d):
 assert not p.exists(),p
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_text(json.dumps(d,indent=2)+'\n')
def protected():
 c=load('reports/full-coverage/checkpoint-18-manifest.json'); paths={}
 for s,row in c['proof_files'].items():
  paths[s]=row['sha256'];paths.update(row['evidence_sha256'])
 assert len(c['proof_files'])==490 and len(paths)==565 and len(c['frozen_inputs_sha256'])==2431
 for p,h in paths.items():assert H(R/p)==h,p
 for p,h in c['frozen_inputs_sha256'].items():assert H(R/c['snapshot']/p)==h,p
 return dict(selected_proofs=490,source_and_evidence_paths=565,frozen18_inputs=2431,all_hashes_exact=True)
def compare(a,b,pages):
 assert a['counts']==b['counts']
 changed={}
 for section in ['exercises','material_source_units']:
  old={r['key']:r for r in a[section]};new={r['key']:r for r in b[section]};assert old.keys()==new.keys();changed[section]=[]
  for k,x in old.items():
   y=new[k];assert x.keys()==y.keys()
   for f in x:
    if f not in ['source_sha256','source_text','text_sha256']:assert x[f]==y[f],(k,f)
   if x['source_text']!=y['source_text']:changed[section].append(k)
   else:assert x['text_sha256']==y['text_sha256']
   if x['source'] not in pages:assert x==y
 return changed
if '--apply' not in sys.argv:
 assert H(R/'book/coverage/inventory.json')=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
 registry=load('book/coverage/material-corrections.json');assert len(registry['corrections'])==33
 pairs=[
 ('foundations-basics','foundations-basics-merged-approved-proposal19-independent-applied-confirmation-v1.json'),
 ('applied-systems','applied-systems-merged-approved-proposal19-independent-foundations-confirmation-v1.json'),
 ('applied-probability','applied-probability-merged-approved-proposal19-independent-foundations-confirmation-v1.json'),
 ('applied-rl','modules-independent-rl-merge-proposal-review33-v2.json'),
 ('applied-policy','modules-independent-policy-merge-proposal-review33-v2.json')]
 pages=[]
 for name,peer in pairs:
  p='book/coverage/checks/'+name+'-merged-approved-proposal19-v1.json';q='book/coverage/checks/'+peer
  d=load(p);v=load(q);assert v['proposal_sha256']==H(R/p)
  assert ('passed' in v['status'] or 'confirmed' in v['status']) and v['reviewer']!=d['prepared_by']
  pages.append(dict(proposal=p,proposal_sha256=H(R/p),independent_merge_review=q,independent_merge_review_sha256=H(R/q),source=d['source']))
 p='book/coverage/checks/modules-approved-corrections33/merged-approved-module-proposals19-v2.json';q='book/coverage/checks/modules-approved-corrections33/merged-approved-module-proposals19-independent-foundations-confirmation-v2.json'
 batch=load(p);peer=load(q)
 assert H(R/p) in json.dumps(peer)
 for row in batch['pages']:
  assert H(R/row['file'])==row['sha256']
  pages.append(dict(proposal=row['file'],proposal_sha256=row['sha256'],independent_merge_review=q,independent_merge_review_sha256=H(R/q),source=row['source'],approved_module_batch=p,approved_module_batch_sha256=H(R/p)))
 assert len(pages)==len({p['source'] for p in pages})==11
 D.mkdir(parents=True,exist_ok=False)
 sim=D/'simulation';(sim/'SafeLearning').mkdir(parents=True)
 for f in (R/'SafeLearning').glob('*.html'):shutil.copy2(f,sim/'SafeLearning'/f.name)
 sys.path.insert(0,str(R/'book'));from validate import Document
 expected={s:set() for s in ['exercises','material_source_units']}
 exercise_keys={r['key'] for r in load('book/coverage/inventory.json')['exercises']}
 replacements=0
 for index,page in enumerate(pages,34):
  d=load(page['proposal']);before=(R/page['source']).read_bytes();after=before
  assert H(R/page['source'])==d['source_sha256_before']
  assert H(R/d['source_bytes_before_snapshot'])==d['source_sha256_before']
  for rep in d['replacements']:
   assert after.count(rep['before'].encode())==rep.get('count',1)==1
   after=after.replace(rep['before'].encode(),rep['after'].encode(),1);replacements+=1
  assert hashlib.sha256(after).hexdigest()==d['proposed_source_sha256_after']==H(R/d['source_bytes_proposed_after_snapshot'])
  reverse=after
  for rep in reversed(d['replacements']):
   assert reverse.count(rep['after'].encode())==1;reverse=reverse.replace(rep['after'].encode(),rep['before'].encode(),1)
  assert reverse==before and before.count(b'\n')==after.count(b'\n')
  a,b=Document(before.decode()),Document(after.decode());assert len(a.nodes)==len(b.nodes)
  assert all((x.tag,x.attrs,x.line)==(y.tag,y.attrs,y.line) for x,y in zip(a.nodes,b.nodes))
  (sim/page['source']).write_bytes(after)
  for s,h in d['actual_proof_source_sha256'].items():assert H(R/s)==h
  page.update(correction_index=index,before_sha256=d['source_sha256_before'],after_sha256=d['proposed_source_sha256_after'],replacements=d['replacements'],proof_source_sha256=d['actual_proof_source_sha256'])
  expected['exercises'].update(d.get('expected_changed_exercises',[]))
  expected['material_source_units'].update(d.get('expected_changed_material_units',[]))
  for k in d.get('expected_changed_text_keys',[]):expected['exercises' if k in exercise_keys else 'material_source_units'].add(k)
 spec=importlib.util.spec_from_file_location('root_batch_inventory',R/'book/inventory_claims.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
 g.ROOT=sim;g.OUT=sim/'book/coverage';g.inventory();old=load('book/coverage/inventory.json');new=json.loads((g.OUT/'inventory.json').read_text())
 delta=compare(old,new,{p['source'] for p in pages})
 for s in expected:assert set(delta[s])==expected[s],(s,set(delta[s])^expected[s])
 write(PLAN,dict(schema_version=1,status='root_exact_approved_eleven_page_prewrite_full_parser_and_protection_passed',prepared_at_utc=now(),inventory_before='book/coverage/inventory-after-correction33.json',inventory_before_sha256=H(R/'book/coverage/inventory.json'),registry_before_sha256=H(R/'book/coverage/material-corrections.json'),writer='/root',correction_indices=list(range(34,45)),pages=pages,counts=dict(pages=11,replacements=replacements,changed_exercises=len(delta['exercises']),changed_material_units=len(delta['material_source_units'])),actual_changed_text_keys=delta,actual_full_parser=dict(exit_code=0,command=['python3','book/coverage/checks/root_source_batch34_44.py'],parser='book/inventory_claims.py',parser_sha256=H(R/'book/inventory_claims.py'),simulated_inventory=str((g.OUT/'inventory.json').relative_to(R)),simulated_inventory_sha256=H(g.OUT/'inventory.json'),all_counts_keys_lines_locators_DOM_structure_other_fields_preserved=True),protection=protected(),limits=['Exact unchanged independently approved substitutions only.','One final inventory regeneration after all eleven page writes, immutable source44 inventory; no intermediate inventory claim.','Changed literal mathematics requires fresh source review; unchanged literal semantic decisions retain original review bodies/times in identity sidecars.']))
 print(json.dumps(dict(plan=str(PLAN.relative_to(R)),sha256=H(PLAN),counts=json.loads(PLAN.read_text())['counts'])))
else:
 p=json.loads(PLAN.read_text());assert p['writer']=='/root'
 assert H(R/'book/coverage/inventory.json')==p['inventory_before_sha256'] and H(R/'book/coverage/material-corrections.json')==p['registry_before_sha256'];protected()
 for page in p['pages']:
  assert H(R/page['proposal'])==page['proposal_sha256'] and H(R/page['independent_merge_review'])==page['independent_merge_review_sha256']
  assert H(R/page['source'])==page['before_sha256']
  for s,h in page['proof_source_sha256'].items():assert H(R/s)==h
 hist=R/'reports/full-coverage/source-history/approved-eleven-page-corrections34-44-20261010';hist.mkdir(parents=True,exist_ok=False)
 names=['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/build_core.py','book/coverage/core_path_reviews.py','book/coverage/core_policy_components.py','book/coverage/core_labels19.py','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json']+[page['source'] for page in p['pages']]
 preserved={}
 for name in names:
  dest=hist/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(R/name,dest);assert H(dest)==H(R/name);preserved[name]=dict(path=str(dest.relative_to(R)),sha256=H(dest))
 write(hist/'preserved-history.json',dict(preserved_at_utc=now(),files=preserved,prewrite_plan=str(PLAN.relative_to(R)),prewrite_plan_sha256=H(PLAN)))
 registry=load('book/coverage/material-corrections.json');assert len(registry['corrections'])==33
 for page in p['pages']:
  text=(R/page['source']).read_text();before=text
  for rep in page['replacements']:
   assert text.count(rep['before'])==1;text=text.replace(rep['before'],rep['after'],1)
  assert hashlib.sha256(text.encode()).hexdigest()==page['after_sha256']
  (R/page['source']).write_text(text)
  registry['corrections'].append(dict(index=page['correction_index'],source=page['source'],line=before[:before.index(page['replacements'][0]['before'])].count('\n')+1,before_sha256=page['before_sha256'],after_sha256=page['after_sha256'],replacements=page['replacements'],reason='Exact independently approved per-page precision and hypothesis corrections.',proposal=page['proposal'],proposal_sha256=page['proposal_sha256'],independent_proposal_review=page['independent_merge_review'],independent_proposal_review_sha256=page['independent_merge_review_sha256'],independent_root_prewrite_integrity_review=str(PLAN.relative_to(R)),independent_root_prewrite_integrity_review_sha256=H(PLAN),authorized_by='User explicitly requested all material and Lean4 verification; root serialized sole-writer after all three owners acknowledged HOLD.',corrected_at_utc=now(),historical_source=preserved[page['source']]['path'],historical_source_sha256=page['before_sha256'],preserved_history=str((hist/'preserved-history.json').relative_to(R)),preserved_history_sha256=H(hist/'preserved-history.json'),status='source_corrected_exact_independently_approved_replacements_pending_fresh_correspondence',limits=['No automatic changed-unit or whole exercise promotion. All original review bodies/times and successful/failing execution records remain immutable.']))
 (R/'book/coverage/material-corrections.json').write_text(json.dumps(registry,indent=2)+'\n')
 started=now();run=subprocess.run([sys.executable,'book/inventory_claims.py'],cwd=R,capture_output=True,text=True)
 write(D/'inventory-generator-execution-v1.json',dict(command=[sys.executable,'book/inventory_claims.py'],started_at_utc=started,finished_at_utc=now(),actual_exit_code=run.returncode,stdout=run.stdout,stderr=run.stderr));assert run.returncode==0,run.stderr
 new=load('book/coverage/inventory.json');old=json.loads((hist/'book/coverage/inventory.json').read_text());delta=compare(old,new,{r['source'] for r in p['pages']});assert delta==p['actual_changed_text_keys']
 sim=load(p['actual_full_parser']['simulated_inventory']);assert {k:v for k,v in sim.items() if k!='generated_at_utc'}=={k:v for k,v in new.items() if k!='generated_at_utc'}
 target=R/'book/coverage/inventory-after-correction44.json';assert not target.exists();shutil.copy2(R/'book/coverage/inventory.json',target)
 write(D/'postwrite-source-integrity-v1.json',dict(status='exact_eleven_page_source_batch_and_single_final_inventory_passed',checked_at_utc=now(),actual_exit_code=0,prewrite_plan=str(PLAN.relative_to(R)),prewrite_plan_sha256=H(PLAN),inventory_after=str(target.relative_to(R)),inventory_after_sha256=H(target),registry_after_sha256=H(R/'book/coverage/material-corrections.json'),counts=p['counts'],changed_text_keys=delta,immutable_source33_sha256=H(R/'book/coverage/inventory-after-correction33.json'),protection=protected(),ledger_state='Historical source33 ledgers intentionally held until independently confirmed identity rebases and fresh corrected-source reviews.'))
 print(json.dumps(dict(status='applied',inventory44_sha256=H(target),counts=p['counts'])))
