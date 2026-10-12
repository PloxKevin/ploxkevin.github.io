from pathlib import Path
import json,hashlib,datetime,re,sys,shutil,importlib.util
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();BH=lambda b:hashlib.sha256(b).hexdigest();started=datetime.datetime.now(datetime.timezone.utc).isoformat()
pp=Path('/tmp/foundations-nonlinear-state-rounding-proposal19.json');assert H(pp)=='b0c5941f875c50bcfef457105ebe4c33f1a50a55795421b67c41ab1e30239f4f';p=json.loads(pp.read_text());before=(R/p['source']).read_bytes();assert BH(before)==p['source_sha256_before']==H(p['source_bytes_before_snapshot'])
rep=p['replacements'];assert len(rep)==1;r=rep[0];assert r['count']==1 and before.count(r['before'].encode())==1
expected=r['before'].replace('$x_{10}=0.209$','$x_{10}\\approx0.209$').replace('$x_{100}=0.0700$','$x_{100}\\approx0.0700$').replace('$x_{1000}=0.0223$','$x_{1000}\\approx0.0223$');assert r['after']==expected
after=before.replace(r['before'].encode(),r['after'].encode(),1);assert BH(after)==p['proposed_source_sha256_after']==H(p['source_bytes_proposed_after_snapshot']) and after==Path(p['source_bytes_proposed_after_snapshot']).read_bytes();assert after.replace(r['after'].encode(),r['before'].encode(),1)==before and before.count(b'\n')==after.count(b'\n')
sys.path.insert(0,str(R/'book'));from validate import Document
ad,bd=Document(before.decode()),Document(after.decode());assert len(ad.nodes)==len(bd.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(ad.nodes,bd.nodes))
ip=R/p['inventory_at_preparation'];assert H(ip)==p['inventory_sha256_at_preparation'];I=json.loads(ip.read_text());sim=Path('/tmp/modules-independent-foundations-nonlinear408-proposal19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for f in (R/'SafeLearning').glob('*.html'):shutil.copyfile(f,sim/'SafeLearning'/f.name)
(sim/p['source']).write_bytes(after)
spec=importlib.util.spec_from_file_location('independent_nonlinear408_inventory',R/'book/inventory_claims.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.ROOT=sim;m.OUT=sim/'book/coverage';m.inventory();np=m.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts'];delta={}
for field in ['exercises','material_source_units']:
 A={u['key']:u for u in I[field]};B={u['key']:u for u in N[field]};assert A.keys()==B.keys();delta[field]=[]
 for k,a in A.items():
  b=B[k];assert a.keys()==b.keys()
  for f in a:
   if f not in ['source_sha256','source_text','text_sha256']:assert a[f]==b[f],(k,f)
  if a['source_text']!=b['source_text']:delta[field].append(k)
  else:assert a['text_sha256']==b['text_sha256']
  if a['source']!=p['source']:assert a==b
assert delta=={'exercises':[],'material_source_units':['primer-basics.html::node-408']}
for f,h in p['actual_proof_source_sha256'].items():assert H(R/f)==h
for e in p['actual_standalone_evidence']:
 assert H(e['compiler_manifest'])==e['compiler_manifest_sha256'];r=e['raw_execution_record'];assert r['exit_code']==0 and r['source_unchanged'] and H(R/r['source'])==r['source_sha256_before']==r['source_sha256_after']==H(r['preserved_source']);assert H(r['log'])==r['log_sha256'] and Path(r['log']).stat().st_size==0
rv=Path('/tmp/foundations-nonlinear-contraction-material-source-components-review19-v3-numerics.json');assert H(rv)=='0b8d8661c2959bef46f465ed8b48014f4bd9a0988287b570570ce190b389f8ae'
mp=R/'reports/full-coverage/checkpoint-18-manifest.json';cm=json.loads(mp.read_text());paths={}
for f,row in cm['proof_files'].items():
 paths[f]=row['sha256'];assert H(R/f)==row['sha256']
 for f,h in row['evidence_sha256'].items():paths[f]=h;assert H(R/f)==h
for f,h in cm['frozen_inputs_sha256'].items():assert H(R/cm['snapshot']/f)==h
assert len(cm['proof_files'])==490 and len(paths)==565 and len(cm['frozen_inputs_sha256'])==2431
assert BH((R/p['source']).read_bytes())==p['source_sha256_before'] and H(ip)==p['inventory_sha256_at_preparation']
out={'schema_version':1,'status':'approved_exact_readonly_numerical_precision_proposal_not_applied','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proposal':str(pp),'proposal_sha256':H(pp),'original_prepared_at_utc_preserved':p['prepared_at_utc'],'exact_source_and_inventory':{'source':p['source'],'before_sha256':BH(before),'proposed_after_sha256':BH(after),'inventory':p['inventory_at_preparation'],'inventory_sha256':H(ip)},'independent_fresh_full_parser':{'actual_command':['python3','/tmp/review-foundations-nonlinear408-proposal19.py'],'started_at_utc':started,'actual_generator_completed':True,'expected_terminal_exit_code':0,'simulated_inventory':str(np),'simulated_inventory_sha256':H(np),'exercises_checked':556,'material_units_checked':12774,'actual_delta':delta,'all_keys_locators_lines_tags_attributes_order_and_other_fields_unchanged':True,'every_other_page_exact':True},'semantic_decision':{'review_status':'approved_precise_source_correction_proposal','hypotheses':p['hypotheses'],'missing_clauses':[],'per_clause_reason':'Read complete literal408 and proposed paragraph; exactly three equality tokens become approximation tokens. Independently read genuine1000-step Nat/real interval proof and actual positive-orbit reciprocal/Cesaro asymptotic route, with exact passing records/logs. Actual x10<.209,x100>.0700,x1000>.0223 proves each equality false; true nearest3/4-place enclosures support each replacement. All other statements/formulas remain byte-for-byte untouched.','new_precise_numeric_review':str(rv),'new_precise_numeric_review_sha256':H(rv)},'actual_proof_source_sha256':p['actual_proof_source_sha256'],'actual_standalone_evidence':p['actual_standalone_evidence'],'preservation_check':{'manifest_sha256':H(mp),'selected_proof_files':490,'selected_unique_source_and_evidence_paths':565,'frozen_inputs':2431,'all_hashes_exact':True},'limits':['TMP-only during HOLD33; no live HTML/inventory/coverage/index mutation.','No serial assigned; root serialization and authorization remain required. A fresh whole literal review after actual application remains separate.','Original proposal/preparation time, precise reviews/bodies/times and all passing/failed source/compiler/log artifacts unchanged.','Actual standalone0 evidence verified; no new aggregate/kernel/browser result inferred.']}
fp=Path('/tmp/modules-foundations-nonlinear408-rounding-independent-proposal-review19.json');assert not fp.exists();fp.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'path':str(fp),'sha256':H(fp),'fresh_parser_delta':delta,'live_unchanged':True},indent=2))
