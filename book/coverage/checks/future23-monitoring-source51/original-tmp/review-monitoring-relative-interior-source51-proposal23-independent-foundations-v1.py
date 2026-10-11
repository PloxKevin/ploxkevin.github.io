from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json,re,shutil,sys,traceback
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
REQUEST=TMP/'applied-monitoring-relative-interior-source51-precision-proposal23-v1.json'
OUT=TMP/'monitoring-relative-interior-source51-proposal23-independent-foundations-semantic-review-v1.json'
FAIL=TMP/'monitoring-relative-interior-source51-proposal23-independent-foundations-checker-failure-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p

def simulate(q,baseline_inventory,baseline_tree,label):
 source=q['source'];original=(baseline_tree/source).read_bytes();assert hashlib.sha256(original).hexdigest()==q['source_sha256_before']
 after=original
 for row in q['replacements']:
  a,b=row['before'].encode(),row['after'].encode()
  assert after.count(a)==1 and b'\n' not in a and b'\n' not in b and row['count']==1
  after=after.replace(a,b,1)
 reverse=after
 for row in reversed(q['replacements']):
  a,b=row['before'].encode(),row['after'].encode();assert reverse.count(b)==1;reverse=reverse.replace(b,a,1)
 assert reverse==original and after.count(b'\n')==original.count(b'\n')
 assert hashlib.sha256(after).hexdigest()==q['proposed_source_sha256_after']
 from validate import Document
 old_doc,new_doc=Document(original.decode()),Document(after.decode())
 assert len(old_doc.nodes)==len(new_doc.nodes)
 assert [(n.tag,n.attrs,n.line) for n in old_doc.nodes]==[(n.tag,n.attrs,n.line) for n in new_doc.nodes]
 sim=TMP/f'foundations-independent-monitoring-relative-interior23-{label}-simulation-v1'
 assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
 for p in (baseline_tree/'SafeLearning').glob('*.html'):
  shutil.copyfile(p,sim/'SafeLearning'/p.name)
 (sim/source).write_bytes(after)
 spec=importlib.util.spec_from_file_location('foundation_precision_inventory_'+label,ROOT/'book/inventory_claims.py')
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=sim;module.OUT=sim/'book/coverage';module.inventory()
 parsed=read(module.OUT/'inventory.json');assert parsed['counts']==baseline_inventory['counts']
 assert len(parsed['source_sha256'])==len(baseline_inventory['source_sha256'])==29
 assert set(parsed['source_sha256'])==set(baseline_inventory['source_sha256'])
 assert {n for n in parsed['source_sha256'] if parsed['source_sha256'][n]!=baseline_inventory['source_sha256'][n]}=={source}
 changes={}
 for section in ('exercises','material_source_units'):
  old={r['key']:r for r in baseline_inventory[section]};new={r['key']:r for r in parsed[section]}
  assert old.keys()==new.keys();changed=[]
  for key,a in old.items():
   b=new[key];assert a.keys()==b.keys()
   assert all(a[f]==b[f] for f in a if f not in {'source_sha256','source_text','text_sha256'}),(label,key)
   if a['source_text']!=b['source_text']:changed.append(key)
   else:assert a['text_sha256']==b['text_sha256']
   if a['source']!=source:assert a==b
  changes[section]=changed
 assert changes==q['expected_changed_text_keys']
 return {'baseline':label,'actual_fresh_full29_page_parser_completed':True,'simulation_inventory':ref(module.OUT/'inventory.json'),'only_changed_literal_keys':changes,'all_keys_lines_attributes_locators_and_other_fields_exact':True,'DOM_signature_exact':True,'unique_forward_reverse_and_newline_bytes_exact':True}

def main():
 assert not OUT.exists() and not FAIL.exists() and sha(REQUEST)=='bc08943551405c66ad3256ee0230f788d89e01aba2e8203a780c0e4689cfd40a'
 q=read(REQUEST);inv=read(check(q['current_authoritative_inventory']));current_sha=sha(ROOT/'book/coverage/inventory.json')
 assert current_sha==q['current_authoritative_inventory']['sha256']=='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
 assert next(r for r in inv['exercises'] if r['key']=='cmdp.html::exercise-21')==q['entire_original_exercise']
 assert next(r for r in inv['material_source_units'] if r['key']=='cmdp.html::node-1138')==q['entire_original_material_record']
 for n,h in inv['source_sha256'].items():assert sha(ROOT/n)==h
 assert len(q['replacements'])==1
 change=q['replacements'][0];assert change['before']=='is an interior point' and change['after']=='lies in the relative interior of the quadrilateral in the plane $V_0+V_1+V_2=1$'
 assert change['source_unit_key']=='cmdp.html::node-1138' and q['whole_current_or_proposed_unit_approved'] is False and q['whole_exercise_approved'] is False
 source=check(q['precise_proof_source']);text=source.read_text();assert sha(source)=='b6c91e28a41d20750254cff2451d82a6ac345d561cea96586629d22978b9b296'
 assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 names=['SafeLearning.CompleteMonitoringExposedInterior23.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)];assert len(names)==6
 original_peer=read(check(q['new_independent_six_body_review']));assert original_peer['errors']==[] and 'passed' in original_peer['status']
 assert original_peer['proof_source']==q['precise_proof_source'] and original_peer['public_theorem_count']==6 and original_peer['material_units'][0]['entire_inventory_record']==q['entire_original_material_record']
 actual=read(check(q['genuine_actual_standalone_record']));assert actual==original_peer['entire_original_actual_standalone_record'] and actual['exit_code']==0
 assert actual['source_sha256']==sha(source) and actual['command']==['lake','env','lean',str(source)]
 assert check(original_peer['raw_log']).stat().st_size==0 and original_peer['raw_log']['sha256']==actual['log_sha256']
 runner=check(original_peer['actual_original_runner']);assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in runner.read_text()
 for dep in original_peer['full_dependencies_read']:check(dep)
 check(q['actual_preparer']);prepared=read(check(q['full29_page_parser']['proposed_inventory']))
 sys.path.insert(0,str(ROOT/'book'));simulation=simulate(q,inv,ROOT,'authoritative-source50')
 fresh=read(Path(simulation['simulation_inventory']['file']))
 assert fresh['exercises']==prepared['exercises'] and fresh['material_source_units']==prepared['material_source_units'] and fresh['source_sha256']==prepared['source_sha256']
 assert next(r for r in fresh['material_source_units'] if r['key']=='cmdp.html::node-1138')==q['proposed_material_record']
 assert fresh['source_sha256']['SafeLearning/lyapunov-mpc.html']=='228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'
 manifest=read(check(q['protected_selected22']['manifest']));assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 assert sha(ROOT/'book/coverage/inventory.json')==current_sha and sha(ROOT/q['source'])==q['source_sha256_before']
 result={'status':'passed_independent_one_phrase_source51_relative_interior_semantics_and_fresh_full29_parser_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'request':ref(REQUEST),'original_proposal_prepared_at_utc':q['prepared_at_utc'],'source':q['source'],'source_sha256_before':q['source_sha256_before'],'proposed_source_sha256_after':q['proposed_source_sha256_after'],'exact_original_single_replacement':change,'semantic_decision':{'proposal_text_approved':True,'hypotheses':['Achievable fraction polytope has nonnegative coordinates, sum1 and V0<=1/2.','The ambient affine plane is exactly V0+V1+V2=1; primal optimum coordinates are all1/3.'],'reason':'The complete actual radius1/12 coordinate-neighborhood proof places every sum1 point sufficiently close to(1/3,1/3,1/3) in the achievable polytope: each coordinate remainspositive and V0<1/2. This is a relatively open product-coordinate neighborhood in the affine sum1 plane, so the proposed relative-interior wording is correct. The quadrilateral has empty ambient R3 interior because it is contained in that proper plane. The six full geometric bodies and definitions derive affine L, true convexity, exposed-to-extreme and four actual exposed/extreme vertices; existing full geometry/face bodies supply the four-weight quadrilateral and affine maximizing classification.','missing_clauses':[],'scope':'Only the exact interior-to-relative-interior phrase is approved; no new complete(b) or full exercise decision is inferred.'},'full_geometric_source_and_all_six_bodies_read':text,'geometric_proof_source':q['precise_proof_source'],'original_geometric_peer':{'reference':q['new_independent_six_body_review'],'entire_original_body_and_time':original_peer},'entire_original_actual_standalone_record':actual,'original_actual_runner':original_peer['actual_original_runner'],'actual_EMPTY_log':original_peer['raw_log'],'source_identity_scope':'Original Root trial record supplies its genuine post-run source hash; no unavailable before-run hash is claimed.','full_source50_exercise_and_unit_context_read':[q['entire_original_exercise'],q['entire_original_material_record']],'proposed_material_record':q['proposed_material_record'],'actual_independent_fresh_full29_page_parser':simulation,'all_other_28_HTML_pages_and_source50_Lyapunov_corrections_exact':True,'only_changed_literal_keys':q['expected_changed_text_keys'],'all1113_selected22_proof_sources_exact':True,'whole_material_unit_or_exercise_approved':False,'coverage_complete':False,'working_HTML_inventory_or_ledgers_written':False,'limits':['No actual source51 correction number or HTML/inventory write is assigned by this peer.','One exact phrase is mathematically qualified; all policy, selector, transient-route, expected/a.s. and A3 wording is retained byte-exact.','Fresh full29 parser independently reproduces the preparer output with exact keys/lines/attributes/DOM/unique reverse/newline bytes. Current50 is authoritative and preserved.','Earlier geometric peer body/time, failed/passing proof history and prior source49/source50 semantic bodies are not rewritten. Only new TMP simulation/checker/review files are written.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':ref(OUT),'changed_keys':q['expected_changed_text_keys'],'fresh_full29_parser':True}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg},indent=2)+'\n')
  sys.stderr.write(msg);sys.exit(1)
