from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys,copy,collections
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
cache={}
def path(p):
 p=Path(p);return p if p.is_absolute() else R/p
def sha(p):
 p=path(p);s=p.stat();k=(str(p),s.st_size,s.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def read(p):return json.loads(path(p).read_text())
B='book/coverage/checks/modules-future22/source48/'
offerpath=B+'modules-audit22-candidate-source48-additions-v1.json';assert sha(offerpath)=='c36cd04a784c529864cb3d1ba1a2a23b164e5848fdf56ad9002aa7a5731282b2'
offer=read(offerpath);cand=read(offer['module_ledger']);assert sha(offer['module_ledger'])==offer['module_ledger_sha256']=='1e9083449d1eb090fe3e5b524a941b8398b55bb60cd596950c1130861d1ac963'
inp=read(B+'nn-two-practices-input-bindings-v1.json');old=read(inp['baseline_owner_assets']['book/coverage/modules.json']['preserved'])
for p,z in inp['baseline_owner_assets'].items():assert sha(p)==sha(z['preserved'])==z['sha256']
assert inp['baseline_owner_assets']==offer['baseline21_owner_assets']
assert sha(offer['module_builder'])==offer['module_builder_sha256']=='baf0e1ddb61753b292ddd88912a4bc76e4a924fc911da546d46b69906b423bba'
be=read(offer['actual_builder']['file']);assert sha(offer['actual_builder']['file'])==offer['actual_builder']['sha256'] and be['actual_exit_code']==0
assert be['helper_sha256_before']==be['helper_sha256_after']==offer['module_builder_sha256'];assert sha(be['log'])==be['log_sha256']
guard=read(offer['current_identity_binding_validation']['file']);assert sha(offer['current_identity_binding_validation']['file'])==offer['current_identity_binding_validation']['sha256']
inv=read(inp['inventory']);assert sha(inp['inventory'])==inp['inventory_sha256']==sha('book/coverage/inventory.json')=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
es={e['key']:e for e in inv['exercises']};us={u['key']:u for u in inv['material_source_units']}
rev=read(inp['review']['file']);assert sha(inp['review']['file'])==sha(inp['review']['original_tmp_path'])==inp['review']['sha256']=='1219b4845d8fdde4fc116b246ac04beebcc22996fd4067c5a4ec0b6888e61cfc'
assert rev['reviewed_at_utc']==inp['review']['original_review_time'];assert offer['original_full_source_review']==inp['review']
aliases=read(inp['canonical_path_aliases']['file'])['aliases'];assert sha(inp['canonical_path_aliases']['file'])==inp['canonical_path_aliases']['sha256']
for src,z in aliases.items():assert sha(src)==sha(z['path'])==z['sha256']
src=inp['source'];assert sha(src)==inp['sha256']=='72bb8711287fa16c93cd227663390d8370f59e788ad961704f0b97254ba7103b'
names=[d['name'] for d in declarations(path(src).read_text()) if d['kind'] in ['theorem','lemma']];assert len(names)==9
actual=[]
for z in inp['actual_execution_records']:
 p=z['record']['file'];r=read(p);assert sha(p)==z['record']['sha256'];assert r['actual_exit_code']==0 and r['source_sha256_before']==r['source_sha256_after']==sha(src)
 assert sha(z['raw_log']['path'])==r['log_sha256']==z['raw_log']['sha256'];assert sha(z['source_snapshot']['path'])==sha(src)
 assert aliases[r['log']]['path']==z['raw_log']['path'];assert sha(r['source_snapshot'])==sha(src)
 actual.append({'file':p,'sha256':sha(p),'actual_exit_code':0,'raw_log_sha256':r['log_sha256'],'source_sha256':sha(src)})
assert len(actual)==2
oe={r['inventory_key']:r for r in old['exercises']};ne={r['inventory_key']:r for r in cand['exercises']};om={r['id']:r for r in old['material_claims']};nm={r['id']:r for r in cand['material_claims']}
assert len(oe)==len(ne)==217 and len(om)==len(nm)==5183
expected_review={'file':inp['review']['file'],'sha256':inp['review']['sha256'],'original_review_time':rev['reviewed_at_utc'],'reviewer':rev['reviewer']}
fresh=[];freshu=[]
for e in rev['records']:
 k=e['exercise_key'];fresh.append(k);assert e['entire_inventory_record']==es[k] and e['whole_exercise_approved'] and e['missing_clauses']==[]
 n=ne[k];assert n['status']=='complete_math' and n['independent_whole_source_review']==expected_review and len(n['claims'])==1
 c=n['claims'][0];assert c['statement_in_prose']==es[k]['source_text'] and c['lean_declarations']==e['lean_declarations'] and c['hypotheses']==e['hypotheses'] and c['remaining_gaps']==[] and c['status']=='proved' and c['independent_source_review']==expected_review and c['scope_limits']==rev['limits']
 a=copy.deepcopy(n);a.pop('independent_whole_source_review');a['claims']=oe[k]['claims'];a['status']=oe[k]['status'];assert a==oe[k]
 for u in e['material_units']:
  key=u['source_unit_key'];freshu.append(key);assert u['entire_inventory_record']==us[key] and u['missing_clauses']==[]
  k=key+'::claim-review';n=nm[k];o=om[k]
  assert n['statement_in_prose']==us[key]['source_text'] and n['status']==u['material_status'] and n['lean_declarations']==u['lean_declarations'] and n['hypotheses']==u['hypotheses'] and n['correspondence']==u['per_unit_reason'] and n['remaining_gaps']==[] and n['independent_source_review']==expected_review and n['scope_limits']==rev['limits']
  a=copy.deepcopy(n)
  for f in ['statement_in_prose','status','kind','lean_declarations','hypotheses','correspondence','remaining_gaps']:
   a[f]=o[f]
  a.pop('independent_source_review');a.pop('scope_limits');assert a==o
assert fresh==offer['fresh_whole_exercise_keys'] and freshu==offer['fresh_material_unit_keys'] and len(freshu)==len(set(freshu))==12
for k in oe:
 if k not in fresh:assert oe[k]==ne[k]
for k in om:
 if k not in {u+'::claim-review' for u in freshu}:assert om[k]==nm[k]
assert {k:v for k,v in cand['proof_files'].items() if k!=src}==old['proof_files'] and len(old['proof_files'])==467 and len(cand['proof_files'])==468
assert cand['declarations'][:len(old['declarations'])]==old['declarations'];assert [d['name'] for d in cand['declarations'][len(old['declarations']):]]==names
for d in cand['declarations'][len(old['declarations']):]:assert d['file']==src and d['statement'] in path(src).read_text()
assert cand['proof_files'][src]['declarations']==names and cand['proof_files'][src]['standalone_compile_evidence']['compiler_manifest']==actual[0]['file']
for p,z in offer['proof_files'].items():
 assert sha(p)==z['sha256']
 for a,h in z['evidence_sha256'].items():assert sha(a)==h
for p,h in offer['required_external_import_dependencies'].items():assert sha(p)==h
assert offer['required_external_import_dependencies']==old['required_external_import_dependencies']
before=copy.deepcopy(cand)
for f in ['generated_at_utc','exercises','material_claims','proof_files','declarations','counts','reviewed_work_integration22_candidate']:before.pop(f,None)
baseline=copy.deepcopy(old)
for f in ['generated_at_utc','exercises','material_claims','proof_files','declarations','counts']:baseline.pop(f,None)
assert before==baseline
m=read('reports/full-coverage/checkpoint-21-manifest.json');assert len(m['proof_files'])==1089 and len(m['frozen_inputs_sha256'])==32040
for p,z in m['proof_files'].items():
 assert sha(p)==z['sha256']
 for a,h in z['evidence_sha256'].items():assert sha(a)==h
for a,h in m['frozen_inputs_sha256'].items():assert sha(str(Path(m['snapshot'])/a))==h
out=Path('/tmp/modules-source48-nn-candidate22-independent-applied-mechanical-confirmation-v1.json');assert not out.exists()
r={'schema_version':1,'status':'independent_isolated_candidate_mapping_and_history_mechanics_passed','reviewer':'/root/applied_next','checked_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_offer':{'file':offerpath,'sha256':sha(offerpath)},'candidate_ledger':{'file':offer['module_ledger'],'sha256':sha(offer['module_ledger'])},'actual_original_builder':{'file':offer['actual_builder']['file'],'sha256':sha(offer['actual_builder']['file']),'actual_exit_code':0},'builder_helper_sha256':sha(offer['module_builder']),'original_review':inp['review'],'original_review_body_and_time_unchanged':True,'counts':{'exact_current_inventory_exercise_rows':217,'exact_owned_material_claim_rows':5183,'whole_exercises_mapped':2,'physical_units_mapped':12,'old_exercises_exact':215,'old_material_claim_bodies_exact':5171,'old_proof_rows_exact':467,'candidate_proof_rows':468,'new_immutable_owned_sources':1,'new_public_theorems':9,'actual_zero_canonical_execution_records':2,'selected21_sources_exact':1089,'frozen21_inputs_exact':32040},'fresh_exercise_keys':fresh,'fresh_physical_unit_keys':freshu,'actual_paired_records':actual,'live21_owner_assets_exact':inp['baseline_owner_assets'],'independent_checker':'/tmp/check-module22-nn-candidate-independent-applied-v1.py','independent_checker_sha256':sha('/tmp/check-module22-nn-candidate-independent-applied-v1.py'),'scope':['Mechanical confirmation only: no new semantic review, compiler execution, builder rerun or live global22 validation is claimed.','The original full review body/time and all original TMP/canonical compiler/log/snapshot bytes agree via explicit aliases. The isolated candidate changes exactly the two reviewed wholes and twelve individual units; old semantic bodies/declaration prefix are preserved.','The actual original ledger has467 prior proof rows and5183 material claim rows; thus5171 unchanged material bodies remain. Earlier informal counts468 old proofs/4965 material were corrected against actual artifacts, not inferred.','All held21 live owner assets and selected/frozen21 inputs remain byte-exact. Mutable live root progress/README are excluded from immutable guards; their frozen snapshot counterparts are checked.'],'errors':[]}
out.write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'file':str(out),'sha256':sha(out),'counts':r['counts']}))
