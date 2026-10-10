from pathlib import Path
import json,hashlib,datetime,copy,sys
R=Path('/home/oxrexkevin/SafetyBased');C=R/'book/coverage';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
op=C/'checks/modules-audit19-source44-additions-v1.json';assert H(op)=='5b1944175c93aeac847780aec4468f13e6122b4161e64eca8b8d4ddbab5a8a01';offer=J(op)
for k in ['module_ledger','module_builder','binding_validator','review_mapping_helper']:assert H(R/offer[k])==offer[k+'_sha256']
for k in ['unchanged_literal_identity_sidecar','canonical_dependency_manifest','proof_selection_manifest','preserved_source33_offer']:
 x=offer[k];assert H(R/x['file'])==x['sha256']
side=J(R/offer['unchanged_literal_identity_sidecar']['file']);mapping=J(C/'checks/modules-future19/review-mappings44-v2.json');assert not mapping['normalization_errors'];assert mapping['unchanged_identity_sidecar']==offer['unchanged_literal_identity_sidecar'];assert H(R/mapping['canonical_path_aliases']['file'])==mapping['canonical_path_aliases']['sha256'];aliases=J(R/mapping['canonical_path_aliases']['file'])['aliases']
def resolve(p):
 x=aliases.get(str(p),{}).get('path',str(p));q=R/x;assert not Path(x).is_absolute() and '..' not in q.parts;return q
def digest(p):return H(resolve(p))
def read(p):return J(resolve(p))
inv=J(R/offer['current_inventory']);assert H(R/offer['current_inventory'])==H(C/'inventory.json')==offer['current_inventory_sha256'];oldinv=read(side['historical_inventory']['file']);assert digest(side['historical_inventory']['file'])==side['historical_inventory']['sha256'];current={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']}
ledger=J(R/offer['module_ledger']);old=read(side['historical_ledger']['preserved']);assert digest(side['historical_ledger']['preserved'])==side['historical_ledger']['sha256'];oldoffer=J(R/offer['preserved_source33_offer']['file']);assert offer['proof_files']==oldoffer['proof_files'];assert offer['required_external_import_dependencies']==oldoffer['required_external_import_dependencies'];assert ledger['proof_files']==old['proof_files'] and ledger['declarations']==old['declarations']
changed_e={x['key']for x in side['changed_owned_literals_excluded']['exercises']};changed_u={x['key']for x in side['changed_owned_literals_excluded']['material_source_units']};scope=set(ledger['scope_pages'])
for section in ['exercises','material_source_units']:
 a={x['key']:x for x in oldinv[section]if x['source']in scope};b={x['key']:x for x in inv[section]if x['source']in scope};assert set(a)==set(b)
 actualchanged={k for k in a if a[k]['source_text']!=b[k]['source_text']};assert actualchanged==(changed_e if section=='exercises'else changed_u)
 listed={x['key']for x in side['unchanged_owned_literals'][section]};assert listed==set(a)-actualchanged
 for k in listed:assert {f:v for f,v in a[k].items()if f!='source_sha256'}=={f:v for f,v in b[k].items()if f!='source_sha256'};assert digest(b[k]['source'])==b[k]['source_sha256']
 for x in side['changed_owned_literals_excluded'][section]:assert x['before']==a[x['key']] and x['after']==b[x['key']]
for path,row in aliases.items():assert digest(row['path'])==row['sha256']
for x in side['original_semantic_review_bodies_times_preserved']:
 assert digest(x['review'])==x['review_sha256'];assert read(x['review']).get('reviewed_at_utc')==x['original_review_time_unchanged']
# Compare every normalized fresh mapping directly to immutable raw semantic rows.
fresh_e={};fresh_u={};review_refs=[];source_checks={}
for entry in mapping['reviews']:
 ref=entry['review'];assert digest(ref['file'])==ref['sha256'];raw=read(ref['file']);assert raw['reviewer']==ref['reviewer'] and raw['reviewed_at_utc']==ref['original_review_time'];assert entry['limits']==raw['limits'];review_refs.append(ref)
 for path,h in raw.get('proof_source_sha256',{}).items():assert digest(path)==h;source_checks[path]=h
 for e in entry['exercises']:
  rr=next(x for x in raw['records']if x['exercise_key']==e['key']);assert not rr['missing_clauses'];assert rr['review_status']=='approved_complete_source';assert rr['exercise_text_sha256']==e['text_sha256']==current[e['key']]['text_sha256'];groups=rr.get('reviewed_components',rr.get('reviewed_clauses',rr.get('components',[])));assert e['components']==groups
  expected_names=rr.get('lean_declarations',list(dict.fromkeys(n for g in groups for n in g.get('lean_declarations',[]))));expected_hyp=rr.get('hypotheses',list(dict.fromkeys(h for g in groups for h in g.get('hypotheses',[]))));assert e['lean_declarations']==expected_names and e['hypotheses']==expected_hyp
  if 'per_exercise_reason'in rr:assert e['reason']==rr['per_exercise_reason']
  else:assert e['reason']=='The independent review separately read the complete question, hint and worked answer; every literal mathematical clause is covered by the exact individually scoped reviewed groups.'
  assert e['key']not in fresh_e;fresh_e[e['key']]=(e,ref,entry['limits'])
 for u in entry['material_units']:
  rr=next(x for x in raw['material_units']if x['source_unit_key']==u['key']);cur=units[u['key']];assert rr['unit_text_sha256']==u['text_sha256']==cur['text_sha256'];assert u['source_sha256']==cur['source_sha256'];assert rr['source_text']==cur['source_text'];assert not rr['missing_clauses']
  assert u['status']==rr['material_status'] and u['lean_declarations']==rr['lean_declarations'] and u['hypotheses']==rr['hypotheses'] and u['reason']==rr['per_unit_reason'];assert u['missing_clauses']==rr['missing_clauses'];assert u['key']not in fresh_u;fresh_u[u['key']]=(u,ref,entry['limits'])
oldex={x['inventory_key']:x for x in old['exercises']};newex={x['inventory_key']:x for x in ledger['exercises']};assert set(oldex)==set(newex);unchanged_ex=0;pending_changed_ex=0
for k,new in newex.items():
 assert new['source_text_sha256']==current[k]['text_sha256'] and new['source_sha256']==current[k]['source_sha256']
 if k in fresh_e:
  row,ref,limits=fresh_e[k];assert new['status']=='complete_math' and new['independent_whole_source_review']==ref;assert len(new['claims'])==1;c=new['claims'][0];assert c['statement_in_prose']==current[k]['source_text'];assert c['status']=='proved' and c['kind']=='independently_reviewed_whole_exercise';assert c['lean_declarations']==row['lean_declarations'] and c['hypotheses']==row['hypotheses'] and c['correspondence']==row['reason'];assert c['remaining_gaps']==[] and c['independent_source_review']==ref and c['scope_limits']==limits
 elif k in changed_e:
  assert new['status']=='pending' and len(new['claims'])==1;c=new['claims'][0];assert c['kind']=='changed_whole_exercise_requires_fresh_source_review' and c['status']=='pending' and c['statement_in_prose']==current[k]['source_text'];assert c['lean_declarations']==[] and c['remaining_gaps'];assert 'independent_whole_source_review'not in new;assert c['id']not in {x['id']for x in oldex[k]['claims']};pending_changed_ex+=1
 else:
  normalized=copy.deepcopy(new);normalized.pop('source44_unchanged_literal_identity');normalized['source_sha256']=oldex[k]['source_sha256'];assert normalized==oldex[k],('unchanged exercise semantic body changed',k);unchanged_ex+=1
oldmat={x['id']:x for x in old['material_claims']};newmat={x['id']:x for x in ledger['material_claims']};assert len(oldmat)==len(old['material_claims']) and len(newmat)==len(ledger['material_claims']);unchanged_material=0;pending_changed_material=0;removed_components=[]
for cid,prior in oldmat.items():
 changed=set(prior['source_unit_keys'])&changed_u;iswhole=next((k for k in changed if cid==k+'::claim-review'),None)
 if changed and not iswhole:
  assert cid not in newmat;removed_components.append(cid);continue
 assert cid in newmat;now=newmat[cid];freshkey=next((k for k in fresh_u if cid==k+'::claim-review'),None)
 if freshkey:
  row,ref,limits=fresh_u[freshkey];assert now['statement_in_prose']==units[freshkey]['source_text'];assert now['status']==row['status'] and now['kind']==row['kind'] and now['lean_declarations']==row['lean_declarations'] and now['hypotheses']==row['hypotheses'];assert now['correspondence']==row['reason'] and now['remaining_gaps']==[] and now['independent_source_review']==ref and now['scope_limits']==limits
 elif iswhole:
  assert now['statement_in_prose']==units[iswhole]['source_text'] and now['status']=='pending' and now['kind']=='changed_whole_material_requires_fresh_source_review';assert now['lean_declarations']==[] and now['remaining_gaps'] and 'independent_source_review'not in now;pending_changed_material+=1
 else:
  z=copy.deepcopy(now);z.pop('source44_unchanged_literal_identity');assert z==prior,('unchanged material semantic body changed',cid);unchanged_material+=1
assert set(newmat)<=set(oldmat)
# Recheck all450 exact original compiler records and raw logs; no compiler rerun.
actual_manifests={};actual_sources={}
def actual_rows(path):
 raw=read(path);rows=raw.get('files',[raw]);assert rows;return rows
def check_actual_record(path,expected=None):
 for row in actual_rows(path):
  source=row.get('file',row.get('source'));sha=row.get('sha256',row.get('source_sha256_after',row.get('sha256_after')));assert row['exit_code']==0 and digest(source)==sha;assert row.get('source_unchanged',True)
  for k in ['sha256_before','source_sha256_before','sha256_after','source_sha256_after']:
   if k in row:assert row[k]==sha
  assert digest(row['log'])==row['log_sha256'];actual_sources[source]=sha
  if expected==source:return row
 return None
for path,h in side['raw_compiler_manifests'].items():assert digest(path)==h;check_actual_record(path);actual_manifests[path]=h
for source,row in side['proof_files'].items():
 assert digest(source)==row['source_sha256'];assert digest(row['compiler_manifest'])==row['compiler_manifest_sha256'];hit=check_actual_record(row['compiler_manifest'],source);assert hit is not None;assert digest(row['raw_log'])==row['raw_log_sha256']==hit['log_sha256']
for source,row in ledger['proof_files'].items():
 e=row['standalone_compile_evidence'];assert digest(source)==row['sha256']==e['sha256'];assert e['exit_code']==0 and e['source_unchanged'];assert digest(e['log'])==e['log_sha256']
for source,row in offer['proof_files'].items():
 assert digest(source)==row['sha256'];assert row['actual_exit_code']==0;assert digest(row['compiler_manifest'])==row['compiler_manifest_sha256'];assert check_actual_record(row['compiler_manifest'],source)is not None;assert digest(row['raw_log'])==row['raw_log_sha256'];assert row['declarations']==ledger['proof_files'][source]['declarations']
 for path,h in row['evidence_sha256'].items():assert digest(path)==h
# Bind all51 exact external imports to actual owner/baseline evidence, separately from ownership.
selection=J(R/'reports/full-coverage/checkpoint-18-selection.json');base=selection['proof_files'];ap=J(C/'applied-audit19-source44-additions-v1.json');aprows={r['source']:r for r in ap['modules']};fp=C/'foundations-audit19-source44-additions-v1.json';fnd=J(fp);external={}
for source,h in offer['required_external_import_dependencies'].items():
 assert digest(source)==h
 if source in base:
  r=base[source];assert r['sha256']==h
  for path,sha in r['evidence_sha256'].items():assert digest(path)==sha
  external[source]={'scope':'actual selected source-matched baseline evidence retained','evidence_sha256':r['evidence_sha256']}
 elif source in aprows:
  r=aprows[source];assert r['source_sha256']==h and r['exit_code']==0 and r['sha256_before']==r['sha256_after']==h;assert digest(r['standalone_evidence'])==r['standalone_evidence_sha256'] and digest(r['log'])==r['log_sha256'];external[source]={'scope':'actual immutable passing Applied owner evidence','owner_offer':'book/coverage/applied-audit19-source44-additions-v1.json','owner_offer_sha256':H(C/'applied-audit19-source44-additions-v1.json'),'standalone_evidence':r['standalone_evidence'],'standalone_evidence_sha256':r['standalone_evidence_sha256'],'raw_log':r['log'],'raw_log_sha256':r['log_sha256']}
 else:
  r=fnd['proof_files'][source];assert r['sha256']==h and r['exit_code']==0 and r['source_unchanged']
  for path,sha in r['evidence_sha256'].items():assert digest(path)==sha
  external[source]={'scope':'actual immutable passing Foundations owner evidence','owner_offer':str(fp.relative_to(R)),'owner_offer_sha256':H(fp),'evidence_sha256':r['evidence_sha256']}
# Independently verify the complete transitive import source closure of the272 new files.
closure=set()
def visit(source):
 if source in closure:return
 closure.add(source);lines=resolve(source).read_text().splitlines()
 for line in lines:
  if not line.startswith('import '):continue
  for imp in line.split()[1:]:
   if not imp.startswith('SafeLearning.'):continue
   dep='verification/lean/'+imp.replace('.','/')+'.lean';assert dep in base or dep in offer['proof_files'] or dep in offer['required_external_import_dependencies'],(source,dep);visit(dep)
for source in offer['proof_files']:visit(source)
# The existing guard is exercised read-only as a supplementary runtime check;
# exact raw row normalization and unchanged semantics were independently compared above.
sys.path.insert(0,str(C));from modules_binding19_source44 import check_bindings
guard=check_bindings(R,ledger,inv,old,side,mapping);assert guard['status']=='exact_current44_unchanged_literal_fresh_review_and_actual_execution_bindings_passed'
dep=J(R/offer['canonical_dependency_manifest']['file'])
for row in dep['artifacts']:assert digest(row['path'])==row['sha256'] and resolve(row['path']).stat().st_size==row['size_bytes']
protected={}
for p,r in base.items():protected[p]=r['sha256'];protected.update(r['evidence_sha256'])
for p,h in protected.items():assert digest(p)==h
manifest=J(R/'reports/full-coverage/checkpoint-18-manifest.json')
for p,h in manifest['frozen_inputs_sha256'].items():assert digest(str(Path(manifest['snapshot'])/p))==h
# Keep every relevant source/owner offered metadata immutable throughout this read-only check.
held={str(p.relative_to(R)):H(p)for p in [op,R/offer['module_ledger'],R/offer['module_builder'],R/offer['binding_validator'],C/'applied.json',C/'applied-promotions.json',C/'build_applied_ledger.py',C/'applied-audit19-source44-additions-v1.json']}
assert held['book/coverage/applied.json']=='034a03cf1d566079a76553149c1c0c71013f76f0f8e4ee34483503564bd371e8'
out={'schema_version':1,'status':'independent_exact_final_modules_source44_mapping_history_actual_evidence_and_offer_confirmation_passed','reviewer':'/root/applied_next','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inventory':offer['current_inventory'],'inventory_sha256':offer['current_inventory_sha256'],'module_offer':str(op.relative_to(R)),'module_offer_sha256':H(op),'module_ledger':offer['module_ledger'],'module_ledger_sha256':H(R/offer['module_ledger']),'builder':offer['module_builder'],'builder_sha256':H(R/offer['module_builder']),'binding_validator':offer['binding_validator'],'binding_validator_sha256':H(R/offer['binding_validator']),'current_identity_sidecar':offer['unchanged_literal_identity_sidecar'],'fresh_mapping':{'file':'book/coverage/checks/modules-future19/review-mappings44-v2.json','sha256':H(C/'checks/modules-future19/review-mappings44-v2.json')},'original_source33_ledger_preserved':side['historical_ledger'],'original_source33_offer_preserved':offer['preserved_source33_offer'],'counts':{'exercises':len(ledger['exercises']),'changed_exercise_literals_excluded_before_fresh_review':len(changed_e),'changed_material_literals_excluded_before_fresh_review':len(changed_u),'exact_raw_fresh_or_new_review_records':len(review_refs),'fresh_whole_exercise_rows':len(fresh_e),'fresh_material_rows':len(fresh_u),'unchanged_nonfresh_exercise_semantic_bodies_exact':unchanged_ex,'unchanged_nonfresh_material_semantic_bodies_exact':unchanged_material,'changed_nonfresh_exercises_correctly_pending':pending_changed_ex,'changed_nonfresh_whole_material_correctly_pending':pending_changed_material,'changed_old_material_component_rows_excluded':len(removed_components),'all_original_proof_records_exact':len(ledger['proof_files']),'exact_new_offered_proof_rows':len(offer['proof_files']),'exact_external_import_sources':len(external),'all_transitive_import_sources':len(closure),'canonical_dependency_artifacts_rehashed':len(dep['artifacts']),'historical_raw_reviews_and_original_times_rehashed':len(side['original_semantic_review_bodies_times_preserved']),'protected_selected_sources':len(base),'protected_source_evidence_paths':len(protected),'frozen18_inputs':len(manifest['frozen_inputs_sha256'])},'current_ledger_counts':ledger['counts'],'exact_fresh_mapping_raw_review_refs':review_refs,'external_actual_evidence':external,'excluded_original_changed_components':removed_components,'held_metadata_sha256':held,'preserved_initial_checker_failure':{'helper':'/tmp/applied-check-final-modules-source44-mapping-offer19-v1-first-failed.py','helper_sha256':H(Path('/tmp/applied-check-final-modules-source44-mapping-offer19-v1-first-failed.py')),'actual_exit_code':1,'reason':'The initial reader sorted union-derived hypothesis lists. The immutable mapping correctly retains first-occurrence order from its exact raw groups. The corrected independent reader uses first-occurrence de-duplication; all names/hypothesis contents were already exact.'},'limits':['Mechanical confirmation only. Existing independently completed semantic review bodies/times/hypotheses/declarations/statuses remain the mathematical correspondence evidence; this check creates no new semantic whole approval.','Every unchanged nonfresh exercise/material semantic body equals its exact source33 original after removing only explicit44 provenance/source identity. Changed original clauses are excluded and only independently fresh exact source reviews restore approved scope.','All450 original proof records and272 offered rows/51 import hashes remain unchanged. Actual retained compiler source/log identities were checked; no new compiler or aggregate/kernel/axiom execution is claimed.','The old module global actual1 record is retained honestly as an earlier cross-owner state; final combined current44 global checks/root freeze remain separate.','All outputs of this independent audit remain under /tmp; no owner ledger/helper/offer/HTML/inventory/proof or historical evidence is changed.']}
q=Path('/tmp/modules-final44-mappings-offer-independent-applied-confirmation19-v1.json');assert not q.exists();q.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(q,H(q),json.dumps(out['counts']))
