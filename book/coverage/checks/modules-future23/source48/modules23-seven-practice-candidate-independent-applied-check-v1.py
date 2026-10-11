from pathlib import Path
from datetime import datetime,timezone
import sys,json,hashlib,copy,collections,re,ast
ROOT=Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
sha=lambda p:hashlib.sha256((ROOT/p if not Path(p).is_absolute() else Path(p)).read_bytes()).hexdigest()
read=lambda p:json.loads((ROOT/p if not Path(p).is_absolute() else Path(p)).read_text())
base='book/coverage/checks/modules-future23/source48/'
offer_path=base+'modules-audit23-candidate-source48-additions-v1.json'
assert sha(offer_path)=='199d3e38a18a5a12a03148ab2d931c3771ad5feceb7a8007b884e92a55cda12e'
offer=read(offer_path)
candidate=read(offer['module_ledger']);assert sha(offer['module_ledger'])==offer['module_ledger_sha256']
builder=ROOT/offer['module_builder'];assert sha(builder)==offer['module_builder_sha256'];ast.parse(builder.read_text())
actual=read(offer['actual_builder']['file']);assert sha(offer['actual_builder']['file'])==offer['actual_builder']['sha256']
assert actual['actual_exit_code']==offer['actual_builder']['actual_exit_code']==0
assert actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']==sha(builder)
assert actual['actual_command']==['python3',str(builder)] and actual['actual_workdir']==str(ROOT)
assert sha(offer['actual_builder_raw_log']['file'])==actual['log_sha256']==offer['actual_builder_raw_log']['sha256']
assert sha(actual['log'])==actual['log_sha256']
guardref=offer['current_identity_binding_validation'];guard=read(guardref['file']);assert sha(guardref['file'])==guardref['sha256']
inp_ref=guard['input_bindings'];inp=read(inp_ref['file']);assert sha(inp_ref['file'])==inp_ref['sha256']=='7b3627e722c30c988e3049e2bcebc83dd80fddcc7aba67d45e94ef3880cf46fb'
original_ref=inp['baseline22_module_ledger'];original=read(original_ref['file']);assert sha(original_ref['file'])==original_ref['sha256']==sha(inp['baseline22_live_module_ledger']['file'])
assert len(original['proof_files'])==469
inv=read(inp['inventory']);assert sha(inp['inventory'])==inp['inventory_sha256']==offer['current_inventory_sha256']==sha('book/coverage/inventory.json')
es={x['key']:x for x in inv['exercises']};us={x['key']:x for x in inv['material_source_units']}
ce={x['inventory_key']:x for x in candidate['exercises']};oe={x['inventory_key']:x for x in original['exercises']}
cu={x['id']:x for x in candidate['material_claims']};ou={x['id']:x for x in original['material_claims']}
assert set(ce)==set(oe) and set(cu)==set(ou)
aliases_ref=inp['canonical_path_aliases'];aliases=read(aliases_ref['file'])['aliases'];assert sha(aliases_ref['file'])==aliases_ref['sha256']
for origin,row in aliases.items():
 assert sha(row['path'])==row['sha256']
 if Path(origin).exists() and not origin.endswith('CompleteModulesNNStabilityLMI23.lean') and not origin.endswith('CompleteModulesNNCertificateAudit23.lean'):
  assert sha(origin)==row['sha256'],origin
exercise_keys=[];unit_decisions=collections.defaultdict(list);public_names=[];reviews=[];imports={};pairs=0
for proof in inp['proof_files']:
 path=proof['source'];assert sha(path)==proof['sha256']==offer['proof_files'][path]['sha256']
 ref=proof['original_review'];assert sha(ref['path'])==ref['sha256']
 rv=read(ref['path']);assert rv['reviewed_at_utc']==ref['original_review_time']
 canonical_ref={'file':ref['path'],'sha256':ref['sha256'],'reviewer':ref['reviewer'],'original_review_time':ref['original_review_time']}
 assert rv['reviewer']==ref['reviewer']
 reviews.append(canonical_ref)
 if ref['original_path'] in aliases:assert aliases[ref['original_path']]['sha256']==ref['sha256']
 scope=rv.get('scope',rv.get('limits',[]))
 for e in rv['records']:
  k=e['exercise_key'];assert k not in exercise_keys;exercise_keys.append(k)
  assert e.get('entire_inventory_record',rv.get('entire_exercise_inventory_record'))==es[k]
  assert e['exercise_text_sha256']==es[k]['text_sha256'] and e['whole_exercise_approved'] and e['independent_whole_source_review_passed'] and e['missing_clauses']==[]
  row=ce[k];old=oe[k];assert old['status']=='pending' and row['status']=='complete_math'
  assert row['independent_whole_source_review']==canonical_ref
  retained=[c for c in old['claims'] if c['status'] in ('proved','not_a_formal_claim')]
  assert row['claims'][:-1]==retained
  claim=row['claims'][-1]
  assert claim=={'id':k+'::source48-independent-whole23','statement_in_prose':es[k]['source_text'],'kind':'independently_reviewed_whole_exercise','status':'proved','lean_declarations':e['lean_declarations'],'hypotheses':e['hypotheses'],'correspondence':e['per_exercise_reason'],'remaining_gaps':[],'source_unit_keys':[],'independent_source_review':canonical_ref,'scope_limits':scope}
  assert {a:b for a,b in row.items() if a not in ('claims','status','independent_whole_source_review')}=={a:b for a,b in old.items() if a not in ('claims','status','independent_whole_source_review')}
 for u in rv['material_units']:
  k=u['source_unit_key'];assert u['entire_inventory_record']==us[k] and u['unit_text_sha256']==us[k]['text_sha256']
  assert u['whole_unit_approved'] and u['missing_clauses']==[]
  unit_decisions[k].append((u,canonical_ref,scope))
 source=(ROOT/path).read_text();names=[d['name'] for d in declarations(source) if d['kind'] in ('theorem','lemma')]
 assert names==proof['public_declarations']==offer['proof_files'][path]['declarations']==candidate['proof_files'][path]['declarations']
 public_names+=names
 pairrows=proof['actual_paired_records'];assert len(pairrows)==2
 for mode,pair in zip(('lean_standalone','named_lean_module_build'),pairrows):
  a=pair['actual_record'];log=pair['raw_log'];snap=pair['source_snapshot'];r=read(a['path'])
  assert sha(a['path'])==a['sha256'] and r['actual_exit_code']==pair['actual_exit_code']==0
  assert r['kind']==mode and r['source_unchanged'] is True and r['source']==r['lean_file']==path
  assert r['source_sha256_before']==r['source_sha256_after']==sha(path)==sha(snap['path'])==snap['sha256']
  assert sha(log['path'])==log['sha256']==r['log_sha256']
  assert aliases[r['log']]['path']==log['path'] and aliases[r['source_snapshot']]['path']==snap['path']
  assert r['command'][0]=='lake' and r['command'][-1] in (path.replace('verification/lean/',''),'SafeLearning.'+Path(path).stem)
  pairs+=1
 assert candidate['proof_files'][path]['actual_paired_records']==pairrows
 evidence=candidate['proof_files'][path]['standalone_compile_evidence'];assert evidence['exit_code']==0 and evidence['source_unchanged'] is True
 assert evidence['compiler_manifest']==pairrows[0]['actual_record']['path'] and evidence['log']==pairrows[0]['raw_log']['path']
 for module in re.findall(r'^import\s+(SafeLearning\.\S+)',source,re.M):
  dep='verification/lean/'+module.replace('.','/')+'.lean';imports[dep]=sha(dep)
assert len(exercise_keys)==7 and set(exercise_keys)==set(inp['whole_exercise_keys'])==set(offer['fresh_whole_exercise_keys'])
assert len(unit_decisions)==42 and sum(map(len,unit_decisions.values()))==43
assert set(unit_decisions)==set(inp['material_unit_keys'])==set(offer['fresh_material_unit_keys'])
assert len(public_names)==len(set(public_names))==48 and pairs==8
suppref=inp['explicit_node1012_scope_supplement'];assert sha(suppref['path'])==suppref['sha256']=='db80ca287866da8d58e0f8efde09c1ec15156ece108c9490b457e77bdf18bdca'
supp=read(suppref['path']);su=supp['material_units'][0];assert supp['original_review_entire_body_time_and_decisions_preserved']
for k,decisions in unit_decisions.items():
 u,ref,scope=decisions[0];row=cu[k+'::claim-review'];old=ou[k+'::claim-review'];status='proved' if u['material_status']=='proved' else 'not_a_formal_claim'
 assert row['statement_in_prose']==us[k]['source_text'] and row['status']==status and row['hypotheses']==u['hypotheses']
 assert row['correspondence']==u['per_unit_reason'] and row['remaining_gaps']==[] and row['independent_source_review']==ref and row['scope_limits']==scope
 assert row['lean_declarations']==(su['lean_declarations'] if k.endswith('node-1012') else u['lean_declarations'])
 assert row['kind']==('independently_reviewed_mathematical_source_unit' if status=='proved' else 'instruction_or_navigation')
 if k.endswith('node-1012'):
  assert su['entire_inventory_record']==us[k] and {a:b for a,b in su.items() if a!='lean_declarations'}=={a:b for a,b in u.items() if a!='lean_declarations'}
  assert len(su['lean_declarations'])==len(u['lean_declarations'])+1
  assert row['explicit_dependency_scope_supplement']['file']==suppref['path'] and row['explicit_dependency_scope_supplement']['original_supplement_time']==supp['reviewed_at_utc']
 if len(decisions)>1:
  assert k=='nn-in-the-loop.html::node-998' and len(decisions)==2 and status=='not_a_formal_claim'
  assert row['additional_independent_source_reviews']==[decisions[1][1]] and row['additional_independent_unit_reasons']==[decisions[1][0]['per_unit_reason']]
  assert not row['lean_declarations'] and not decisions[1][0]['lean_declarations']
 changed={'statement_in_prose','status','kind','lean_declarations','hypotheses','correspondence','remaining_gaps','independent_source_review','scope_limits','additional_independent_source_reviews','additional_independent_unit_reasons','explicit_dependency_scope_supplement'}
 assert {a:b for a,b in row.items() if a not in changed}=={a:b for a,b in old.items() if a not in changed}
for k,row in ce.items():
 if k not in exercise_keys:assert row==oe[k]
for k,row in cu.items():
 if k.removesuffix('::claim-review') not in unit_decisions:assert row==ou[k]
new_sources=set(offer['proof_files']);assert len(new_sources)==4
assert {k:v for k,v in candidate['proof_files'].items() if k not in new_sources}==original['proof_files']
assert candidate['declarations'][:len(original['declarations'])]==original['declarations']
assert [x['name'] for x in candidate['declarations'][len(original['declarations']):]]==public_names
expected_imports=copy.deepcopy(original['required_external_import_dependencies']);expected_imports.update({n:h for n,h in imports.items() if n not in new_sources})
assert candidate['required_external_import_dependencies']==expected_imports
allowed={'exercises','material_claims','proof_files','declarations','required_external_import_dependencies','generated_at_utc','reviewed_work_integration23_candidate','counts'}
assert {k:v for k,v in candidate.items() if k not in allowed}=={k:v for k,v in original.items() if k not in allowed}
for p,h in offer['required_evidence_artifacts_sha256'].items():assert sha(p)==h
for proof in offer['proof_files'].values():
 for p,h in proof['evidence_sha256'].items():assert sha(p)==h
failure=inp['preserved_first_preparation_failure']
for field in ('actual_record','raw_log','helper'):assert sha(failure[field]['path'])==failure[field]['sha256']
failed=read(failure['actual_record']['path']);assert failed['actual_exit_code']==1 and failed['log_sha256']==failure['raw_log']['sha256']
selection_path='reports/full-coverage/checkpoint-22-selection.json';selection=read(selection_path)
assert selection['proof_file_count']==1113
for n,row in selection['proof_files'].items():assert sha(n)==row['sha256']
for n,h in inp['protected_owner_and_html_sha256'].items():assert sha(n)==h
assert offer['live_owner_assets_mutated'] is False and offer['coverage_complete'] is False
assert candidate['counts']['exercise_status']==dict(collections.Counter(x['status'] for x in candidate['exercises']))
assert candidate['counts']['material_claim_status']==dict(collections.Counter(x['status'] for x in candidate['material_claims']))
out=Path('/tmp/modules23-seven-practice-candidate-independent-applied-confirmation-v1.json');assert not out.exists()
result={'status':'passed_independent_read_only_module23_seven_practice_candidate_mechanical_confirmation','reviewer':'/root/applied_next','checked_at_utc':datetime.now(timezone.utc).isoformat(),'offer':{'file':offer_path,'sha256':sha(offer_path)},'candidate':{'file':offer['module_ledger'],'sha256':sha(offer['module_ledger'])},'builder':{'file':offer['module_builder'],'sha256':sha(builder)},'actual_isolated_builder':offer['actual_builder'],'actual_builder_log':offer['actual_builder_raw_log'],'guard':guardref,'input_bindings':inp_ref,'original_whole_reviews':reviews,'semantic_reviews_were_not_rewritten_or_reperformed':True,'explicit_node1012_supplement':suppref,'shared_nominal_instruction':'node998 has two original immutable nonformal decisions/reasons but one exact physical claim row. Both review times are retained.','counts':{'whole_exercises':7,'distinct_material_units':42,'original_material_review_decisions':43,'baseline_exercises_byte_semantics_preserved':210,'baseline_material_bodies_preserved':5141,'old_proof_rows_preserved':469,'new_sources':4,'new_public_theorem_exports':48,'source_matched_actual_pairs':8,'selected22_sources_rehashed':1113,'archived_original_aliases':len(aliases)},'candidate_counts':candidate['counts'],'first_preparation_failure':failure,'held22_owner_and_html_sha256':inp['protected_owner_and_html_sha256'],'scope':'Mechanical candidate-only confirmation of precise original independent source decisions/whole scopes, literal records, declarations/hypotheses/reasons/times and actual source/command/log evidence. No current owner mutation, live global23 check, compiler run, production selection or aggregate23 audit.','actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'errors':[],'coverage_complete':False}
with out.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','file':str(out),'sha256':sha(out),'counts':result['counts']}))
