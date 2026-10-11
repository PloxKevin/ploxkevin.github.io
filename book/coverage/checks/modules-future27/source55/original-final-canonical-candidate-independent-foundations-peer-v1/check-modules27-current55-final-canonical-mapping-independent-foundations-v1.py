from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future27/source55'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(n):return {'file':str(n.relative_to(R)) if isinstance(n,Path) and n.is_relative_to(R) else str(n),'sha256':sha(path(n))}
def read(n):return json.loads(path(n).read_text())
def check(r):assert sha(path(r['file']))==r['sha256'],r;return read(r['file'])
def zero(x):
 vals=[x[k] for k in ('actual_exit_code','exit_code') if k in x];assert vals and all(type(v)is int and v==0 for v in vals)
cand=B/'modules27-current55-two-whole-canonical-candidate-v1.json';of=B/'modules-audit27-candidate-current55-additions-draft-v1.json';it=B/'modules27-current55-two-whole-canonical-candidate-interface-v1.json'
assert sha(cand)=='7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487' and sha(of)=='5bd5b8198fe0e2b4a817a714d97dc38645185bf55443ca69de284da331670dc9' and sha(it)=='2d26c1cd7e67afca15fda80dac3f8a4d5db7e435aa5ef570409127e21196fdb9'
d=read(cand);o=read(of);i=read(it);m=d['reviewed_work_integration27_candidate'];draft=check(i['original_mapping_draft']);peer=check(i['original_independent_draft_peer']);old=read('book/coverage/modules.json')
assert i['errors']==[] and o['errors']==[] and peer['errors']==[];assert i['candidate_ledger']==o['candidate']==o['candidate_ledger']==ref(cand) and o['mapped_ledger']==str(cand.relative_to(R)) and o['mapped_ledger_sha256']==sha(cand)
assert i['original_mapping_draft']['sha256']=='1926ee49a419d5c9ef97f9859767b7481652eb24f3a7f022f83c4d3a9a93455c' and i['original_independent_draft_peer']['sha256']=='5d140ce68b84264b92390420f3ad25186d6158d91f3393935d97dec32c16a5ab' and i['entire_original_mapping_peer_body_and_time']==peer
assert check(o['original_pending_pair_mapping_draft'])==draft and check(o['original_independent_mapping_draft_peer'])==peer
assert m['original_reviewed_mapping_draft']==i['original_mapping_draft'] and m['original_independent_draft_mechanics']==i['original_independent_draft_peer']
changes=m['strict_reversible_finalization_changes'];inv=copy.deepcopy(d);inv.pop('reviewed_work_integration27_candidate');inv['generated_at_utc']=changes['original_generated_at_utc'];inv['proof_files'].update(changes['original_new_proof_rows']);inv['declarations'][len(old['declarations']):]=changes['original_declaration_suffix']
for a in changes['active_reference_replacements']:
 if a['kind']=='exercise':obj=next(e for e in inv['exercises'] if e['inventory_key']==a['key'])
 elif a['kind']=='exercise_claim':obj=next(c for e in inv['exercises'] for c in e['claims'] if c['id']==a['key'])
 else:obj=next(c for c in inv['material_claims'] if c['id']==a['key'])
 assert obj[a['field']]==a['canonical_alias'];obj[a['field']]=a['original'];assert sha(path(a['canonical_alias']['file']))==a['original']['sha256']==a['canonical_alias']['sha256']
assert inv==draft
# Fresh full second inverse to installed26, independent of the stored prior report.
s=inv['reviewed_current55_two_whole_mapping_draft27'];prior=s['original_two_whole_exercise_and_eight_pending_material_rows'];back=copy.deepcopy(inv);back.pop('reviewed_current55_two_whole_mapping_draft27')
for idx,e in enumerate(back['exercises']):
 if e['inventory_key'] in s['fresh_whole_exercise_keys']:back['exercises'][idx]=prior[e['inventory_key']]
for idx,c in enumerate(back['material_claims']):
 if c['id'] in prior:back['material_claims'][idx]=prior[c['id']]
for plan in s['planned_four_new_sources']:back['proof_files'].pop(plan['canonical_source'])
back['declarations']=back['declarations'][:len(old['declarations'])]
for k,v in s['source55_identity']['preserved_original_top_level_fields'].items():
 if k in old:back[k]=v
 else:back.pop(k,None)
assert back==old and sha(R/'book/coverage/modules.json')=='c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231'
assert d['reviewed_current55_two_whole_mapping_draft27']==draft['reviewed_current55_two_whole_mapping_draft27']
assert d['counts']==draft['counts'] and d['source_sha256']==draft['source_sha256'] and d['declarations'][:3172]==old['declarations'] and len(d['declarations'])==3259
for n,r in old['proof_files'].items():assert d['proof_files'][n]==r
assert len(old['proof_files'])==491 and len(d['proof_files'])==495
aliases=o['original_closed_byte_aliases'];assert aliases==i['original_closed_byte_aliases']
for k,row in aliases.items():
 assert k==row['original_file']+'::'+row['original_sha256'] and row['original_sha256']==row['sha256'] and sha(path(row['file']))==row['sha256']
for n,h in peer['closed_evidence_sha256'].items():
 row=aliases[n+'::'+h];assert row['sha256']==h and sha(path(row['file']))==h
assert len(peer['closed_evidence_sha256'])==13
assert o['entire_original_conformal_full_review_body_and_time']==s['entire_original_conformal_whole_review_body_and_time'] and o['entire_original_viability_full_review_body_and_time']==s['entire_original_viability_whole_review_body_and_time']
for r in o['original_full_source_reviews']:
 body=check(r);assert body in [o['entire_original_conformal_full_review_body_and_time'],o['entire_original_viability_full_review_body_and_time']]
assert o['counts']=={'new_sources':4,'new_public_exports':87,'whole_exercises':2,'whole_material_units':8};assert i['proof_source_count']==4 and i['public_export_count']==87 and i['whole_exercises']==2 and i['whole_material_units']==8
assert o['final_independent_candidate_mapping_peer'] is None and o['actual_isolated_candidate_preparation'] is None and o['coverage_complete'] is False and m['installed_owner_mutation'] is False and m['whole_corpus_coverage_complete'] is False
ready=check(o['actual_combined_canonical_readiness']);actual=check(o['actual_combined_canonical_execution']);zero(actual)
assert sha(path(o['actual_combined_canonical_readiness']['file']))=='74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f' and o['actual_combined_canonical_execution']['sha256']=='9ee7428bc5d16d6b65ec0fd88877d85e3ba38cb879f11951eca72ddd0b6df384'
assert actual['actual_command']==['python3','book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py','--apply'] and actual['actual_workdir']==str(R)
assert actual['helper_sha256_before']==actual['helper_sha256_after'];assert sha(path(actual['log']))==actual['log_sha256']
for n,h in actual['helper_sha256_after'].items():assert sha(path(n))==h
plans=s['planned_four_new_sources'];own={p['canonical_source'] for p in plans};assert own==set(o['proof_files'])==set(d['proof_files'])-set(old['proof_files'])
pair_rows=[];names=[]
for plan in plans:
 n=plan['canonical_source'];h=plan['source_sha256'];row=o['proof_files'][n];assert row==d['proof_files'][n] and sha(path(n))==h==row['sha256']
 assert row['declarations']==plan['all_public_declarations'] and row['standalone_compile_status']=='passed_source_matched_actual_canonical_standalone_and_named' and row['canonical_pair_execution_claimed'] is True
 assert read(path(row['independent_full_source_review']['file'])) in [o['entire_original_conformal_full_review_body_and_time'],o['entire_original_viability_full_review_body_and_time']]
 names+=row['declarations'];assert len(row['declarations'])==plan['public_theorem_count'] and [x.rsplit('.',1)[-1] for x in row['declarations']]==re.findall(r'^theorem\s+(\w+)',path(n).read_text(),re.M)
 rs=row['actual_paired_records'];assert rs==i['actual_pairs'][n] and len(rs)==2 and {r['kind'] for r in rs}=={'standalone','named'}
 for r in rs:
  assert r in ready['actual_paired_records'] and r['source']=={'file':n,'sha256':h} and type(r['actual_exit_code'])is int and r['actual_exit_code']==0
  native=check(r['actual_record']);zero(native);assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==h and native['source_unchanged'] is True
  assert native['actual_workdir']==str(R/'verification/lean');expected=['lake','env','lean','SafeLearning/'+Path(n).name] if r['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem];assert native['command']==expected
  assert r['raw_log']=={'file':native['log'],'sha256':native['log_sha256']} and sha(path(r['raw_log']['file']))==r['raw_log']['sha256'] and r['source_snapshot']['sha256']==h and sha(path(r['source_snapshot']['file']))==h
  pair_rows.append(r)
 for f,hf in row['evidence_sha256'].items():assert sha(path(f))==hf
assert len(names)==len(set(names))==87 and len(pair_rows)==8 and set(json.dumps(x,sort_keys=True) for x in pair_rows)==set(json.dumps(x,sort_keys=True) for x in o['actual_paired_records'])
for a,b in zip(d['declarations'][3172:],draft['declarations'][3172:]):assert a=={k:v for k,v in b.items() if k!='canonical_source_execution_pending'}
assert o['required_evidence_artifacts_sha256']==o['additional_frozen_inputs']
for n,h in o['required_evidence_artifacts_sha256'].items():assert sha(path(n))==h
actual_name='reports/full-coverage/modules27-current55-isolated-candidate-builder-execution-v1.json';builder=read(actual_name);zero(builder)
assert builder['actual_command']==['python3','book/coverage/build_modules27_candidate_current55_v2.py','--pair-execution','reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json'] and builder['actual_workdir']==str(R)
assert builder['helper_sha256_before']==builder['helper_sha256_after']=={o['candidate_builder']['file']:o['candidate_builder']['sha256']};assert sha(path(builder['log']))==builder['log_sha256'] and sha(path(builder['actual_runner']['file']))==builder['actual_runner']['sha256']
assert sha(path(o['candidate_builder']['file']))==o['candidate_builder']['sha256']
for n,h in ready['protected_input_sha256'].items():assert sha(path(n))==h,n
for r in ready['sources']:assert sha(path(r['canonical_source']))==r['source']['sha256']
result={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Modules authored isolated canonical builder','candidate':ref(cand),'offer':ref(of),'candidate_interface':ref(it),'actual_candidate_builder_execution':ref(actual_name),'actual_candidate_builder':o['candidate_builder'],'actual_candidate_builder_runner':builder['actual_runner'],'entire_original_pending_pair_draft_mechanics_peer_body_and_time':peer,'original_pending_pair_draft_peer':i['original_independent_draft_peer'],'original_conformal_and_viability_review_bodies_times_unchanged':True,'full_candidate_reverse_to1926_then_installed26_exact':True,'unchanged_old_proof_metadata':491,'unchanged_old_declaration_prefix':3172,'new_sources':4,'new_exports':87,'genuine_actual_canonical_records':8,'whole_exercises':2,'whole_material_units':8,'all_current55_record_mappings_scopes_reasons_hypotheses_and_times_exact':True,'all_original_peer13_reader_histories_and_original_byte_aliases_exact':True,'all1167_current55_31assets_fiveowners_and_eight_new_sources_exact':True,'semantic_redecision_or_retiming':False,'owner_installation_or_global_selection_claim':False,'scope':'Fresh exact canonical-byte/native-pair and reversible isolated mapping mechanics confirmation. Whole decisions remain precisely those of original554f/7248; all previous pending/partial bodies and times retain exact history. Root live copy, current55 owner global identity, selection/freeze/aggregate/publication remain separate unperformed steps.'}
O=Path('/tmp/modules27-current55-final-canonical-mapping-independent-foundations-check-result-v1.json');assert not O.exists();O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','new_sources':4,'exports':87,'actual_pairs':8,'full_double_inverse_exact':True}))
