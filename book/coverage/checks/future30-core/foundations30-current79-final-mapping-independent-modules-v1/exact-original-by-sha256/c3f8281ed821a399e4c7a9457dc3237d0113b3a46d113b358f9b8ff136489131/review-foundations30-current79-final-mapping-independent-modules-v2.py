from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');O=Path('/tmp/foundations30-current79-final-mapping-independent-modules-peer-v2.json');assert not O.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def check(v):p=path(v['file']);assert p.is_file() and sha(p)==v['sha256'];assert 'bytes' not in v or p.stat().st_size==v['bytes'];return p
def readref(v):return json.loads(check(v).read_bytes())
def encoded(d):return (json.dumps(d,indent=2)+'\n').encode()
def normalized_literal(d):return {k:v for k,v in d.items() if k!='source_sha256'}
P=R/'book/coverage/checks/future30-foundations/current79-completed90-association-v1/foundations30-completed90-current79-pair-bound-closed-offer-v5.json';assert sha(P)=='861b55eae2da41bc766ebcf7dd6776bcc9c6e8335cd90a581489965a47756830';offer=json.loads(P.read_bytes());assert offer['errors']==[] and not offer['all_new_actual_canonical_pairs_pending'];candidate=readref(offer['candidate']);final=copy.deepcopy(candidate)
I90=readref(offer['exact_interface']);I54=readref(offer['original_real54_binding_exact_interface']);IP=readref(offer['original_pending_current79_exact_interface']);basepath=check(offer['original_installed29_ledger']);base=json.loads(basepath.read_bytes());assert sha(basepath)=='67889e85ad190d150ec888b803cfcc4d2c80dc48aa096d1969ddfbf90cda5f07'
# Check every finalized hash edge explicitly, then reproduce each complete reverse and forward stage.
def undo_metadata(d,changes):
 hit=[x for x in changes if x['path'] in [['current30_material_mapping','exact_interface'],['current30_material_mapping']]];assert len(hit)==1
 value=hit[0]['after'] if len(hit[0]['path'])==2 else hit[0]['after']['exact_interface']
 d['current30_material_mapping']['exact_interface']=copy.deepcopy(value)
 for x in reversed(changes):
  cur=d
  for k in x['path'][:-1]:cur=cur[k]
  k=x['path'][-1];assert cur[k]==x['after']
  if x['before_present']:cur[k]=copy.deepcopy(x['before'])
  else:del cur[k]
 return d
rev=undo_metadata(copy.deepcopy(final),I90['exact_metadata_changes']);stage54=readref(I90['original_real54_candidate']);assert rev==stage54 and encoded(rev)==check(I90['original_real54_candidate']).read_bytes()
rev=undo_metadata(rev,I54['canonical_metadata_changes']);provisional=readref(I54['original_current79_provisional_candidate']);assert rev==provisional and encoded(rev)==check(I54['original_current79_provisional_candidate']).read_bytes()
assert rev['material_claims'][-4:]==IP['four_component_only_rows_appended'];rev['material_claims']=rev['material_claims'][:-4]
for x in IP['individual66_pending_row_replacements']:assert rev['material_claims'][x['index']]==x['new_row'];rev['material_claims'][x['index']]=copy.deepcopy(x['rebased_pending_row'])
for x in reversed(IP['source_identity_field_changes']):
 row=rev[x['table']][x['index']]
 for fld,v in x['field_changes'].items():assert row[fld]==v['after'];row[fld]=copy.deepcopy(v['before'])
for k in ['source_sha256','proof_files','proof_sha256','counts']:rev[k]=copy.deepcopy(base[k])
for k in ['current79_owner_identity','current30_material_mapping']:del rev[k]
assert rev==base and encoded(rev)==basepath.read_bytes()
fw=copy.deepcopy(base)
for x in IP['source_identity_field_changes']:
 for fld,v in x['field_changes'].items():assert fw[x['table']][x['index']][fld]==v['before'];fw[x['table']][x['index']][fld]=copy.deepcopy(v['after'])
for x in IP['individual66_pending_row_replacements']:assert fw['material_claims'][x['index']]==x['rebased_pending_row'];fw['material_claims'][x['index']]=copy.deepcopy(x['new_row'])
fw['material_claims']+=copy.deepcopy(IP['four_component_only_rows_appended'])
for k in ['source_sha256','proof_files','proof_sha256','counts','current79_owner_identity','current30_material_mapping']:fw[k]=copy.deepcopy(provisional[k])
assert fw==provisional
for stage,changes,target,interface_ref in [(54,I54['canonical_metadata_changes'],stage54,offer['original_real54_binding_exact_interface']),(90,I90['exact_metadata_changes'],final,offer['exact_interface'])]:
 for x in changes:
  cur=fw
  for k in x['path'][:-1]:cur=cur[k]
  if x['before_present']:assert cur[x['path'][-1]]==x['before']
  else:assert x['path'][-1] not in cur
  cur[x['path'][-1]]=copy.deepcopy(x['after'])
 fw['current30_material_mapping']['exact_interface']=copy.deepcopy(target['current30_material_mapping']['exact_interface']);assert fw==target
# Read every complete qualified/current literal and its authoritative original full peer decision.
INV=readref(offer['inventory']);UN={u['key']:u for u in INV['material_source_units']};plan=readref(offer['approved_scope_plan']);whole=IP['all58_entire_math_literal_bindings'];assert len(whole)==len({b['inventory_key'] for b in whole})==58
assert set(b['inventory_key'] for b in whole)==set(plan['current65_whole_keys_independently_approved']+plan['reviewed_qualified_whole_keys_for_later_actual79_mapping']);decisions=[]
for b in whole:
 key=b['inventory_key'];u=UN[key];assert b['entire_current79_literal']==u;peer=readref(b['original_full_semantic_peer']);assert peer['status'].startswith('passed_') and peer.get('errors',[])==[]
 qual=b['qualification_application_association'];original_dec=b['original_individual_decision_retained']
 if qual is None:
  assert original_dec is not None and any(original_dec.get(n) is True for n in ['whole_literal_approved','current_whole_literal_approved','entire_current_literal_approved','entire_literal_approved'])
 else:
  assert qual['current79_entire_literal']==u;check(qual['original_individual_Source65_proposal']);narrow=readref(qual['full_wording_and_independent_parser_peer']);assert narrow['status'].startswith('passed_') and narrow.get('errors',[])==[]
  for pr in qual['full_mathematical_scope_peers']+qual['additional_full_prospective_literal_associations']:
   dd=readref(pr);assert dd['status'].startswith('passed_') and dd.get('errors',[])==[]
  # Preserve original false/current decisions; the exact only-gap qualifier supplies the separately measured79 whole association.
  if key=='primer-linalg.html::node-190':assert peer['prospective_corrected190_whole_semantic_approved'] is True and peer['current190_whole_approved'] is False and normalized_literal(peer['entire_prospective_corrected_literal'])==normalized_literal(u)
 decisions.append({'key':key,'whole_actual79_literal_approved':True,'remaining_gaps':[],'qualified_from_original_component_or_prospective_scope':qual is not None,'original_full_peer':b['original_full_semantic_peer'],'text_sha256':u['text_sha256'],'support_names':b['public_support'],'original_peer_body_time_false_statuses_unchanged':True})
assert sum(x['qualification_application_association'] is not None for x in whole)==15
replacements=IP['individual66_pending_row_replacements'];assert len(replacements)==66 and Counter(x['classification'] for x in replacements)=={'whole_math':63,'nonformal_reference':3};assert len({x['index'] for x in replacements})==66
for x in replacements:
 assert x['original_row']==base['material_claims'][x['index']] and x['original_row']['status']=='pending';z=final['material_claims'][x['index']];assert z['status']==('proved' if x['classification']=='whole_math' else 'not_a_formal_claim') and z['remaining_gaps']==[]
 if x['classification']=='whole_math':assert z['source_text']==UN[z['source_unit_keys'][0]]['source_text'] and z['original_full_literal_decision_and_actual79_association']['entire_current79_literal']==UN[z['source_unit_keys'][0]]
 else:assert z['lean_declarations']==[] and z['mathematical_whole_approval_claimed'] is False
assert {r['source_unit_keys'][0] for r in final['material_claims'][-4:]}=={'primer-linalg.html::node-323','primer-linalg.html::node-421','primer-linalg.html::node-873','primer-linalg.html::node-879'}
for z in final['material_claims'][-4:]:assert z['current_whole_literal_approved'] is False and any(r['status']=='pending' and r['source_unit_keys']==z['source_unit_keys'] for r in final['material_claims'])
assert len(final['exercises'])==119 and [{k:v for k,v in e.items() if k!='source_sha256'} for e in final['exercises']]==[{k:v for k,v in e.items() if k!='source_sha256'} for e in base['exercises']]
changed=set(IP['source65_to79_changed_owned_literal_keys']);assert len(changed)==14
for i,z in enumerate(base['material_claims']):
 if z['status']=='proved':
  allow={'source_sha256'}|({'source_text','source_text_sha256'} if set(z['source_unit_keys'])&changed else set());assert {k:v for k,v in z.items() if k not in allow}=={k:v for k,v in final['material_claims'][i].items() if k not in allow}
counts=dict(Counter(r['status'] for r in final['material_claims']));assert counts==offer['material_claim_counts']=={'proved':1208,'pending':380,'not_a_formal_claim':535};assert len({k for r in final['material_claims'] if r['status']=='pending' for k in r['source_unit_keys']})==354
# Full namespace-aware source index and literal command/native/log/snapshot chains: actual54 is a strict subset of authentic90.
NAMES=R/'book/coverage/lean_names.py';spec=importlib.util.spec_from_file_location('independent_foundations30_final_names',NAMES);names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names);rd=readref(offer['actual_common90_readiness']);rootnative=readref(offer['actual_common90_outer_execution']);assert rootnative['status']=='passed' and type(rootnative['actual_exit_code']) is int and rootnative['actual_exit_code']==0
assert rd['source_count']==45 and rd['actual_compiler_command_count']==90 and rd['errors']==[];newnames=[];paircount=0
for source,p in offer['proof_files'].items():
 body=(R/source).read_text();assert sha(R/source)==p['sha256'];ns=[v['name'] for v in names.declarations(body) if v['kind'] in ['theorem','lemma']];assert ns==p['public_theorem_names']==p['mapped_named_declarations'] and len(ns)==p['theorem_count'];newnames+=ns
 pair=p['actual_pair'];assert len(pair)==2 and [r['kind'] for r in pair]==['standalone','named'];assert pair==[r for r in rd['actual_paired_records'] if r['source']['file']==source]
 for r in pair:
  for k in ['source','actual_record','raw_log','source_snapshot']:check(r[k])
  native=readref(r['actual_record']);assert type(native['exit_code']) is int and native['exit_code']==r['actual_exit_code']==0 and native['source']==source and native['source_sha256_before']==native['source_sha256_after']==p['sha256'] and native['actual_workdir']==str(R/'verification/lean')
  expected=['lake','env','lean','SafeLearning/'+Path(source).name] if r['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(source).stem];assert native['command']==expected and native['log']==r['raw_log']['file'] and native['log_sha256']==r['raw_log']['sha256'];paircount+=1
 for k,h in p['evidence_sha256'].items():assert sha(path(k))==h
assert len(offer['proof_files'])==27 and paircount==54 and len(newnames)==len(set(newnames))==370;assert final['proof_files'][:len(base['proof_files'])]==base['proof_files'] and all(final['proof_sha256'][k]==v for k,v in base['proof_sha256'].items())
physical=offer['required_evidence_artifacts_sha256'];assert physical
for n,h in physical.items():p=path(n);assert not Path(n).is_absolute() and p.is_file() and p.resolve().is_relative_to(R) and sha(p)==h and n not in ['book/coverage/foundations.json','book/coverage/modules.json','book/coverage/core.json','book/coverage/applied.json','book/coverage/applied-promotions.json']
for original,v in offer['original_closed_byte_aliases'].items():check(v)
for field in ['actual_author_preparation','actual_canonical_binder_execution','actual_completed90_association_execution']:
 n=readref(offer[field]);assert n['status']=='passed' and type(n['actual_exit_code']) is int and n['actual_exit_code']==0 and n['protection_errors']==[]
CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');c=json.loads(CTX.read_bytes());pins={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']};assert all(sha(path(n))==h for n,h in pins.items())
D={'original_independent_reader1_true_failure':ref('/tmp/foundations30-current79-final-mapping-independent-modules-actual-v1.json'),'reader1_failure_scope':'Own first genuine reader expected the hash-finalization metadata change at a child path. Actual54 interface changes the entire current30_material_mapping bucket; NEW2 uses its exact after.exact_interface before reversing. The static scope-plan total58 is also treated as a count, with keys derived from the real43+15 lists. No producer/source/candidate/math defect or fabricated second native failure; original reader/helper/raw/native/body/time retained.','status':'passed_independent_Foundation30_current79_completed90_27_source54_pair_bound_whole_component_NF_and_composed_exact_owner29_mapping_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':offer['candidate'],'offer':ref(P),'exact_interface':offer['exact_interface'],'original_raw_owner29':offer['original_installed29_ledger'],'all_three_forward_and_reverse_stages_full_byte_exact':True,'old119_exercises_and1141_proved_semantic_bodies_metadata_history_and_times_retained':True,'individual_actual79_whole_unit_decisions':decisions,'whole_material_keys':58,'original_pending_math_rows_resolved':63,'individually_nonformal_reference_rows':3,'component_only_rows_kept_whole_pending':['primer-linalg.html::node-323','primer-linalg.html::node-421','primer-linalg.html::node-873','primer-linalg.html::node-879'],'qualified_whole_decisions15_are_fresh_current79_literal_associations_not_retimed_old_native_claims':True,'all14_source_correction_literal_slots_current79_exact':True,'proof_source_count':27,'public_theorem_count':370,'actual_canonical_command_count':54,'actual_common90_readiness':offer['actual_common90_readiness'],'actual_common90_execution':offer['actual_common90_outer_execution'],'all_literal_commands_cwd_source_before_after_snapshot_log_names_and_zero_statuses_checked':True,'all427_physical_closure_refs_checked':len(physical),'actual_author_binder_and_completed90_association_body_times_preserved':True,'material_counts':counts,'physical_pending_units':354,'actual79_guard_context':ref(CTX),'producer_or_compiler_launched_by_reviewer':False,'owner_source_selection_Git_publication_mutated':False,'coverage_complete':False,'selection_aggregate_and_owner_installation_remain_Root_actions':True}
O.write_text(json.dumps(D,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':ref(O),'whole_units':58,'actual_commands':54,'exact_raw_owner_inverse':True,'physical_refs':len(physical)}))
