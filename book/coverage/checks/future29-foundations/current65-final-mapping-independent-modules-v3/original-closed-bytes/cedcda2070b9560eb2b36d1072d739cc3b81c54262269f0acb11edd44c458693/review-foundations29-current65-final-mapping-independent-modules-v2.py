from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import json,hashlib,copy,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-foundations/current65-final-mapping-independent-modules-v2';assert not D.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_bytes())
def P(n):p=Path(n);return p if p.is_absolute()else R/p
def check(v):p=P(v['file']);assert H(p)==v['sha256'];return p
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':H(p)}
def samebytes(v,p):
 raw=Path(p).read_bytes();original=J(p);modes=[mode for mode in [True,False]if(json.dumps(original,indent=2,ensure_ascii=mode)+'\n').encode()==raw];assert modes
 assert v==original and any((json.dumps(v,indent=2,ensure_ascii=mode)+'\n').encode()==raw for mode in modes)
O=R/'book/coverage/checks/future28-foundations/current65-owner29-canonical-v2/foundations29-current65-canonical-offer-draft-v3.json';assert H(O)=='cd6bcd6d9c97d0ab9fc9485043b16dc38e8d7e68cbc88eaaf94498a8a9d28a6d';o=J(O);assert o['errors']==[]and o['coverage_complete']is False
C=check(o['candidate']);assert H(C)=='67889e85ad190d150ec888b803cfcc4d2c80dc48aa096d1969ddfbf90cda5f07';c=J(C);B=check(o['original_installed28_ledger']);assert H(B)==H(R/'book/coverage/foundations.json')=='269b6f6053c4fd91fa9c4346b469e190a804f41a5edb0f9d5a74319fcadf5ddf';b=J(B)
assert c['exercises']==b['exercises']and len(c['exercises'])==119 and c['proof_files'][:len(b['proof_files'])]==b['proof_files']and len(c['proof_files'])==len(b['proof_files'])+6
I=check(o['exact_interface']);i=J(I);rev=copy.deepcopy(c)
# The canonical interface hashes itself only after writing its SHA-absent reference; restore that exact pre-hash metadata.
mapping=next(x for x in i['canonical_metadata_changes']if x['path']==['current29_material_mapping']);rev['current29_material_mapping']['exact_interface']=copy.deepcopy(mapping['after']['exact_interface'])
for x in reversed(i['canonical_metadata_changes']):
 d=rev
 for k in x['path'][:-1]:d=d[k]
 assert d[x['path'][-1]]==x['after']
 if x['before_present']:d[x['path'][-1]]=copy.deepcopy(x['before'])
 else:del d[x['path'][-1]]
C65=check(i['original65_candidate']);samebytes(rev,C65)
a65=J(check(o['current65_inventory_association_interface']));rev.pop('current65_owner_identity');C64=check(a65['original_current64_candidate']);samebytes(rev,C64)
i64=J(check(o['original_pending64_exact_interface']));assert len(i64['sixteen_individual_row_replacements'])==16 and len(i64['source_identity_field_changes'])==2120
math=[];nf=[];units=J(check(o['inventory']));actual={x['key']:x for x in units['material_source_units']};removals={x['original_index']for x in i64['sixteen_individual_row_replacements']}
for x in i64['sixteen_individual_row_replacements']:
 idx=x['original_index'];row=rev['material_claims'][idx];assert row==x['new_row']and b['material_claims'][idx]==x['original_source60_owner_row']and b['material_claims'][idx]['status']=='pending';key=row['source_unit_keys'][0];u=actual[key]
 assert row['source_text']==row['statement_in_prose']==u['source_text']and row['source_text_sha256']==u['text_sha256']and row['source_sha256']==u['source_sha256']and row['remaining_gaps']==[]
 peer=J(check(row['source_review']));assert peer['errors']==[]and peer['status'].startswith('passed_')
 if row['status']=='proved':
  assert row['whole_literal_scope_independently_approved']is True and row['lean_declarations'];math.append(key)
  assert set(row['lean_declarations'])<=set(o['proof_files'][row['new_canonical_source']]['public_theorem_names'])
  if key.endswith('141'):
   q=J(check(row['additional_corrected_literal_association_peer']));assert q['status']=='passed_independent_source64_full_narrow_wording_and_isolated_full29_parser_review'and q['errors']==[]and all(x['approved']for x in q['narrow_wording_decisions']);assert 'u_{\\max}\\ge0'in row['source_text']and 'j\\ne y'in row['source_text']
 elif row['status']=='not_a_formal_claim':assert row['lean_declarations']==[]and 'bibliographic-reference'in row['id'];nf.append(key)
 else:raise AssertionError(row['status'])
 rev['material_claims'][idx]=copy.deepcopy(x['rebased_pending_row'])
assert len(math)==len(nf)==8
for x in reversed(i64['source_identity_field_changes']):
 row=rev[x['table']][x['index']]
 for k,pair in x['field_changes'].items():
  assert k in ['source_sha256','source_text','source_text_sha256']and row[k]==pair['after'];row[k]=copy.deepcopy(pair['before'])
for k in ['current64_owner_identity','current29_material_mapping','current29_source_qualification_support']:rev.pop(k)
for k in ['source_sha256','proof_files','proof_sha256','counts']:rev[k]=copy.deepcopy(b[k])
samebytes(rev,B)
# Entire prior semantic clauses (including their dates/hypotheses/proofs) were restored, not regenerated.
assert sum(x['status']=='proved'for x in b['material_claims'])==1133
assert Counter(x['status']for x in c['material_claims'])=={'proved':1141,'pending':446,'not_a_formal_claim':532}and o['physical_pending_unit_count']==415
assert o['new_whole_material_unit_count']==o['new_nonformal_reference_row_count']==8 and o['new_whole_exercise_count']==0 and o['new_theorem_or_lemma_count']==53
ready=J(check(o['actual_canonical_readiness']));assert ready['errors']==[]and ready['actual_compiler_command_count']==20 and H(check(o['actual_canonical_readiness']))=='69a560ae42809ecaf8a11e0b6492fd411691e4c928a83684ced9c29936492917'
# Read all53 actual source theorem bodies as text and reproduce the namespace-aware actual source declaration list.
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
count=0
for n,p in o['proof_files'].items():
 source=R/n;assert H(source)==p['sha256'];text=source.read_text();ds=declarations(text);names=[x['name']for x in ds if x['kind']in ['theorem','lemma']];assert p['public_theorem_names']==p['mapped_named_declarations']==names and p['theorem_count']==len(names);count+=len(names)
 pairs=[v for v in ready['actual_paired_records']if v['source']['file']==n];assert [v['kind']for v in pairs]==['standalone','named']and p['actual_pair']==pairs
 for v in pairs:
  nr=J(check(v['actual_record']));assert v['actual_exit_code']==nr['exit_code']==0 and nr['status']=='passed'and nr['source']==n and nr['source_sha256_before']==nr['source_sha256_after']==H(source)and nr['actual_workdir']==str(R/'verification/lean')
  expected=['lake','env','lean','SafeLearning/'+source.name]if v['kind']=='standalone'else['lake','build','SafeLearning.'+source.stem];assert nr['command']==expected
  assert check(v['source_snapshot']).read_bytes()==source.read_bytes()and H(check(v['raw_log']))==nr['log_sha256']
  for k in ['actual_record','raw_log','source_snapshot']:assert o['required_evidence_artifacts_sha256'][v[k]['file']]==v[k]['sha256']and p['evidence_sha256'][v[k]['file']]==v[k]['sha256']
assert count==53 and len(o['proof_files'])==6
native=J(check(o['author_actual_finalizer']));assert native['actual_exit_code']==0 and native['status']=='passed'and native['command']==native['actual_command']==['python3','/tmp/prepare-foundations-owner29-current65-canonical-candidate-v2.py']and native['cwd']==str(R)
cl=J(check(o['actual_author_preparation_closure']));aliases=cl['original_preparation_byte_aliases'];assert H(check(aliases[native['helper']['file']]))==native['helper']['sha256']and H(check(aliases[native['log']['file']]))==native['log']['sha256']
for n,h in o['required_evidence_artifacts_sha256'].items():assert not Path(n).is_absolute()and P(n).resolve().is_relative_to(R.resolve())and H(P(n))==h,n
assert len(o['required_evidence_artifacts_sha256'])==225
for n,h in o['source_sha256'].items():assert H(P(n))==h
assert H(R/'book/coverage/inventory.json')==o['inventory_sha256']=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
ctx=J('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
for n,h in {**ctx['pins_sha256'],**ctx['held_current_source_sha256']}.items():assert H(P(n))==h,n
D.mkdir(parents=True);out={'status':'passed_independent_exact_foundations29_current65_six_source_eight_math_eight_reference_final_mapping','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':o['candidate'],'offer':ref(O),'exact_forward_and_composed_three_stage_full_byte_inverse_to_original_owner28':True,'all119_exercises_all1133_prior_proved_semantic_rows_original_hypotheses_declarations_body_histories_and_times_retained':True,'all256_old_proof_metadata_prefix_retained':True,'whole_material_units':math,'individually_reviewed_nonformal_bibliography_rows':nf,'source_count':6,'theorem_or_lemma_count':53,'actual_native_command_count':12,'all_actual_pair_command_cwd_source_log_snapshot_and_native_time_bodies_exact':True,'entire_six_current_canonical_sources_and_namespace_aware_declarations_read':True,'all16_entire_current65_literals_and_individual_peer_correspondence_rows_read':True,'source141_prospective_original_peer_literal_now_equal_to_actual65_with_both_source64_qualifications':True,'seven_countermodel_support_theorems_in_two_sources_do_not_promote_any_other_whole_unit':True,'all225_physical_Root_closure_hashes_checked':True,'original_author1_failure_and_author2_success_preserved':True,'original_independent_whole_semantic_peers_and_review_times_retained_without_redecision':True,'new_whole_exercise_count':0,'no_source_owner_canonical_selection_publication_or_compiler_mutation':True,'original_author_actual_finalizer':o['author_actual_finalizer'],'actual_finalizer':None,'coverage_complete':False}
q=D/'foundations29-current65-final-mapping-independent-modules29-peer-v1.json';q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(q),'candidate':o['candidate'],'offer':ref(O),'status':out['status']}))
