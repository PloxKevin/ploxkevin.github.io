from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future30-foundations/current79-real54-pair-bound-v1';assert not D.exists()
OLD=R/'book/coverage/checks/future30-foundations/current79-provisional-owner30-v1/foundations30-current79-provisional-owner30-root-offer-v1.json'
PLAN=R/'book/coverage/checks/future30-core/current79-canonical-plan45-v2.json';RUNNER=R/'book/coverage/checks/run_root30_reviewed_canonical_pairs_v2.py';CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');PAIRS=R/'book/coverage/checks/future30-core/current79-canonical-pairs45-v1'
def path(n):
 p=Path(n);return p if p.is_absolute() else R/p
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def read(n):return json.loads(path(n).read_bytes())
def data(x):return (json.dumps(x,indent=2)+'\n').encode()
assert sha(OLD)=='b034f496d09b063c2713060f45e6dea0ff56d41079949baffc4f4564db567d3a'
assert sha(PLAN)=='4a2c2ab8e877d098f243562adc2112c116aa93062b40757c2d5e0cd57f90b09d'
assert sha(RUNNER)=='ec15d8df2c473174489cc412868db434e483dafc862d649334edf2d3512c4e2c'
assert sha(CTX)=='d06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737'
d=read(OLD);prior=read(d['candidate']['file']);prior_bytes=path(d['candidate']['file']).read_bytes();interface=read(d['exact_interface']['file']);plan=read(PLAN);context=read(CTX)
def guard():
 for fld in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in context[fld].items():assert sha(n)==h,n
 assert sha('book/coverage/inventory.json')==d['inventory_sha256']=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
 assert sha(OLD)=='b034f496d09b063c2713060f45e6dea0ff56d41079949baffc4f4564db567d3a'
 return {fld:copy.deepcopy(context[fld]) for fld in ['pins_sha256','held_current_source_sha256','owners_sha256']}
before=guard();started=datetime.now(timezone.utc).isoformat();requirements=dict(d['required_evidence_artifacts_sha256']);aliases=dict(d['original_closed_byte_aliases'])
def include(q):
 p=path(q['file']);assert sha(p)==q['sha256'];assert p.is_relative_to(R) and not p.is_symlink() and p.resolve().is_relative_to(R)
 n=p.relative_to(R).as_posix()
 if n in requirements:assert requirements[n]==q['sha256']
 requirements[n]=q['sha256'];return q
for q in [ref(OLD),d['candidate'],d['exact_interface'],ref(PLAN),ref(RUNNER)]:include(q)
sys.path.insert(0,str(R/'book/coverage'));import lean_names;include(ref(R/'book/coverage/lean_names.py'))
plans={s['canonical_source']:s for s in plan['sources'] if s['owner']=='foundations'};assert len(plans)==27 and sum(s['public_theorem_count'] for s in plans.values())==370
assert set(plans)==set(d['proof_files']) and plan['canonical_owner_selection_aggregate_or_publication_claimed'] is False
proofs=copy.deepcopy(d['proof_files']);records=[];changes=[];candidate=copy.deepcopy(prior)
def change(keys,value):
 cur=candidate
 for k in keys[:-1]:cur=cur[k]
 exists=keys[-1] in cur;old=copy.deepcopy(cur.get(keys[-1]));cur[keys[-1]]=copy.deepcopy(value);changes.append({'path':keys,'before_present':exists,'before':old,'after':copy.deepcopy(value)})
def zero(a):
 vals=[a[k] for k in ['exit_code','actual_exit_code','actual_runner_exit_code'] if k in a];assert vals and all(type(v) is int and v==0 for v in vals)
 assert a.get('protection_errors',[])==[] and a['status']=='passed'
def actual(a,cmd):
 zero(a);ks=[k for k in ['command','actual_command'] if k in a];assert ks and all(a[k]==cmd for k in ks)
 ks=[k for k in ['actual_workdir','cwd','working_directory','workdir'] if k in a];assert ks and all(a[k]==str(R/'verification/lean') for k in ks)
for dest,row in proofs.items():
 s=plans[dest];p=R/dest;h=row['sha256'];assert sha(p)==h==s['original_tmp_source']['sha256']
 decls=lean_names.declarations(p.read_text());assert decls==s['public_declarations']==row['source_level_public_declarations'];names=[v['name'] for v in decls if v['kind'] in ['theorem','lemma']];assert names==row['public_theorem_names'] and len(names)==row['theorem_count']==s['public_theorem_count']
 stem=p.stem;snapshot=PAIRS/'source-snapshots'/p.name;assert sha(snapshot)==h;include(ref(snapshot));include(ref(p));pair=[]
 for kind,postfix,cmd,invocation in [('standalone','-standalone.json',['lake','env','lean','SafeLearning/'+p.name],'-standalone-helper-invocation.log'),('named','-named-build.json',['lake','build','SafeLearning.'+stem],'-named-helper-invocation.log')]:
  native=R/'book/coverage/checks'/(stem+postfix);a=read(native);actual(a,cmd)
  assert a['source']==dest and a['source_sha256_before']==a['source_sha256_after']==h and a['source_unchanged'] is True
  raw=path(a['log']);assert sha(raw)==a['log_sha256'] and isinstance(a['checked_at_utc'],str) and type(a['elapsed_seconds']) in [int,float] and a['elapsed_seconds']>=0
  invlog=PAIRS/(stem+invocation);assert json.loads(invlog.read_bytes())==a
  r={'kind':kind,'source':{'file':dest,'sha256':h},'actual_record':include(ref(native)),'raw_log':include(ref(raw)),'source_snapshot':include(ref(snapshot)),'root_helper_invocation_raw':include(ref(invlog)),'actual_exit_code':0,'original_checked_at_utc':a['checked_at_utc'],'original_elapsed_seconds':a['elapsed_seconds'],'original_record_has_no_start_time_field':True,'emitted_diagnostic_warning_headers':len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))}
  pair.append(r);records.append(r)
 row.update(actual_pair=pair,new_current79_canonical_standalone_and_named_pair_pending=False,evidence_scope='Genuine current79 canonical standalone and named per-file pair. Exact original Source65 TMP histories/full semantic decisions retained. Full Root90 batch completion, final readiness, selected aggregate30 and owner integration are separate pending gates.')
 for r in pair:
  for fld in ['actual_record','raw_log','source_snapshot','root_helper_invocation_raw']:row['evidence_sha256'][r[fld]['file']]=r[fld]['sha256']
 row['evidence_sha256'][dest]=h
assert len(records)==54 and len(proofs)==27
base=D.relative_to(R).as_posix();reportfile=base+'/foundations30-current79-actual27-source54-command-per-file-pair-report-v1.json';ifile=base+'/foundations30-current79-real54-canonical-binding-exact-inverse-v1.json';cfile=base+'/foundations30-current79-real54-pair-bound-candidate-v1.json';ofile=base+'/foundations30-current79-real54-pair-bound-offer-v1.json'
report={'status':'passed_actual_Foundation30_27_source54_per_file_canonical_pairs_only','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':27,'public_theorem_body_count':370,'actual_compiler_command_count':54,'actual_paired_records':records,'exact_approved_provisional_offer':ref(OLD),'common45_plan':ref(PLAN),'common_actual_runner':ref(RUNNER),'common_full90_runner_completion_claimed':False,'final_common90_readiness_claimed':False,'aggregate30_kernel_or_axiom_audit_claimed':False,'owner_installation_or_selection_or_publication_claimed':False,'canonical_compiler_executed_by_this_binder':False,'original_native_times_fields_body_and_raw_logs_preserved':True,'protected_source79_1197_31_raw5_guard':{k:copy.deepcopy(context[k]) for k in ['pins_sha256','held_current_source_sha256','owners_sha256']},'coverage_complete':False}
reportbytes=data(report);reportref={'file':reportfile,'sha256':hashlib.sha256(reportbytes).hexdigest(),'bytes':len(reportbytes)}
for i,row in enumerate(prior['material_claims']):
 if 'new_canonical_source' not in row:continue
 dest=row['new_canonical_source'];assert dest in proofs and row['new_canonical_standalone_and_named_pair_pending'] is True
 change(['material_claims',i,'new_canonical_standalone_and_named_pair_pending'],False)
 change(['material_claims',i,'actual_current79_canonical_pair'],proofs[dest]['actual_pair'])
 q=row['source_review'];alias=aliases.get(q['file'])
 if alias is None:alias=aliases.get(str(path(q['file'])))
 if alias is not None and alias!=q:change(['material_claims',i,'source_review'],alias)
assert sum('actual_current79_canonical_pair' in row for row in candidate['material_claims'])==67
mapping=copy.deepcopy(prior['current30_material_mapping']);mapping.update(exact_interface={'file':ifile},original_provisional_exact_interface=d['exact_interface'],approved_scope_plan=d['approved_scope_plan'],actual_canonical_pair_report=reportref,new_canonical_pairs_pending=False,actual_canonical_compiler_commands=54,common90_final_readiness_and_global_review_pending=True,final_independent_mapping_review_pending=True)
change(['current30_material_mapping'],mapping)
identity=copy.deepcopy(prior['current79_owner_identity']);identity['actual79_TMP_guard_context']=d['actual79_context'];change(['current79_owner_identity'],identity)
change(['current30_canonical_bindings'],{'proof_files':proofs,'source_count':27,'public_theorem_body_count':370,'compiler_command_count':54,'actual_per_file_pair_report':reportref,'common90_final_runner_and_readiness_pending':True,'scope':'58 whole keys covering63 previously pending mathematical clauses,3 individually nonformal references,4 component-only additions. No neighboring whole inference, selected aggregate or installed owner claim.'})
reverse=copy.deepcopy(candidate)
for ch in reversed(changes):
 cur=reverse
 for k in ch['path'][:-1]:cur=cur[k]
 assert cur[ch['path'][-1]]==ch['after']
 if ch['before_present']:cur[ch['path'][-1]]=copy.deepcopy(ch['before'])
 else:del cur[ch['path'][-1]]
assert reverse==prior and data(reverse)==prior_bytes
oldowner=read(d['original_installed29_ledger']['file']);reverse.pop('current79_owner_identity');reverse.pop('current30_material_mapping');reverse['material_claims']=reverse['material_claims'][:-4]
for row in interface['individual66_pending_row_replacements']:reverse['material_claims'][row['index']]=copy.deepcopy(row['rebased_pending_row'])
for ch in reversed(interface['source_identity_field_changes']):
 row=reverse[ch['table']][ch['index']]
 for fld,v in ch['field_changes'].items():assert row[fld]==v['after'];row[fld]=v['before']
for k in ['source_sha256','proof_files','proof_sha256','counts']:reverse[k]=copy.deepcopy(oldowner[k])
assert reverse==oldowner and data(reverse)==path(d['original_installed29_ledger']['file']).read_bytes()
iface={'status':'passed_actual54_per_file_canonical_metadata_binding_and_exact_composed_owner29_inverse_pending_independent_full_mapping','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_current79_provisional_candidate':d['candidate'],'original_current79_qualified_material_inverse':d['exact_interface'],'canonical_metadata_changes':changes,'mapping_interface_hash_finalization_rule':'After hashing this interface, current30_material_mapping.exact_interface receives this SHA. Reverse first by restoring its SHA-absent ref from canonical_metadata_changes.after, then apply changes backwards; the exact provisional interface gives the remaining full owner29 inverse.','exact_reverse_restores_original_current79_provisional_candidate_bytes':True,'exact_composed_reverse_restores_entire_original_owner29_bytes':True,'all119_exercises1141_old_proved_semantic_bodies_and_original_native_review_times_retained':True,'actual_pair_report':reportref,'new_whole_math_material_keys':58,'new_math_pending_rows':63,'new_nonformal_rows':3,'new_component_only_rows':4,'source_public_bodies_actual_commands':[27,370,54],'common90_outer_final_readiness_still_pending':True,'final_independent_mapping_peer_pending':True,'coverage_complete':False}
ibytes=data(iface);iref={'file':ifile,'sha256':hashlib.sha256(ibytes).hexdigest(),'bytes':len(ibytes)};candidate['current30_material_mapping']['exact_interface']=iref
cbytes=data(candidate);cref={'file':cfile,'sha256':hashlib.sha256(cbytes).hexdigest(),'bytes':len(cbytes)}
offer=copy.deepcopy(d);offer.update(status='closed_current79_Foundation_owner30_actual27_source54_per_file_pair_bound_candidate_pending_full_mapping_and_common90_readiness',prepared_at_utc=datetime.now(timezone.utc).isoformat(),candidate=cref,mapped_ledger=cfile,mapped_ledger_sha256=cref['sha256'],exact_interface=iref,original_current79_provisional_offer=ref(OLD),original_pending_current79_exact_interface=d['exact_interface'],proof_files=proofs,actual_canonical_pair_report=reportref,all_new_actual_canonical_pairs_pending=False,new_actual_canonical_compiler_commands=54,common90_outer_runner_and_final_readiness_pending=True,final_independent_mapping_review_pending=True,candidate_preparation_actual_pending=True,selection_aggregate_or_installed_owner_claimed=False)
requirements.update({reportfile:reportref['sha256'],ifile:iref['sha256'],cfile:cref['sha256']});offer['required_evidence_artifacts_sha256']=requirements;offer['additional_frozen_inputs']=requirements
planned={R/reportfile:reportbytes,R/ifile:ibytes,R/cfile:cbytes,R/ofile:data(offer)}
assert guard()==before
for p,b in planned.items():assert p.is_relative_to(D) and not p.exists()
for p,b in planned.items():p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
assert guard()==before
print(json.dumps({'candidate':cref,'offer':ref(R/ofile),'exact_interface':iref,'actual_per_file_pair_report':reportref,'source_public_bodies_commands':[27,370,54],'whole_keys_rows':[58,63],'NF_rows':3,'component_rows':4,'counts':candidate['counts']['material_claim_statuses'],'physical_pending':354,'exact_composed_inverse':True,'common90_final_readiness_claimed':False,'errors':[]}))
