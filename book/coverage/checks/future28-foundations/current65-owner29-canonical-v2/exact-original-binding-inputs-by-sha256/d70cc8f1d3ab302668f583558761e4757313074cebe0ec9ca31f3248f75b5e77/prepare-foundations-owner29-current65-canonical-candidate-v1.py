from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,re
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/current65-owner29-canonical-v1';assert not D.exists()
BASE='book/coverage/checks/future28-foundations/current65-owner29-association-v1/'
OLD=BASE+'foundations29-current65-provisional-candidate-v1.json'
OFFER=BASE+'foundations29-current65-provisional-offer-draft-v1.json'
READY='book/coverage/checks/future29-core/current65-canonical-pairs10-v1/actual-reviewed29-canonical-paired-readiness-v1.json'
OUTER='reports/full-coverage/current65-canonical-pairs10-application29-execution-v1.json'
EXECUTOR='book/coverage/checks/run_root29_reviewed_canonical_pairs_v1.py'
EXECUTOR_SHA='d1d4358d68e183ad3d4fee48735d2bd99572a5c640c8be5d9ea753abc61af141'
def path(n):
 p=Path(n);return p if p.is_absolute() else R/p
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def read(n):return json.loads(path(n).read_bytes())
def ref(n):
 p=path(n);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(n)}
def checked(r):assert sha(r['file'])==r['sha256'],r['file'];return read(r['file'])
def data(x):return (json.dumps(x,indent=2)+'\n').encode()
def zero(d):
 vals=[d[k] for k in ['exit_code','actual_exit_code','actual_runner_exit_code'] if k in d]
 assert vals and all(type(v) is int and v==0 for v in vals)
 assert d.get('protection_errors',[])==[]
def actual(d,cmd,cwd):
 zero(d);assert d.get('status')=='passed'
 ks=[k for k in ['command','actual_command'] if k in d];assert ks and all(d[k]==cmd for k in ks)
 ks=[k for k in ['cwd','working_directory','actual_workdir','workdir'] if k in d];assert ks and all(d[k]==cwd for k in ks)
assert sha(OLD)=='79466b3aabad1f6d4661d7d65dd23dd476f894d446a9c800995827f37e7539b8'
assert sha(OFFER)=='4a044e4c536edcab6aa01c5580d261bd6f0b50bfc5566c483c3b185dc42ddc0c'
assert sha(READY)=='69a560ae42809ecaf8a11e0b6492fd411691e4c928a83684ced9c29936492917'
assert sha(OUTER)=='ccd8d152e579e60a97b09cf0d1d4477414133ae79aef8622d28cd987a70305c4'
assert sha(EXECUTOR)==EXECUTOR_SHA
started=datetime.now(timezone.utc).isoformat();prior=read(OLD);oldoffer=read(OFFER);ready=read(READY);outer=read(OUTER);context=checked(oldoffer['current65_original_context'])
def guard():
 for field in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in context[field].items():assert sha(n)==h,n
 for n,h in ready['protected_inputs_sha256'].items():assert sha(n)==h,n
 assert sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction65.json')==oldoffer['inventory_sha256']
 assert sha(OLD)=='79466b3aabad1f6d4661d7d65dd23dd476f894d446a9c800995827f37e7539b8' and sha(OFFER)=='4a044e4c536edcab6aa01c5580d261bd6f0b50bfc5566c483c3b185dc42ddc0c'
 assert sha(READY)=='69a560ae42809ecaf8a11e0b6492fd411691e4c928a83684ced9c29936492917' and sha(OUTER)=='ccd8d152e579e60a97b09cf0d1d4477414133ae79aef8622d28cd987a70305c4'
 return {k:copy.deepcopy(context[k]) for k in ['pins_sha256','held_current_source_sha256','owners_sha256']}
before=guard();assert ready['status']=='passed_actual_reviewed29_canonical_standalone_and_named_pairs_unselected' and ready['errors']==[]
assert (ready['source_count'],ready['public_theorem_count'],ready['actual_compiler_command_count'])==(10,202,20)
assert ready['coverage_complete'] is False and ready['selection_aggregate_owner_or_publication_claimed'] is False
actual(outer,['python3',EXECUTOR,'--plan','book/coverage/checks/future29-core/current65-canonical-plan10-v1.json','--plan-sha256','c52479b0decac7ad29160ec198e4c6ebce8c42948603939c55080ce71bbdb49b','--apply'],str(R))
assert outer['helper_sha256_before']==outer['helper_sha256_after']=={EXECUTOR:EXECUTOR_SHA};assert sha(outer['log'])==outer['log_sha256']
assert checked(ready['context'])==context
last=json.loads(path(outer['log']).read_text().splitlines()[-1]);assert last['readiness']==ref(READY) and last['actual_commands']==20
spec=importlib.util.spec_from_file_location('foundation29_names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
assert sha('book/coverage/lean_names.py')=='9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d'
sources={r['canonical_source']:r for r in ready['sources']};assert len(sources)==10
pairs={(p['source']['file'],p['kind']):p for p in ready['actual_paired_records']};assert len(pairs)==20
base=D.relative_to(R).as_posix();planned={};archive_aliases={}
def archive(r):
 p=path(r['file']);assert sha(r['file'])==r['sha256'];q=D/'exact-original-binding-inputs-by-sha256'/r['sha256']/p.name
 if q in planned:assert planned[q]==p.read_bytes()
 planned[q]=p.read_bytes();a={'file':q.relative_to(R).as_posix(),'sha256':r['sha256']};archive_aliases[r['file']]=a;return a
outerref=archive(ref(OUTER));rawref=archive(ref(outer['log']));executorref=archive(ref(EXECUTOR))
proofs=copy.deepcopy(oldoffer['proof_files']);assert len(proofs)==6
requirements=dict(oldoffer['additional_frozen_inputs'])
def include(r):
 assert type(r) is dict and sha(r['file'])==r['sha256']
 p=path(r['file']);assert p.is_relative_to(R);n=p.relative_to(R).as_posix()
 if n in requirements:assert requirements[n]==r['sha256']
 requirements[n]=r['sha256']
def allrefs(x):
 if isinstance(x,dict):
  if type(x.get('file')) is str and type(x.get('sha256')) is str and re.fullmatch('[0-9a-f]{64}',x['sha256']):include(x)
  for v in x.values():allrefs(v)
 elif isinstance(x,list):
  for v in x:allrefs(v)
for n,row in proofs.items():
 s=sources[n];h=row['sha256'];assert sha(n)==h==s['original_tmp_source']['sha256']
 decls=names.declarations(path(n).read_text());assert decls==s['public_declarations']
 theoremnames=[d['name'] for d in decls if d['kind'] in ['theorem','lemma']]
 assert theoremnames==row['public_theorem_names'] and len(theoremnames)==row['theorem_count']==s['public_theorem_count']
 pair=[]
 for kind in ['standalone','named']:
  p=copy.deepcopy(pairs[(n,kind)]);zero(p);assert p['source']=={'file':n,'sha256':h}
  a=checked(p['actual_record']);cmd=['lake','env','lean','SafeLearning/'+Path(n).name] if kind=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
  actual(a,cmd,str(R/'verification/lean'));assert a['source']==n and a['source_sha256_before']==a['source_sha256_after']==h and a['source_unchanged'] is True
  assert sha(p['raw_log']['file'])==p['raw_log']['sha256']==a['log_sha256'] and p['raw_log']['file']==a['log']
  assert sha(p['source_snapshot']['file'])==p['source_snapshot']['sha256']==h
  pair.append(p)
 row.update(actual_pair=pair,new_current64_or_later_canonical_standalone_and_named_pair_pending=False,
  actual_current65_canonical_readiness=ref(READY),actual_current65_canonical_outer_execution=outerref,
  source_level_public_declarations=decls,
  evidence_scope='Genuine current65 canonical standalone and named build pair, exact historical TMP failures/passes and original full source correspondence decision. No selected aggregate29 or installed owner claim.')
 es=dict(row['evidence_sha256'])
 for p in pair:
  for fld in ['actual_record','raw_log','source_snapshot']:es[p[fld]['file']]=p[fld]['sha256']
 for r in [ref(READY),outerref,rawref,executorref]:es[r['file']]=r['sha256']
 row['evidence_sha256']=es
 for f,h0 in es.items():include({'file':f,'sha256':h0})
 allrefs(row)
assert sum(v['theorem_count'] for v in proofs.values())==53
candidate=copy.deepcopy(prior);changes=[]
def change(keys,value):
 p=candidate
 for k in keys[:-1]:p=p[k]
 present=keys[-1] in p;old=copy.deepcopy(p.get(keys[-1]));p[keys[-1]]=copy.deepcopy(value)
 changes.append({'path':keys,'before_present':present,'before':old,'after':copy.deepcopy(value)})
oldiface=checked(oldoffer['exact_interface']);math=[r for r in oldiface['sixteen_individual_row_replacements'] if r['classification']=='whole_math'];assert len(math)==8
for r in math:
 i=r['original_index'];row=candidate['material_claims'][i];assert row==r['new_row'];n=row['new_canonical_source']
 change(['material_claims',i,'new_canonical_standalone_and_named_pair_pending'],False)
 change(['material_claims',i,'actual_current65_canonical_pair'],proofs[n]['actual_pair'])
support=copy.deepcopy(candidate['current29_source_qualification_support'])
for s in support:
 n=s.pop('canonical_source_pending');s.update(canonical_source=n,actual_current65_canonical_pair=proofs[n]['actual_pair'],whole_literal_approval=False)
change(['current29_source_qualification_support'],support)
interfacepath=base+'/foundations29-current65-canonical-binding-exact-inverse-v1.json'
mapping=copy.deepcopy(candidate['current29_material_mapping']);mapping.update(exact_interface={'file':interfacepath},original_pending64_exact_interface=oldoffer['exact_interface'],actual_canonical_readiness=ref(READY),actual_canonical_outer_execution=outerref,new_canonical_pairs_pending=False,actual_canonical_compiler_commands=12,final_independent_mapping_review_pending=True,original65_provisional_candidate=ref(OLD))
# The interface SHA is inserted after its payload is fixed; it is recorded separately in the inverse.
change(['current29_material_mapping'],mapping)
change(['current29_canonical_bindings'],{'proof_files':proofs,'source_count':6,'public_theorem_body_count':53,'whole_mathematical_body_count':46,'correction_support_body_count':7,'compiler_command_count':12,'actual_readiness':ref(READY),'actual_outer_execution':outerref,'scope':'Eight whole mathematical literals and eight individually nonformal bibliography rows; seven source correction-support bodies do not promote additional whole units. Independent final mapping and aggregate29 remain pending.'})
reversed_candidate=copy.deepcopy(candidate)
for c0 in reversed(changes):
 p=reversed_candidate
 for k in c0['path'][:-1]:p=p[k]
 assert p[c0['path'][-1]]==c0['after']
 if c0['before_present']:p[c0['path'][-1]]=copy.deepcopy(c0['before'])
 else:del p[c0['path'][-1]]
assert reversed_candidate==prior and data(reversed_candidate)==path(OLD).read_bytes()
raw64=copy.deepcopy(reversed_candidate);raw64.pop('current65_owner_identity');assert data(raw64)==path(prior['current65_owner_identity']['original_current64_candidate']['file']).read_bytes()
oldowner=checked(oldoffer['original_installed28_ledger']);reverse=copy.deepcopy(raw64)
for k in ['current64_owner_identity','current29_material_mapping','current29_source_qualification_support']:reverse.pop(k)
for k in ['source_sha256','proof_files','proof_sha256','counts']:reverse[k]=copy.deepcopy(oldowner[k])
for r in oldiface['sixteen_individual_row_replacements']:reverse['material_claims'][r['original_index']]=copy.deepcopy(r['rebased_pending_row'])
for c0 in reversed(oldiface['source_identity_field_changes']):
 row=reverse[c0['table']][c0['index']]
 for fld,v in c0['field_changes'].items():assert row[fld]==v['after'];row[fld]=v['before']
assert reverse==oldowner and candidate['exercises']==oldowner['exercises'] and len(candidate['exercises'])==119
stamp=datetime.now(timezone.utc).isoformat();interface={'status':'passed_exact_current65_canonical_metadata_binding_and_full_owner28_inverse','errors':[],'prepared_at_utc':stamp,'original65_candidate':ref(OLD),'original64_inverse':oldoffer['exact_interface'],'inventory':oldoffer['inventory'],'actual_pairs':ref(READY),'outer_execution':outerref,'canonical_metadata_changes':changes,'mapping_interface_hash_finalization_rule':'After hashing this interface, candidate current29_material_mapping.exact_interface gets this file SHA. To reverse, first replace that one ref with its SHA-absent copy in canonical_metadata_changes.after, then apply the recorded reverse changes.','exact_reverse_restores_original65_candidate_bytes':True,'exact_composed_reverse_restores_entire_original_owner28':True,'all119_exercises_and1133_previous_proved_semantic_bodies_times_retained':True,'new_whole_math_material_units':8,'new_nonformal_rows':8,'source_public_bodies_and_actual_commands':[6,53,12],'final_independent_mapping_review_pending':True,'coverage_complete':False}
interfacebytes=data(interface);interfaceref={'file':interfacepath,'sha256':hashlib.sha256(interfacebytes).hexdigest()};candidate['current29_material_mapping']['exact_interface']=interfaceref
candidatepath=base+'/foundations29-current65-canonical-candidate-v1.json';candidatebytes=data(candidate);candidateref={'file':candidatepath,'sha256':hashlib.sha256(candidatebytes).hexdigest()}
for r in [ref(OLD),ref(OFFER),oldoffer['exact_interface'],oldoffer['current65_inventory_association_interface'],ref(BASE+'foundations29-current65-inventory-association-preparation-closure-v1.json'),ref(READY),oldoffer['inventory']]:include(r)
allrefs(proofs);allrefs(candidate['current65_owner_identity'])
for n,h in requirements.items():assert not Path(n).is_absolute() and sha(n)==h,n
offer=copy.deepcopy(oldoffer);offer.update(status='prepared_current65_foundations29_canonical_eight_math_eight_reference_candidate_pending_independent_final_mapping',started_at_utc=started,prepared_at_utc=stamp,candidate=candidateref,mapped_ledger=candidatepath,mapped_ledger_sha256=candidateref['sha256'],proof_files=proofs,exact_interface=interfaceref,original_pending64_exact_interface=oldoffer['exact_interface'],actual_canonical_readiness=ref(READY),actual_canonical_outer_execution=outerref,all_new_actual_canonical_pairs_pending=False,new_actual_canonical_compiler_commands=12,original_current65_provisional_offer=ref(OFFER),additional_frozen_inputs=requirements,required_evidence_artifacts_sha256={**requirements,interfacepath:interfaceref['sha256']},candidate_preparation_actual_pending=True,independent_final_candidate_mapping_peer_pending=True,selection_aggregate_or_installed_owner_claimed=False)
offerpath=base+'/foundations29-current65-canonical-offer-draft-v1.json';planned.update({R/candidatepath:candidatebytes,R/interfacepath:interfacebytes,R/offerpath:data(offer)})
assert guard()==before
for p,b in planned.items():assert p.is_relative_to(D) and not p.exists()
for p,b in planned.items():p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
assert guard()==before
print(json.dumps({'status':offer['status'],'candidate':candidateref,'draft_offer':ref(offerpath),'exact_interface':interfaceref,'counts':candidate['counts'],'physical_pending':415,'six_sources_public_bodies_actual_commands':[6,53,12],'exact_composed_inverse':True,'required_evidence_count':len(offer['required_evidence_artifacts_sha256']),'original_binding_input_aliases':archive_aliases,'coverage_complete':False}))
