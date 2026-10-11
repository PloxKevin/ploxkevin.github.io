"""Read-only selector26 review with isolated explicitly synthetic authorization and pair fixtures."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');FIX=Path('/tmp/applied-checkpoint26-selector-retainer-fixtures-v1');OUT=Path('/tmp/checkpoint26-selector-retainer-independent-applied-review-v1.json')
assert not FIX.exists() and not OUT.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();R=lambda p:json.loads(Path(p).read_text())
reqname='book/coverage/checks/future26-core/modules26-engineering-unexecuted-draft-readiness-v3.json';req=R(ROOT/reqname)
helper_hashes={'book/coverage/prepare_checkpoint26_selection_v2.py':'9e130aa89131e3fb9cd860ee898d95a9fd92e6fbe33723913c5ff5c86dcde3d9','book/coverage/retain_baseline_inputs26_v2.py':'86ecc3a33de29841aaa6e117d56390305502e6f238151674890ce2e67c60302e'}
bodies={}
for n,h in helper_hashes.items():assert H(ROOT/n)==h;bodies[n]=(ROOT/n).read_text();ast.parse(bodies[n])
for row in req['immutable_original_helpers'].values():assert H(ROOT/row['file'])==row['sha256']
parent_selector=(ROOT/'book/coverage/prepare_checkpoint25_selection_v3.py').read_text()
def function_body(text,name):return ast.dump(next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)and n.name==name),include_attributes=False)
for name in ['safe','sha','read','exact','checked','actual_exit_zero','standalone_success']:assert function_body(parent_selector,name)==function_body(bodies['book/coverage/prepare_checkpoint26_selection_v2.py'],name)
sys.dont_write_bytecode=True;sys.path.insert(0,str(ROOT/'book/coverage'))
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
retainer=load('independent_retainer26',ROOT/'book/coverage/retain_baseline_inputs26_v2.py');selector=load('independent_selector26',ROOT/'book/coverage/prepare_checkpoint26_selection_v2.py')
bn=selector.BASELINE;mn=selector.MANIFEST
assert H(ROOT/bn)==selector.BASELINE_SHA and H(ROOT/mn)==selector.MANIFEST_SHA and H(ROOT/selector.AUDIT)==selector.AUDIT_SHA
b=R(ROOT/bn);m=R(ROOT/mn);assert m['proof_files']==b['proof_files']and len(b['proof_files'])==1156 and len(m['frozen_inputs_sha256'])==44111
owners=retainer.OWNER_EVIDENCE_PATHS;old={n:m['working_inputs_sha256'][n]for n in owners};raw_applied=old['book/coverage/applied.json'];frozen_applied=m['frozen_inputs_sha256']['book/coverage/applied.json'];assert raw_applied!=frozen_applied
protected={n:H(ROOT/n)for n in sorted(owners|{'book/coverage/applied-promotions.json','book/coverage/inventory.json'})}
for n in owners:assert H(ROOT/n)==old[n]
ordinary={}
for source,row in b['proof_files'].items():
 assert H(ROOT/source)==row['sha256']
 for n,h in row['evidence_sha256'].items():assert n not in ordinary or ordinary[n]==h;ordinary[n]=h
for n,h in ordinary.items():assert H(ROOT/n)==h,n
for n in owners:
 occurrences=[r for r in b['proof_files'].values()if n in r['evidence_sha256']];assert occurrences and all(r['evidence_sha256'][n]==old[n]for r in occurrences)
paths={'foundations':'book/coverage/checks/foundations-future26/source53/foundations-audit26-candidate-source53-additions-v1-reviewed.json','applied':'book/coverage/checks/applied-future26/source53-v2/applied-audit26-candidate-source53-additions-v1-reviewed.json','modules':'book/coverage/checks/modules-future26/source53/modules-audit26-candidate-source53-additions-v1-reviewed.json'}
real_offers={};refs={};pairs=[]
for owner,n in paths.items():
 offer=R(ROOT/n);real_offers[n]=H(ROOT/n);ref={'file':offer['mapped_ledger'],'sha256':offer['mapped_ledger_sha256']};assert H(ROOT/ref['file'])==ref['sha256'];refs['book/coverage/'+owner+'.json']=ref
 for source,row in offer['proof_files'].items():
  assert H(ROOT/source)==row['sha256'];record=selector.standalone_success(source,row['sha256'],row['evidence_sha256']);pairs.append({'source':source,'sha256':row['sha256'],'actual_standalone_record':record,'native_evidence_origin':n})
cn='book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-v1.json';core=R(ROOT/cn);refs['book/coverage/core.json']={'file':cn,'sha256':H(ROOT/cn)}
for row in core['future26_composed_candidate_binding']['new_proof_sources']:
 source=row['source']['file'];digest=row['source']['sha256'];ev={row['source_snapshot']['file']:row['source_snapshot']['sha256']}
 for r in row['pair']:ev[r['file']]=r['sha256'];ev[r['log']['file']]=r['log']['sha256']
 record=selector.standalone_success(source,digest,ev);pairs.append({'source':source,'sha256':digest,'actual_standalone_record':record,'native_evidence_origin':'Exact fixed Core26 candidate source/pair rows before final offer packaging'})
assert len(pairs)==len({r['source']for r in pairs})==11
FIX.mkdir()
def put(n,data):p=FIX/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def putj(n,obj):put(n,(json.dumps(obj,indent=2)+'\n').encode())
for n in owners:
 put(n,(ROOT/refs[n]['file']).read_bytes());put(refs[n]['file'],(ROOT/refs[n]['file']).read_bytes())
 put('reports/full-coverage/owner25-originals-before-owner26-integration-v1/'+Path(n).name,(ROOT/n).read_bytes())
 put(m['snapshot']+'/'+n,(ROOT/(m['snapshot']+'/'+n)).read_bytes())
helper='book/coverage/checks/root_integrate_owner26_candidates_v2.py';put(helper,(ROOT/helper).read_bytes())
binding='book/coverage/checks/synthetic-owner26-code-fixture-binding.json';putj(binding,{'synthetic_fixture_only':True})
log='reports/full-coverage/synthetic-owner26-code-fixture-apply.log';put(log,b'SYNTHETIC code fixture only, no actual integration.\n')
resname='reports/full-coverage/synthetic-owner26-code-fixture-result.json';exname='reports/full-coverage/synthetic-owner26-code-fixture-record.json'
replacements=[{'destination':n,'before_sha256':old[n],'candidate':refs[n],'original25_byte_copy':'reports/full-coverage/owner25-originals-before-owner26-integration-v1/'+Path(n).name} for n in sorted(owners)]
aux='book/coverage/applied-promotions.json';put(aux,(ROOT/aux).read_bytes());replacements.append({'destination':aux,'before_sha256':H(ROOT/aux),'candidate':{'file':aux,'sha256':H(ROOT/aux)},'original25_byte_copy':'reports/full-coverage/owner25-originals-before-owner26-integration-v1/applied-promotions.json'})
result={'status':'four_exact_reviewed_owner26_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate25_audit','applied':True,'actual_helper':helper,'actual_helper_sha256':H(FIX/helper),'binding_manifest':binding,'binding_manifest_sha256':H(FIX/binding),'exact_replacements':replacements,'synthetic_fixture_only':True}
execution={'actual_exit_code':0,'actual_command':['python3',helper,binding,'--apply'],'actual_workdir':str(FIX),'helper_sha256_before':{helper:H(FIX/helper)},'helper_sha256_after':{helper:H(FIX/helper)},'log':log,'log_sha256':H(FIX/log),'synthetic_fixture_only':True}
putj(resname,result);putj(exname,execution)
source='verification/lean/SafeLearning/SyntheticRetentionCodeFixture.lean';ordname='book/coverage/checks/synthetic-ordinary-evidence.txt';put(source,b'-- Synthetic code fixture only; no Lean compile.\n');put(ordname,b'Exact ordinary fixture bytes.\n')
real_old_row=next(r for r in b['proof_files'].values() if 'checkpoint25_original_baseline_owner_evidence' in r)
row={'sha256':H(FIX/source),'evidence_sha256':{ordname:H(FIX/ordname),**old},'original_review_time':'synthetic metadata only','checkpoint25_original_baseline_owner_evidence':copy.deepcopy(real_old_row['checkpoint25_original_baseline_owner_evidence'])}
fb={'status':'synthetic_fixture_requires_fresh_aggregate_audit','proof_files':{source:row},'extra_frozen_inputs':{}};putj(bn,fb)
frozen={source:H(FIX/source),ordname:H(FIX/ordname)}
for n in list(frozen):put(m['snapshot']+'/'+n,(FIX/n).read_bytes())
for n in owners:frozen[n]=H(FIX/(m['snapshot']+'/'+n))
fm={'status':'formal_verification_passed_partial_coverage','selection':bn,'selection_sha256':H(FIX/bn),'proof_files':fb['proof_files'],'snapshot':m['snapshot'],'frozen_inputs_sha256':frozen,'working_inputs_sha256':old,'synthetic_fixture_only':True};putj(mn,fm)
aliases={n:{'original_sha256':old[n],'immutable_byte_copy':{'file':'reports/full-coverage/owner25-originals-before-owner26-integration-v1/'+Path(n).name,'sha256':old[n]}} for n in owners}
ref=lambda n:{'file':n,'sha256':H(FIX/n)}
auth={'actual_integration_execution':ref(exname),'integration_result':ref(resname),'aliases':aliases};fixtures=[]
assert retainer.validate_owner_evidence_aliases(FIX,bn,mn,auth)==aliases;fixtures.append({'label':'exact_four_synthetic_old_archives_and_current_candidate_bytes','observed':'accepted','synthetic_only':True})
def reject_auth(label,fn):
 a=copy.deepcopy(auth);fn(a)
 try:retainer.validate_owner_evidence_aliases(FIX,bn,mn,a)
 except (AssertionError,KeyError,FileNotFoundError,ValueError):fixtures.append({'label':label,'observed':'rejected','synthetic_only':True})
 else:raise AssertionError('Bad authorization accepted: '+label)
reject_auth('missing_owner',lambda a:a['aliases'].pop('book/coverage/core.json'));reject_auth('unauthorized_fifth_owner',lambda a:a['aliases'].update({aux:aliases['book/coverage/applied.json']}))
reject_auth('old_raw_hash_drift',lambda a:a['aliases']['book/coverage/core.json'].update(original_sha256='0'*64));reject_auth('pruned_frozen_Applied_substitutes_unpruned_raw',lambda a:a['aliases']['book/coverage/applied.json'].update(original_sha256=frozen_applied))
reject_auth('archive_hash_drift',lambda a:a['aliases']['book/coverage/core.json']['immutable_byte_copy'].update(sha256='0'*64));reject_auth('same_hash_wrong_archive_path',lambda a:a['aliases']['book/coverage/core.json']['immutable_byte_copy'].update(file='book/coverage/core.json'))
reject_auth('execution_pointer_drift',lambda a:a['actual_integration_execution'].update(sha256='0'*64));reject_auth('result_pointer_drift',lambda a:a['integration_result'].update(sha256='0'*64))
def variant(label,kind,fn):
 d=copy.deepcopy(execution if kind=='execution' else result);fn(d);n='reports/full-coverage/synthetic-'+label+'.json';putj(n,d)
 reject_auth(label,lambda a:a.update({('actual_integration_execution' if kind=='execution' else 'integration_result'):ref(n)}))
variant('failed_execution','execution',lambda d:d.update(actual_exit_code=1));variant('conflicting_exit_codes','execution',lambda d:d.update(exit_code=1));variant('boolean_exit','execution',lambda d:d.update(actual_exit_code=False))
variant('missing_apply_command','execution',lambda d:d.update(actual_command=['python3',helper,binding]));variant('wrong_helper_command','execution',lambda d:d.update(actual_command=['python3','book/coverage/checks/root_integrate_owner25_candidates_v3.py',binding,'--apply']))
variant('wrong_workdir','execution',lambda d:d.update(actual_workdir=str(FIX/'other')));variant('changed_helper_after','execution',lambda d:d['helper_sha256_after'].update({helper:'0'*64}));variant('unapplied_dry_run','result',lambda d:d.update(applied=False))
variant('changed_before_hash','result',lambda d:d['exact_replacements'][0].update(before_sha256='0'*64));variant('wrong_archive_field','result',lambda d:d['exact_replacements'][0].update(original25_byte_copy='reports/full-coverage/other.json'))
normalized,used=retainer.normalized_baseline_owner_evidence(row,aliases);assert fb['proof_files'][source]==row
selected_row=copy.deepcopy(row);selected_row['evidence_sha256']={**normalized,**{n:refs[n]['sha256'] for n in owners}};selected_row['checkpoint26_original_baseline_owner_evidence']={'original_baseline_selection':ref(bn),'original_baseline_source':source,'original_row_body':copy.deepcopy(row),'authorized_original_path_aliases':used}
selected={source:copy.deepcopy(selected_row)};retained=retainer.retain(FIX,bn,mn,selected,{},'book/coverage/checks/positive-synthetic-content-map.json',auth);content=R(FIX/retained['file'])
assert {r['original_frozen_path']:r['sha256'] for r in content['input_bindings']}==frozen
assert selected[source]['checkpoint25_original_baseline_owner_evidence']==row['checkpoint25_original_baseline_owner_evidence'] and selected[source]['checkpoint26_original_baseline_owner_evidence']['original_row_body']==row
appliedrow=next(r for r in content['input_bindings'] if r['original_frozen_path']=='book/coverage/applied.json');assert appliedrow['sha256']==frozen_applied and appliedrow['retained_input']!=aliases['book/coverage/applied.json']['immutable_byte_copy']['file']
fixtures.append({'label':'old_archive_current_raw_and_distinct_pruned_frozen_Applied_coexist_full_prior24_metadata','observed':'accepted','synthetic_only':True})
negatives=[('resurfaced_old_raw',lambda r:r['evidence_sha256'].update({'book/coverage/core.json':old['book/coverage/core.json']})),('arbitrary_current_raw',lambda r:r['evidence_sha256'].update({'book/coverage/core.json':'0'*64})),('pruned_Applied_as_current_raw',lambda r:r['evidence_sha256'].update({'book/coverage/applied.json':frozen_applied})),('missing_archive_alias',lambda r:r['evidence_sha256'].pop(aliases['book/coverage/core.json']['immutable_byte_copy']['file'])),('ordinary_evidence_drift',lambda r:r['evidence_sha256'].update({ordname:'0'*64})),('original_review_time_drift',lambda r:r.update(original_review_time='changed')),('nested_original25_provenance_drift',lambda r:r['checkpoint25_original_baseline_owner_evidence'].update(original_baseline_source='changed')),('entire_original_baseline_row_drift',lambda r:r['checkpoint26_original_baseline_owner_evidence']['original_row_body'].update(original_review_time='changed')),('proof_hash_drift',lambda r:r.update(sha256='0'*64)),('alias_provenance_drift',lambda r:r['checkpoint26_original_baseline_owner_evidence']['authorized_original_path_aliases']['book/coverage/core.json'].update(original_sha256='0'*64))]
for i,(label,fn) in enumerate(negatives):
 rr=copy.deepcopy(selected_row);fn(rr);out='book/coverage/checks/negative-'+str(i)+'.json'
 try:retainer.retain(FIX,bn,mn,{source:rr},{},out,auth)
 except (AssertionError,KeyError,FileNotFoundError,ValueError):assert not (FIX/out).exists();fixtures.append({'label':label,'observed':'rejected_before_output','synthetic_only':True})
 else:raise AssertionError('Bad retention accepted: '+label)
# Pair eligibility fixtures have explicit fabricated records, never actual compiler claims.
selector.ROOT=FIX;pair_source='verification/lean/SafeLearning/SyntheticPairCodeFixture.lean';put(pair_source,b'-- Synthetic pair eligibility fixture; no Lean execution.\n');pd=H(FIX/pair_source);plog='book/coverage/checks/synthetic-pair.log';put(plog,b'SYNTHETIC pair fixture.\n');snapshot='book/coverage/checks/synthetic-pair-source.lean';put(snapshot,(FIX/pair_source).read_bytes())
common={'actual_exit_code':0,'source':pair_source,'source_sha256_before':pd,'source_sha256_after':pd,'actual_workdir':str(FIX/'verification/lean'),'raw_log_sha256':H(FIX/plog),'synthetic_fixture_only':True}
stand={**common,'actual_command':['lake','env','lean','SafeLearning/SyntheticPairCodeFixture.lean'],'source_snapshot_sha256':pd};named={**common,'actual_command':['lake','build','SafeLearning.SyntheticPairCodeFixture'],'source_snapshot_sha256':pd};history={**common,'actual_command':['lake','env','lean','/tmp/synthetic-historical-unsupported.lean']}
sn='book/coverage/checks/synthetic-standalone.json';nn='book/coverage/checks/synthetic-named.json';hn='book/coverage/checks/synthetic-absolute-no-snapshot.json'
putj(sn,stand);putj(nn,named);putj(hn,history)
evidence={n:H(FIX/n) for n in [sn,nn,hn,plog,snapshot]};assert selector.standalone_success(pair_source,pd,evidence)==sn;fixtures.append({'label':'valid_canonical_pair_skips_unsupported_absolute_historical_record','observed':'accepted','synthetic_only':True})
def reject_pair(label,ev):
 try:selector.standalone_success(pair_source,pd,ev)
 except (AssertionError,KeyError,FileNotFoundError,ValueError):fixtures.append({'label':label,'observed':'rejected','synthetic_only':True})
 else:raise AssertionError('Bad pair accepted: '+label)
reject_pair('absolute_historical_without_snapshot_plus_named_not_canonical_pair',{n:h for n,h in evidence.items() if n!=sn});reject_pair('canonical_standalone_without_named',{n:h for n,h in evidence.items() if n!=nn});reject_pair('named_without_any_standalone',{n:h for n,h in evidence.items() if n not in [sn,hn]})
reject_pair('missing_actual_log_evidence',{n:h for n,h in evidence.items() if n!=plog})
for label,fn in [('failed_standalone',lambda d:d.update(actual_exit_code=1)),('conflicting_standalone_exit_codes',lambda d:d.update(exit_code=1)),('wrong_standalone_workdir',lambda d:d.update(actual_workdir=str(FIX/'other'))),('changed_standalone_snapshot_hash',lambda d:d.update(source_snapshot_sha256='0'*64))]:
 d=copy.deepcopy(stand);fn(d);n='book/coverage/checks/synthetic-'+label+'.json';putj(n,d);reject_pair(label,{**{k:h for k,h in evidence.items() if k!=sn},n:H(FIX/n)})
selector.ROOT=ROOT
for n,h in helper_hashes.items():assert H(ROOT/n)==h
for n,h in ordinary.items():assert H(ROOT/n)==h
for n,h in real_offers.items():assert H(ROOT/n)==h
for n,h in protected.items():assert H(ROOT/n)==h
assert not (ROOT/selector.DESTINATION).exists() and not (ROOT/selector.CONTENT_MAP).exists()
report={'status':'passed_independent_checkpoint26_selector_retainer_code_and_isolated_fixture_review_requires_real_installed_owner26_plan_and_production','errors':[],'reviewer':'applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helpers_sha256':helper_hashes,'entire_reviewed_helper_bodies':bodies,'readiness':{'file':reqname,'sha256':H(ROOT/reqname)},'baseline25':req['baseline'],'actual11_native_new_source_pair_schema_reads':pairs,'real_final_offer_sha256':real_offers,'fixtures':fixtures,'fixture_count':len(fixtures),'fixture_directory':str(FIX),'fixture_scope':'All fabricated authorization/record schemas are explicitly synthetic isolated files. Only validator functions were called against them. No production prepare, integration, plan assignment, compiler, selector output or aggregate was executed. Existing11 distinct sources with22 native paired records were separately read and hash-checked.','baseline25_unique_evidence_rehashed':len(ordinary),'all1156_baseline_sources_rehashed':True,'original_unpruned_Applied24_sha256':raw_applied,'distinct_frozen_pruned_Applied24_sha256':frozen_applied,'live_owner_inventory_sha256_before_after_exact':protected,'future_required_actual_gates':['actual_owner26_apply0_and_exact_original25_archives','independent_installed_owner26_interfaces_and_plan','fresh_global_integrity0','genuine_production_selector_output','fresh_frozen25_aggregate_and_publication'],'coverage_complete':False,'scope':'Code and isolated schema/retention review only; no future actual release or integration result is inferred from draft files.'}
previous_name='book/coverage/checks/future26-core/checkpoint26-selector-retainer-independent-applied-review-v2.json'
previous=R(ROOT/previous_name);assert H(ROOT/previous_name)=='61964066e992db19f15029c8229bfb7acb4e8db4a45647c22521fbbb36b034f5'
for old,new in [('book/coverage/retain_baseline_inputs25_v2.py','book/coverage/retain_baseline_inputs26_v2.py'),('book/coverage/prepare_checkpoint26_selection_v2.py','book/coverage/prepare_checkpoint26_selection_v3.py')]:
 text=(ROOT/new).read_text()
 if 'retain_baseline' in old:text=text.replace('root_integrate_owner26_candidates_v2.py','root_integrate_owner26_candidates_v2.py')
 else:text=text.replace('retain_baseline_inputs25_v3','retain_baseline_inputs25_v2')
 assert text==(ROOT/old).read_text()
report['previous_independent_peer_entire_body_and_time']=previous
report['previous_independent_peer']={'file':previous_name,'sha256':H(ROOT/previous_name)}
report['only_declared_code_delta']='Retainer expected integration helper path v2→v3 only; selector import and helper-plan pin refer to unchanged retainer_v3. All real execution/authorization/owner-alias/body/retention/pair gates remain enforced; no singleton mutable-hash authorization is inferred by this code peer.'
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'fixtures':len(fixtures),'native_pairs':11,'report':str(OUT),'sha256':H(OUT)}))
