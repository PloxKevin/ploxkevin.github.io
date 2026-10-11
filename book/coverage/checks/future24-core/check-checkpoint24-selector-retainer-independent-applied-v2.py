"""Read-only independent code review; isolated fixtures are never real executions."""
from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, importlib.util, json, sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/checkpoint24-selector-retainer-independent-applied-review-v2.json')
FIX = Path('/tmp/applied-checkpoint24-selector-retainer-code-fixtures-v2')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
R = lambda p: json.loads(Path(p).read_text())
REQ = 'book/coverage/checks/future24-core/checkpoint24-unexecuted-selector-retainer-code-review-request-v1.json'
assert not OUT.exists() and not FIX.exists()
request = R(ROOT / REQ)
assert H(ROOT / REQ) == 'c3bd98e2c302a0850b64044bd4742e3eb933bed342fa5038b94afcf5a6843df1'
helpers = {r['file']:r['sha256'] for r in request['helpers'].values()}
assert H(ROOT/'book/coverage/prepare_checkpoint24_selection_v2.py') == helpers.pop('book/coverage/prepare_checkpoint24_selection_v2.py')
helpers['book/coverage/prepare_checkpoint24_selection_v3.py']='e584a646250ade2e59e5b9ce05e215cd74f5976e526c5ead79b08da4669d6992'
failed_original=R('/tmp/checkpoint24-selector-retainer-independent-applied-actual-v1.json')
assert failed_original['actual_exit_code']==1 and H(failed_original['log'])==failed_original['log_sha256']
assert 'source_snapshot_sha256' not in R(ROOT/'book/coverage/checks/future24-core/barrier-intro/original-tmp/root-barrier-intro-material24-trial2.json')
old_selector=(ROOT/'book/coverage/prepare_checkpoint24_selection_v2.py').read_text()
new_selector=(ROOT/'book/coverage/prepare_checkpoint24_selection_v3.py').read_text()
patch="            if snapshot_hash is None:\n                # Retain unsupported historical absolute-input executions as\n                # provenance, but do not treat them as canonical pair evidence.\n                # An eligible canonical standalone plus named run is mandatory.\n                continue\n"
assert new_selector.count(patch)==1 and new_selector.replace(patch,'')==old_selector
bodies = {}
for n,d in helpers.items():
    assert H(ROOT/n) == d
    bodies[n] = (ROOT/n).read_text(); ast.parse(bodies[n])
sys.dont_write_bytecode = True
sys.path.insert(0,str(ROOT/'book/coverage'))
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
retainer=load('independent_applied_retainer24_v2',ROOT/'book/coverage/retain_baseline_inputs24_v2.py')
selector=load('independent_applied_selector24_v3',ROOT/'book/coverage/prepare_checkpoint24_selection_v3.py')
baseline_name=request['baseline23']['selection']['file']
manifest_name=request['baseline23']['manifest']['file']
for r in request['baseline23'].values():
    if isinstance(r,dict):assert H(ROOT/r['file'])==r['sha256']
baseline,manifest=R(ROOT/baseline_name),R(ROOT/manifest_name)
assert len(baseline['proof_files'])==1131 and len(manifest['frozen_inputs_sha256'])==36910
assert manifest['proof_files']==baseline['proof_files']
owners=set(request['production_plan_schema']['authorized_owner_alias_names'])
old={n:manifest['working_inputs_sha256'][n] for n in owners}
assert old['book/coverage/applied.json']=='cf35fa4605bd21c1d6b638ab2fecfdd871beea8e7a3b850456b8053832ae9131'
frozen_applied=manifest['frozen_inputs_sha256']['book/coverage/applied.json']
assert frozen_applied!=old['book/coverage/applied.json']
ordinary_evidence={}
for source,row in baseline['proof_files'].items():
    assert H(ROOT/source)==row['sha256']
    for n,d in row['evidence_sha256'].items():
        assert n not in ordinary_evidence or ordinary_evidence[n]==d
        ordinary_evidence[n]=d
for n,d in ordinary_evidence.items():assert H(ROOT/n)==d,n
for n in owners:
    assert H(ROOT/n)==old[n]
    occurrences=[r for r in baseline['proof_files'].values() if n in r['evidence_sha256']]
    assert len(occurrences)==1 and occurrences[0]['evidence_sha256'][n]==old[n]

offer_paths={
 'core':'book/coverage/checks/future24-core/core-audit24-candidate-source51-material-additions-v1-reviewed.json',
 'foundations':'book/coverage/checks/foundations-future24/source51/foundations-audit24-candidate-source51-additions-v1-reviewed.json',
 'applied':'book/coverage/checks/applied-future24/source51/applied-audit24-candidate-source51-additions-v2-reviewed.json',
 'modules':'book/coverage/checks/modules-future24/source51/modules-audit24-candidate-source51-additions-v1-reviewed.json'}
real_offers={};candidate_refs={};paired=[]
for owner,p in offer_paths.items():
    d=R(ROOT/p); real_offers[p]=H(ROOT/p)
    if owner=='core':ref=d['candidate_ledger']
    else:ref={'file':d.get('mapped_ledger',d.get('module_ledger')),'sha256':d.get('mapped_ledger_sha256',d.get('module_ledger_sha256'))}
    assert H(ROOT/ref['file'])==ref['sha256'];candidate_refs['book/coverage/'+owner+'.json']=ref
    for source,row in d['proof_files'].items():
        assert H(ROOT/source)==row['sha256']
        record=selector.standalone_success(source,row['sha256'],row['evidence_sha256'])
        paired.append({'source':source,'sha256':row['sha256'],'actual_standalone_record':record})
assert len(paired)==13 and len({p['source'] for p in paired})==13

FIX.mkdir()
def put(n,b):
    p=FIX/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def putj(n,d):put(n,(json.dumps(d,indent=2)+'\n').encode())
for n in owners:
    put(n,(ROOT/candidate_refs[n]['file']).read_bytes())
    put('reports/full-coverage/owner23-originals-before-owner24-integration-v1/'+Path(n).name,(ROOT/n).read_bytes())
    put(candidate_refs[n]['file'],(ROOT/candidate_refs[n]['file']).read_bytes())
    put(manifest['snapshot']+'/'+n,(ROOT/(manifest['snapshot']+'/'+n)).read_bytes())
helper='book/coverage/checks/root_integrate_owner24_candidates_v2.py'
put(helper,(ROOT/helper).read_bytes())
binding='book/coverage/checks/synthetic-owner24-code-fixture-binding.json'
putj(binding,{'synthetic_fixture_only':True,'scope':'No real integration was executed.'})
log='reports/full-coverage/synthetic-owner24-code-fixture-apply.log'
put(log,b'SYNTHETIC code fixture only; not a tool or integration execution.\n')
result_name='reports/full-coverage/synthetic-owner24-code-fixture-result.json'
execution_name='reports/full-coverage/synthetic-owner24-code-fixture-record.json'
replacements=[]
for n in sorted(owners):
    replacements.append({'destination':n,'before_sha256':old[n],'candidate':candidate_refs[n],
      'original23_byte_copy':'reports/full-coverage/owner23-originals-before-owner24-integration-v1/'+Path(n).name})
aux='book/coverage/applied-promotions.json'
put(aux,(ROOT/aux).read_bytes())
replacements.append({'destination':aux,'before_sha256':H(ROOT/aux),
 'candidate':{'file':aux,'sha256':H(ROOT/aux)},'original23_byte_copy':'reports/full-coverage/owner23-originals-before-owner24-integration-v1/applied-promotions.json'})
result={'status':request['required_owner24_actual_integration']['expected_result_status'],'applied':True,
 'actual_helper':helper,'actual_helper_sha256':H(FIX/helper),'binding_manifest':binding,'binding_manifest_sha256':H(FIX/binding),
 'exact_replacements':replacements,'synthetic_fixture_only':True}
execution={'actual_exit_code':0,'command':['python3',helper,binding,'--apply'],
 'actual_workdir':str(FIX),'helper_sha256_before':{helper:H(FIX/helper)},'helper_sha256_after':{helper:H(FIX/helper)},
 'log':log,'log_sha256':H(FIX/log),'synthetic_fixture_only':True,'scope':'Fabricated schema fixture; no actual success is claimed.'}
putj(result_name,result);putj(execution_name,execution)
source='verification/lean/SafeLearning/SyntheticRetentionCodeFixture.lean'
ordinary='book/coverage/checks/synthetic-ordinary-evidence.txt'
put(source,b'-- Explicit synthetic code fixture. No Lean compilation.\n')
put(ordinary,b'Ordinary exact evidence fixture.\n')
real_old_row=next(r for r in baseline['proof_files'].values() if 'checkpoint23_original_baseline_owner_evidence' in r)
fixture_row={'sha256':H(FIX/source),'evidence_sha256':{ordinary:H(FIX/ordinary),**old},
 'original_review_time':'explicit synthetic metadata; not execution time',
 'checkpoint23_original_baseline_owner_evidence':copy.deepcopy(real_old_row['checkpoint23_original_baseline_owner_evidence'])}
fixture_baseline={'status':'synthetic_fixture_requires_fresh_aggregate_audit','proof_files':{source:fixture_row},'extra_frozen_inputs':{}}
putj(baseline_name,fixture_baseline)
frozen={source:H(FIX/source),ordinary:H(FIX/ordinary)}
for n in list(frozen):put(manifest['snapshot']+'/'+n,(FIX/n).read_bytes())
for n in owners:frozen[n]=H(FIX/(manifest['snapshot']+'/'+n))
fixture_manifest={'status':'formal_verification_passed_partial_coverage','selection':baseline_name,'selection_sha256':H(FIX/baseline_name),
 'proof_files':fixture_baseline['proof_files'],'snapshot':manifest['snapshot'],'frozen_inputs_sha256':frozen,
 'working_inputs_sha256':old,'synthetic_fixture_only':True}
putj(manifest_name,fixture_manifest)
aliases={n:{'original_sha256':old[n],'immutable_byte_copy':{'file':'reports/full-coverage/owner23-originals-before-owner24-integration-v1/'+Path(n).name,'sha256':old[n]}} for n in owners}
ref=lambda n:{'file':n,'sha256':H(FIX/n)}
auth={'actual_integration_execution':ref(execution_name),'integration_result':ref(result_name),'aliases':aliases}
fixtures=[]
core_offer=R(ROOT/offer_paths['core'])
core_source,core_row=next(iter(core_offer['proof_files'].items()))
for label,keep in [
 ('historical_absolute_without_snapshot_is_not_a_standalone_pair',lambda n,d: not n.endswith('.json') or ('original-tmp/root-barrier-intro-material24-trial2.json' in n)),
 ('canonical_standalone_without_named_is_not_a_pair',lambda n,d: not n.endswith('.json') or n.endswith('CompleteBarrierIntroMaterial24-standalone.json')),
 ('named_without_canonical_standalone_is_not_a_pair',lambda n,d: not n.endswith('.json') or n.endswith('CompleteBarrierIntroMaterial24-named-build.json'))]:
    evidence={n:d for n,d in core_row['evidence_sha256'].items() if keep(n,d)}
    try:selector.standalone_success(core_source,core_row['sha256'],evidence)
    except (AssertionError,KeyError,FileNotFoundError,ValueError):fixtures.append({'label':label,'expected':'reject','observed':'rejected'})
    else:raise AssertionError('Incomplete pair was accepted: '+label)
assert retainer.validate_owner_evidence_aliases(FIX,baseline_name,manifest_name,auth)==aliases
fixtures.append({'label':'exact_four_synthetic_authorizations_with_real_old_and_candidate_bytes','expected':'accept','observed':'accepted','synthetic_only':True})
def reject_auth(label,mutator):
    a=copy.deepcopy(auth);mutator(a)
    try:retainer.validate_owner_evidence_aliases(FIX,baseline_name,manifest_name,a)
    except (AssertionError,KeyError,FileNotFoundError,ValueError):fixtures.append({'label':label,'expected':'reject','observed':'rejected'})
    else:raise AssertionError('Invalid alias authorization accepted: '+label)
reject_auth('missing_one_owner',lambda a:a['aliases'].pop('book/coverage/core.json'))
reject_auth('unauthorized_fifth_owner_path',lambda a:a['aliases'].update({aux:copy.deepcopy(aliases['book/coverage/applied.json'])}))
reject_auth('old_hash_drift',lambda a:a['aliases']['book/coverage/core.json'].update(original_sha256='0'*64))
reject_auth('pruned_frozen_Applied_as_unpruned_original',lambda a:a['aliases']['book/coverage/applied.json'].update(original_sha256=frozen_applied))
reject_auth('archive_hash_drift',lambda a:a['aliases']['book/coverage/core.json']['immutable_byte_copy'].update(sha256='0'*64))
reject_auth('same_hash_wrong_archive_path',lambda a:a['aliases']['book/coverage/core.json']['immutable_byte_copy'].update(file='book/coverage/core.json'))
reject_auth('execution_pointer_drift',lambda a:a['actual_integration_execution'].update(sha256='0'*64))
reject_auth('result_pointer_drift',lambda a:a['integration_result'].update(sha256='0'*64))
def variant_record(label,kind,mutator):
    d=copy.deepcopy(execution if kind=='execution' else result);mutator(d)
    n='reports/full-coverage/synthetic-'+label+'.json';putj(n,d)
    reject_auth(label,lambda a:a.update({('actual_integration_execution' if kind=='execution' else 'integration_result'):ref(n)}))
variant_record('failed_execution','execution',lambda d:d.update(actual_exit_code=1))
variant_record('conflicting_exit_codes','execution',lambda d:d.update(exit_code=1))
variant_record('boolean_is_not_real_exit_code','execution',lambda d:d.update(actual_exit_code=False))
variant_record('missing_apply_command','execution',lambda d:d.update(command=['python3',helper,binding]))
variant_record('wrong_helper_command','execution',lambda d:d.update(command=['python3','book/coverage/checks/root_integrate_owner24_candidates_v1.py',binding,'--apply']))
variant_record('changed_workdir','execution',lambda d:d.update(actual_workdir=str(FIX/'other')))
variant_record('changed_helper_after','execution',lambda d:d['helper_sha256_after'].update({helper:'0'*64}))
variant_record('dry_run_result_is_not_applied','result',lambda d:d.update(applied=False))
variant_record('changed_old_before_hash','result',lambda d:d['exact_replacements'][0].update(before_sha256='0'*64))
variant_record('wrong_original_archive_field','result',lambda d:d['exact_replacements'][0].update(original23_byte_copy='reports/full-coverage/other.json'))
normalized,used=retainer.normalized_baseline_owner_evidence(fixture_row,aliases)
assert fixture_baseline['proof_files'][source]==fixture_row
selected_row=copy.deepcopy(fixture_row)
selected_row['evidence_sha256']={**normalized,**{n:candidate_refs[n]['sha256'] for n in owners}}
selected_row['checkpoint24_original_baseline_owner_evidence']={'original_baseline_selection':ref(baseline_name),'original_baseline_source':source,'original_row_body':copy.deepcopy(fixture_row),'authorized_original_path_aliases':used}
selected={source:copy.deepcopy(selected_row)}
retained=retainer.retain(FIX,baseline_name,manifest_name,selected,{},'book/coverage/checks/positive-synthetic-content-map.json',auth)
content=R(FIX/retained['file'])
assert {r['original_frozen_path']:r['sha256'] for r in content['input_bindings']}==frozen
assert selected[source]['checkpoint23_original_baseline_owner_evidence']==fixture_row['checkpoint23_original_baseline_owner_evidence']
assert selected[source]['checkpoint24_original_baseline_owner_evidence']['original_row_body']==fixture_row
applied_frozen_row=next(r for r in content['input_bindings'] if r['original_frozen_path']=='book/coverage/applied.json')
assert applied_frozen_row['sha256']==frozen_applied
assert applied_frozen_row['retained_input']!=aliases['book/coverage/applied.json']['immutable_byte_copy']['file']
fixtures.append({'label':'old_archive_current_candidate_and_distinct_frozen_Applied_coexist_with_original23_metadata','expected':'accept','observed':'accepted'})
negative_rows=[
 ('resurfaced_old_raw_hash',lambda r:r['evidence_sha256'].update({'book/coverage/core.json':old['book/coverage/core.json']})),
 ('arbitrary_current_raw_hash',lambda r:r['evidence_sha256'].update({'book/coverage/core.json':'0'*64})),
 ('frozen_pruned_Applied_as_current_raw',lambda r:r['evidence_sha256'].update({'book/coverage/applied.json':frozen_applied})),
 ('missing_archive_alias',lambda r:r['evidence_sha256'].pop(aliases['book/coverage/core.json']['immutable_byte_copy']['file'])),
 ('ordinary_evidence_drift',lambda r:r['evidence_sha256'].update({ordinary:'0'*64})),
 ('original_metadata_time_drift',lambda r:r.update(original_review_time='changed')),
 ('original_nested23_provenance_drift',lambda r:r['checkpoint23_original_baseline_owner_evidence'].update(original_baseline_source='changed')),
 ('original_entire24_row_body_drift',lambda r:r['checkpoint24_original_baseline_owner_evidence']['original_row_body'].update(original_review_time='changed')),
 ('proof_source_hash_drift',lambda r:r.update(sha256='0'*64)),
 ('wrong_alias_provenance',lambda r:r['checkpoint24_original_baseline_owner_evidence']['authorized_original_path_aliases']['book/coverage/core.json'].update(original_sha256='0'*64))]
for index,(label,mutator) in enumerate(negative_rows):
    row=copy.deepcopy(selected_row);mutator(row);out='book/coverage/checks/negative-'+str(index)+'.json'
    try:retainer.retain(FIX,baseline_name,manifest_name,{source:row},{},out,auth)
    except (AssertionError,KeyError,FileNotFoundError,ValueError):
        assert not (FIX/out).exists();fixtures.append({'label':label,'expected':'reject','observed':'rejected_before_output'})
    else:raise AssertionError('Invalid retention accepted: '+label)
for n,d in helpers.items():assert H(ROOT/n)==d
for n,d in ordinary_evidence.items():assert H(ROOT/n)==d,n
for n,d in real_offers.items():assert H(ROOT/n)==d
for n in owners:assert H(ROOT/n)==old[n]
assert not (ROOT/selector.DESTINATION).exists() and not (ROOT/selector.CONTENT_MAP).exists()
report={'status':'passed_independent_checkpoint24_selector_v3_retainer_v2_code_and_isolated_fixture_review_requires_genuine_source52_installation_plan_and_production_execution',
 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[],
 'request':{'file':REQ,'sha256':H(ROOT/REQ)},'original_failed_reader':{'actual_record':{'file':'/tmp/checkpoint24-selector-retainer-independent-applied-actual-v1.json','sha256':H('/tmp/checkpoint24-selector-retainer-independent-applied-actual-v1.json')},'entire_actual_body':failed_original,'checker':{'file':'/tmp/check-checkpoint24-selector-retainer-independent-applied-v1.py','sha256':H('/tmp/check-checkpoint24-selector-retainer-independent-applied-v1.py')},'root_cause':'The v2 selector aborted on a preserved absolute historical record without snapshot_hash before reaching the valid canonical pair. All original failures and true records are preserved; only selector eligibility changed.'},'helpers_sha256':helpers,'entire_reviewed_helper_bodies':bodies,
 'original_v1_and_actual_parent23_helpers':{**request['original_unexecuted_v1_helpers'],**{'parent_'+k:v for k,v in request['actual_parent23_helpers'].items()}},
 'baseline23':request['baseline23'],'all1131_real_baseline_sources_and_original_evidence_rehashed':True,
 'unique_original_baseline_evidence_count':len(ordinary_evidence),'real13_source_actual_paired_schema_reads':paired,'real_source51_reviewed_offer_sha256':real_offers,
 'fixtures':fixtures,'fixture_count':len(fixtures),'fixture_directory':str(FIX),
 'fixture_scope':'Synthetic code-only authorization and retention fixtures use real old/current reviewed-candidate/pruned frozen bytes. Their fabricated execution-schema records are explicitly synthetic and are never presented as actual tool results. The production validator has not been invoked against an actual owner24 installation because it has not occurred. No production prepare, source52 apply, owner24 install, aggregate or publication is claimed.',
 'original_unpruned_Applied23_sha256':old['book/coverage/applied.json'],'frozen_pruned_Applied23_sha256':frozen_applied,
 'required_future_real_checks':['actual_source52_apply0_and_postwrite0','actual_owner24_apply0_with_exact_archives','installed_source52_current_owner_interfaces_and_fresh_global0','immutable_independently_reviewed_production_plan','genuine_production_selector_output','fresh_frozen24_aggregate_and_publication'],
 'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),'coverage_complete':False,
 'scope':'Independent code and explicit isolated accept/reject tests only. All current owner assets, selected proofs, original review bodies/times, HTML/inventory and PUB bytes remain unchanged. No current52 or owner24 readiness is inferred.'}
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':str(OUT),'sha256':H(OUT),'fixtures':len(fixtures),'actual_production_executed':False}))
