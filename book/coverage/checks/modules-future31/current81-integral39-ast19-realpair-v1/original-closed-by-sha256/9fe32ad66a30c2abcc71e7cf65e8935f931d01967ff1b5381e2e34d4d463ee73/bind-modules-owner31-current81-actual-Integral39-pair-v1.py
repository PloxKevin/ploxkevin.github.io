"""Bind Root's genuine canonical pair into a new TMP candidate and raw30 inverse."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/modules-owner31-current81-integral39-ast19-actual-pair-v1')
PRE=Path('/tmp/modules-owner31-current81-integral39-ast19-provisional-v1')
CONTEXT=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
READY='book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
READY_SHA='c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
EXECUTION='reports/full-coverage/current81-canonical31-six-paired-application-execution-v1.json'
EXECUTION_SHA='5f65ff3afbdc659a667e2f4cf1f307d8975945dad709b70de2231b57d98fa80d'
CANONICAL='verification/lean/SafeLearning/CompleteModulesIntegralTrackingWhole31.lean'

def path(f):
    p=Path(f);return p if p.is_absolute() else ROOT/p
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(f):
    p=path(f);return {'file':str(f),'sha256':sha(p),'bytes':p.stat().st_size}
def load_ref(r):
    assert sha(path(r['file']))==r['sha256'],r['file']
    return json.loads(path(r['file']).read_bytes())

assert sha(CONTEXT)==CONTEXT_SHA and sha(path(READY))==READY_SHA and sha(path(EXECUTION))==EXECUTION_SHA
context=json.loads(CONTEXT.read_bytes());ready=json.loads(path(READY).read_bytes());execution=json.loads(path(EXECUTION).read_bytes())
assert not ready['errors'] and ready['source_count']==6 and ready['actual_compiler_command_count']==12
assert execution['status']=='passed' and execution['actual_exit_code']==0
assert ready['status']=='passed_actual_reviewed31_canonical_standalone_and_named_pairs_unselected'
base_offer=load_ref({'file':str(PRE/'modules31-current81-provisional-root-offer-v2.json'),'sha256':'054acc89810c7c43051928484c57df80a17d5ebad68b808dfc7f68a8275f77e2'})
base_request=load_ref(base_offer['request']);base=load_ref(base_offer['candidate'])
forward0=load_ref(base_offer['forward_patch']);inverse0=load_ref(base_offer['inverse_patch'])
original=load_ref(base_request['original_owner30'])
original_bytes=path(base_request['original_owner30']['file']).read_bytes()
pins={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256'],**ready['protected_inputs_sha256']}
for r in ready['sources']:
    pins[r['canonical_source']]=r['original_tmp_source']['sha256']
assert len(ready['sources'])==6
for r in ready['actual_paired_records']:
    assert r['actual_exit_code']==0
    for k in ['actual_record','raw_log','source_snapshot']:pins[r[k]['file']]=r[k]['sha256']
pins[READY]=READY_SHA;pins[EXECUTION]=EXECUTION_SHA
pins[execution['log']]=execution['log_sha256']
for r in [base_offer['candidate'],base_offer['forward_patch'],base_offer['inverse_patch'],base_offer['identity'],base_offer['request']]:pins[r['file']]=r['sha256']

def guard():
    assert sha(CONTEXT)==CONTEXT_SHA
    for f,h in pins.items():
        p=path(f)
        assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
        assert not p.is_symlink() and sha(p)==h,f

guard();assert not OUT.exists();OUT.mkdir()
source=next(r for r in ready['sources'] if r['canonical_source']==CANONICAL)
proof=base['proof_files'][CANONICAL]
assert proof['sha256']==source['original_tmp_source']['sha256']=='1a388e0109e6e8ff8bd9ce8c102420a7202f064eb7e46a76ff2cd4bcfefc10aa'
assert source['public_theorem_count']==39 and len(source['public_declarations'])==52
assert source['public_declarations']==proof['public_declarations']
assert [r['name'] for r in source['public_declarations'] if r['kind'] in ['theorem','lemma']]==proof['public_theorem_names']
pairs=[r for r in ready['actual_paired_records'] if r['source']['file']==CANONICAL]
assert len(pairs)==2 and {r['kind'] for r in pairs}=={'standalone','named'}
body_chains=[]
for p in pairs:
    body=load_ref(p['actual_record'])
    expected=['lake','env','lean','SafeLearning/CompleteModulesIntegralTrackingWhole31.lean'] if p['kind']=='standalone' else ['lake','build','SafeLearning.CompleteModulesIntegralTrackingWhole31']
    assert body['status']=='passed' and body['exit_code']==0 and body['source']==CANONICAL
    assert body['command']==expected and body['actual_workdir']==str(ROOT/'verification/lean')
    assert body['source_unchanged'] and body['source_sha256_before']==body['source_sha256_after']==proof['sha256']
    assert body['log']==p['raw_log']['file'] and body['log_sha256']==p['raw_log']['sha256']
    assert sha(path(p['source_snapshot']['file']))==proof['sha256']
    body_chains.append({'pair_kind':p['kind'],'entire_original_native_body_unchanged':body,'exact_root_pair_ref':p})
candidate=copy.deepcopy(base);forward=[];inverse=[]
def parent_obj(obj,pointer):
    t=[k.replace('~1','/').replace('~0','~') for k in pointer.split('/')[1:]]
    for k in t[:-1]:obj=obj[int(k)] if isinstance(obj,list) else obj[k]
    return obj,t[-1]
def replace(pointer,value):
    p,k=parent_obj(candidate,pointer)
    if isinstance(p,list):k=int(k)
    before=copy.deepcopy(p[k])
    if before==value:return
    forward.extend([{'op':'test','path':pointer,'value':before},{'op':'replace','path':pointer,'value':copy.deepcopy(value)}])
    inverse[0:0]=[{'op':'test','path':pointer,'value':copy.deepcopy(value)},{'op':'replace','path':pointer,'value':before}]
    p[k]=copy.deepcopy(value)
def add(pointer,value):
    p,k=parent_obj(candidate,pointer);assert isinstance(p,dict) and k not in p
    p[k]=copy.deepcopy(value);forward.append({'op':'add','path':pointer,'value':copy.deepcopy(value)})
    inverse[0:0]=[{'op':'test','path':pointer,'value':copy.deepcopy(value)},{'op':'remove','path':pointer}]

newproof=copy.deepcopy(proof)
newproof.update(selection_scope='direct_reviewed_reference_with_actual_canonical_standalone_and_named_pairs',standalone_compile_status='passed_source_matched_actual_canonical_pair',canonical_pair_pending=False,actual_pair_claimed=True)
newproof['actual_pair']=pairs
newproof['actual_pair_entire_native_command_cwd_log_snapshot_chains']=body_chains
newproof['actual_Root_complete12_readiness']=ref(READY)
newproof['actual_Root_complete12_execution']=ref(EXECUTION)
newproof['evidence_sha256']={r[k]['file']:r[k]['sha256'] for r in pairs for k in ['actual_record','raw_log','source_snapshot']}
newproof['evidence_sha256'].update({READY:READY_SHA,EXECUTION:EXECUTION_SHA,execution['log']:execution['log_sha256']})
replace('/proof_files/'+CANONICAL.replace('~','~0').replace('/','~1'),newproof)
target={'nn-in-the-loop.html::node-1240','nn-in-the-loop.html::node-1244','nn-in-the-loop.html::node-1247','nn-in-the-loop.html::node-1249'}
for a,r in enumerate(candidate['material_claims']):
    if set(r.get('source_unit_keys',[])).intersection(target):
        replace('/material_claims/'+str(a)+'/canonical_pair_pending',False)
        add('/material_claims/'+str(a)+'/actual_Integral39_canonical_pair',{'readiness':ref(READY),'execution':ref(EXECUTION),'pair_records':[r['actual_record'] for r in pairs]})
exkey='nn-in-the-loop.html::exercise-19';exindex=next(a for a,r in enumerate(candidate['exercises']) if r['inventory_key']==exkey)
replace('/exercises/'+str(exindex)+'/canonical_pair_pending',False)
for a,r in enumerate(candidate['exercises'][exindex]['claims']):replace('/exercises/'+str(exindex)+'/claims/'+str(a)+'/canonical_pair_pending',False)
add('/exercises/'+str(exindex)+'/actual_Integral39_canonical_pair',{'readiness':ref(READY),'execution':ref(EXECUTION),'pair_records':[r['actual_record'] for r in pairs]})
replace('/status','prepared_Source81_Modules_owner31_Integral39_actual_canonical_pair_and19_NF_pending_final_independent_mapping_and_Root_installation')
binding={'status':'actual39_theorems52_public_names_two_canonical_commands_bound_exact_current81_mapping_pending_Root_owner_installation','bound_at_utc':datetime.now(timezone.utc).isoformat(),'original_provisional_candidate':base_offer['candidate'],'original_provisional_root_offer':ref(str(PRE/'modules31-current81-provisional-root-offer-v2.json')),'actual_complete12_readiness':ref(READY),'actual_complete12_execution':ref(EXECUTION),'own_source_count':1,'own_theorem_count':39,'own_public_name_count':52,'own_actual_command_count':2,'own_actual_pairs':pairs,'full_own_native_command_cwd_log_snapshot_chains':body_chains,'new6_canonical_sources_guarded':{r['canonical_source']:r['original_tmp_source']['sha256'] for r in ready['sources']},'source81_aggregate_verification_claimed':False,'owner_installation_and_aggregate_selection_pending':True,'coverage_complete':False}
add('/actual_current81_pair_binding31',binding)
validation=copy.deepcopy(candidate['current_identity_binding_validation']);validation['status']='exact_Source81_owned_identity_and_actual_Integral39_pairs_bound_independent_mapping_and_owner_installation_pending';validation['actual_canonical_pair']=ref(READY)
replace('/current_identity_binding_validation',validation)
integration=copy.deepcopy(candidate['reviewed_work_integration31_current81_provisional_candidate']);integration['status']='prepared_one_whole_Integral_exercise_four_whole_literals19_NF_leaves_actual39_pair_bound_pending_final_independent_mapping';integration['canonical_pair_pending']=False;integration['actual_Root_complete12_readiness']=ref(READY);integration['actual_Root_complete12_execution']=ref(EXECUTION)
replace('/reviewed_work_integration31_current81_provisional_candidate',integration)

def apply_patch(obj,operations):
    obj=copy.deepcopy(obj)
    for op in operations:
        p,k=parent_obj(obj,op['path'])
        if isinstance(p,list) and k!='-':k=int(k)
        if op['op']=='test':assert p[k]==op['value'],op['path']
        elif op['op']=='replace':p[k]=copy.deepcopy(op['value'])
        elif op['op']=='remove':
            if isinstance(p,list):p.pop(k)
            else:del p[k]
        elif op['op']=='add':
            if isinstance(p,list):assert k=='-';p.append(copy.deepcopy(op['value']))
            else:assert k not in p;p[k]=copy.deepcopy(op['value'])
        else:raise AssertionError(op['op'])
    return obj

full_forward=forward0['operations']+forward;full_inverse=inverse+inverse0['operations']
assert apply_patch(original,full_forward)==candidate
restored=apply_patch(candidate,full_inverse);assert restored==original
serialization=inverse0['original_serialization'];restored_bytes=(json.dumps(restored,ensure_ascii=serialization['ensure_ascii'],indent=serialization['indent'])+'\n').encode()
assert restored_bytes==original_bytes and hashlib.sha256(restored_bytes).hexdigest()=='6f347b3d512a5ce36222e72e8236eb350f3218ace430c3a9dabd8776a03fbc34'
assert candidate['declarations'][:3988]==original['declarations'] and len(candidate['declarations'])==4027
assert {f:candidate['proof_files'][f] for f in original['proof_files']}==original['proof_files']
assert len(candidate['proof_files'])==518 and candidate['counts']==base['counts']
assert all('ShiftedTemporalIQC31' not in str(r) for r in candidate['declarations'][-39:])
for k in ['nn-in-the-loop.html::exercise-20','viability.html::exercise-19','verification.html::exercise-19']:
    assert next(r for r in candidate['exercises'] if r['inventory_key']==k)['status']=='partial'

def write(name,value):
    p=OUT/name
    with p.open('x',encoding='utf-8') as f:json.dump(value,f,ensure_ascii=False,indent=2);f.write('\n')
    return ref(str(p))
candidate_ref=write('modules31-current81-Integral39-actual-pair-AST19-candidate-v1.json',candidate)
forward_ref=write('modules31-current81-actual-pair-full-typed-forward-JSONpatch-v1.json',{'format':'RFC6902_JSON_Patch_operations_with_explicit_typed_test_values','original_owner30':base_request['original_owner30'],'candidate':candidate_ref,'operations':full_forward})
inverse_ref=write('modules31-current81-actual-pair-full-typed-inverse-JSONpatch-v1.json',{'format':'RFC6902_JSON_Patch_operations_with_explicit_typed_test_values','candidate':candidate_ref,'restores_original_owner30':base_request['original_owner30'],'original_serialization':serialization,'inverse_reconstruction_original_bytes_sha256':hashlib.sha256(restored_bytes).hexdigest(),'operations':full_inverse})
overlay_ref=write('modules31-provisional-to-actual-pair-typed-overlay-and-inverse-v1.json',{'original_provisional_candidate':base_offer['candidate'],'actual_pair_bound_candidate':candidate_ref,'forward_operations':forward,'inverse_operations':inverse,'all_existing_semantic_correspondences_counts_and_declaration_names_unchanged':True})
association=load_ref(base_request['explicit_associations']);association['proof_metadata']=newproof;association['actual_pair_binding']=binding
association['Integral_material_rows']=[r for r in candidate['material_claims'] if set(r.get('source_unit_keys',[])).intersection(target)]
association['entire_Integral_exercise']=candidate['exercises'][exindex]
association_ref=write('modules31-current81-actual-pair-full-explicit-Integral39-and-AST19-row-associations-v1.json',association)
guard()
request=copy.deepcopy(base_request);request.update(status='prepared_final_Modules_owner31_Source81_actual39_pair_bound_full_mapping_request_author_binding_native_pending',candidate=candidate_ref,forward_patch=forward_ref,inverse_patch=inverse_ref,explicit_associations=association_ref,canonical_pair_pending=False)
request['original_provisional_request']=base_offer['request'];request['original_provisional_candidate']=base_offer['candidate'];request['actual_pair_overlay']=overlay_ref;request['actual_current81_pair_binding31']=binding
request['review_scope']='Independently read all exact19 NF leaves, four full Integral literals and all five original Exercise19 requirements with the exact39 theorem input predicates/scope/primary associations. Check actual standalone+named command/cwd/source/native/log/snapshot chains,52public/39theorem names,4977unit/217exercise identity,full forward/inverse rawowner30 byte reconstruction, all old517proofs/3988declprefix and111wholeFalse flags. No IQC future source is included. Owner installation, aggregate selection and publication remain pending.'
request['required_evidence_artifacts_sha256']={READY:READY_SHA,EXECUTION:EXECUTION_SHA,execution['log']:execution['log_sha256'],CANONICAL:newproof['sha256'],**newproof['evidence_sha256']}
request['actual_canonical_source_pair_claimed']=True;request['owner_installation_or_aggregate_selection_claimed']=False
request_ref=write('modules31-current81-actual-pair-independent-final-mapping-review-request-v1.json',request)
offer_ref=write('modules31-current81-actual-pair-root-offer-v1.json',{'status':'prepared_actual39_canonical_pair_bound_owner31_pending_author_binding_native_final_mapping_and_Root_installation','candidate':candidate_ref,'original_owner30':base_request['original_owner30'],'forward_patch':forward_ref,'inverse_patch':inverse_ref,'identity':base_offer['identity'],'request':request_ref,'original_provisional_offer':ref(str(PRE/'modules31-current81-provisional-root-offer-v2.json')),'new_source':ref(CANONICAL),'actual_pair_binding':binding,'new_theorem_count':39,'public_name_count':52,'counts':candidate['counts'],'canonical_pair_pending':False,'current_owner_selection_or_publication_written':False,'coverage_complete':False})
print(json.dumps({'status':'passed_isolated_actual_pair_binding','candidate':candidate_ref,'inverse':inverse_ref,'request':request_ref,'offer':offer_ref,'full_forward_operations':len(full_forward),'full_inverse_operations':len(full_inverse),'guarded_unique_files':len(pins),'new_canonical_sources_guarded':6,'own_actual_command_count':2,'counts':candidate['counts']}))
