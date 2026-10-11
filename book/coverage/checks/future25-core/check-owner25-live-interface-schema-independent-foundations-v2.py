"""Actual read-only code tests; every simulated integration stays in memory."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, copy, runpy, ast
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future25-core'
HELPER=ROOT/'book/coverage/prepare_checkpoint25_live_owner_interfaces_v3.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)), 'sha256':H(p)}
assert H(HELPER)=='e68cdcd77e09f025ae8cec86d55e3432d1fd7a3a503f184dd0f9f9d0ec6eaef2'
ast.parse(HELPER.read_text())
support=BASE/'owner25-live-interface-in-memory-fixture-support-v2.py'
f=runpy.run_path(str(support),run_name='explicit_in_memory_fixture')
ns=f['ns'];store=f['store'];base=dict(store);outputs=f['outputs'];put=f['put'];read=f['read'];digest=f['digest'];fx=f['fx'];req0=copy.deepcopy(f['req'])
cases=[]
def reset():
    store.clear();store.update(base);outputs.clear()
    return copy.deepcopy(req0)
def run(name,body,reject=False):
    request=reset()
    try:body(request)
    except (AssertionError,KeyError,TypeError,ValueError):
        assert reject,name
        cases.append({'fixture':name,'expected':'reject','observed':'rejected'})
    else:
        assert not reject,name
        cases.append({'fixture':name,'expected':'accept','observed':'accepted'})
def execute_mutation(request,edit):
    value=read(request['actual_integration_execution']['file']);edit(value)
    request['actual_integration_execution']=put(request['actual_integration_execution']['file'],value)
    return ns['integration'](request)
def normalize_all(request):
    out=ns['interfaces'](f['reqref']['file'])
    manifest=read(out['interface_manifest'])
    assert set(manifest['owners'])==ns['OWNERS'] and len(outputs)==5
    for owner,row in manifest['owners'].items():
        original=read(row['original_candidate_offer']['file']);live=read(row['live_offer']['file'])
        reverse=copy.deepcopy(live)
        for k in row['appended_live_interface_fields']:reverse.pop(k)
        for k in row['changed_original_fields']:reverse[k]=copy.deepcopy(original[k])
        assert reverse==original and row['original_body_reversible_exact']
        if owner=='core':assert live['candidate_ledger']==original['candidate_ledger'] and live['mapped_ledger']=='book/coverage/core.json'
        if owner=='modules':
            assert live['mapped_ledger']==live['module_ledger']=='book/coverage/modules.json'
            assert live['mapped_ledger_sha256']==live['module_ledger_sha256']==digest('book/coverage/modules.json')
        if owner=='applied'and 'required_live_integration_evidence_sha256'in original:
            for n,h in original['required_live_integration_evidence_sha256'].items():assert live['required_live_integration_evidence_sha256'][n]==h
            assert 'required_live_integration_evidence_sha256' in row['changed_original_fields']
    return out
def plan_fixture(request,global_edit=lambda x:None,peer_edit=lambda x:None):
    out=normalize_all(request);mi={'file':out['interface_manifest'],'sha256':out['sha256']}
    peer={'status':'synthetic_fixture_passed','errors':[],'live_interface_manifest':mi};peer_edit(peer);pr=put(fx+'synthetic-output-peer.json',peer)
    global_data={'integrity_status':'passed','errors':[],'inventory_sha256':ns['INVENTORY_SHA'],'domains':[{'domain':o,'ledger_sha256':digest('book/coverage/'+o+'.json')}for o in f['paths']]};global_edit(global_data);gr=put(fx+'synthetic-global.json',global_data)
    out=ns['plan'](f['reqref']['file'],mi,pr,gr);plan=read(out['selection_plan'])
    assert out['new_proof_sources']==12 and len(plan['owners'])==4
    aliases=plan['authorized_baseline_owner_evidence_aliases']['aliases']
    assert set(aliases)=={'book/coverage/'+o+'.json'for o in f['paths']}
    for n,row in aliases.items():assert row['original_sha256']==f['manifest']['working_inputs_sha256'][n]==digest(row['immutable_byte_copy']['file'])
    assert plan['actual_source52_apply']==request['actual_source52_apply'] and plan['actual_source52_postwrite']==request['actual_source52_postwrite']
    assert plan['helpers_sha256'][str(HELPER.relative_to(ROOT))]==H(HELPER)
    assert plan['content_map']=='book/coverage/checks/frozen24-input-content-bindings25-v1.json'
    return plan
run('four_real_owner_offer_shapes_normalize_and_reverse_entire_original',normalize_all)
run('production_plan_schema_twelve_new_sources_four_old_working_aliases_source52_refs',plan_fixture)
run('actual_command_only_and_raw_log_sha256_only_accepted',lambda r:execute_mutation(r,lambda e:(e.update(actual_command=e.pop('command'),raw_log_sha256=e.pop('log_sha256')))))
run('matching_command_exit_and_all_three_log_aliases_accepted',lambda r:execute_mutation(r,lambda e:e.update(actual_command=e['command'],exit_code=0,original_log_sha256=e['log_sha256'],raw_log_sha256=e['log_sha256'])))
run('conflicting_command_alias_rejected',lambda r:execute_mutation(r,lambda e:e.update(actual_command=['python3','wrong','wrong','--apply'])),True)
run('missing_both_commands_rejected',lambda r:execute_mutation(r,lambda e:e.pop('command')),True)
run('dry_command_rejected',lambda r:execute_mutation(r,lambda e:e['command'].__setitem__(3,'--dry-run')),True)
run('failed_exit_rejected',lambda r:execute_mutation(r,lambda e:e.update(actual_exit_code=1)),True)
run('boolean_exit_rejected',lambda r:execute_mutation(r,lambda e:e.update(actual_exit_code=False)),True)
run('conflicting_exit_alias_rejected',lambda r:execute_mutation(r,lambda e:e.update(exit_code=1)),True)
run('wrong_cwd_rejected',lambda r:execute_mutation(r,lambda e:e.update(actual_workdir='/tmp')),True)
run('changed_helper_after_rejected',lambda r:execute_mutation(r,lambda e:e.update(helper_sha256_after='0'*64)),True)
run('wrong_helper_before_and_after_rejected',lambda r:execute_mutation(r,lambda e:e.update(helper_sha256_before='0'*64,helper_sha256_after='0'*64)),True)
run('conflicting_original_log_alias_rejected',lambda r:execute_mutation(r,lambda e:e.update(original_log_sha256='0'*64)),True)
run('conflicting_raw_log_alias_rejected',lambda r:execute_mutation(r,lambda e:e.update(raw_log_sha256='0'*64)),True)
run('missing_all_log_digests_rejected',lambda r:execute_mutation(r,lambda e:e.pop('log_sha256')),True)
run('wrong_log_digest_rejected',lambda r:execute_mutation(r,lambda e:e.update(log_sha256='0'*64)),True)
run('wrong_inventory_authorization_rejected',lambda r:(r.update(inventory={'file':ns['INVENTORY'],'sha256':'0'*64}),ns['integration'](r)),True)
def edit_result(request,edit):
    result=read(request['integration_result']['file']);edit(result);request['integration_result']=put(request['integration_result']['file'],result);return ns['integration'](request)
run('unapplied_result_rejected',lambda r:edit_result(r,lambda x:x.update(applied=False)),True)
run('wrong_original24_archive_digest_rejected',lambda r:edit_result(r,lambda x:x['exact_replacements'][0].update(before_sha256='0'*64)),True)
run('wrong_current_candidate_digest_rejected',lambda r:edit_result(r,lambda x:x['exact_replacements'][0]['candidate'].update(sha256='0'*64)),True)
def offer_fixture(owner,edit):
    request=reset();binding=read(request['integration_binding']['file']);row=binding['owners'][owner];old=read(row['reviewed_final_offer']['file']);edit(old)
    row['reviewed_final_offer']=put(fx+'modified-original-'+owner+'.json',old)
    bref=put(request['integration_binding']['file'],binding);request['integration_binding']=bref
    result=read(request['integration_result']['file']);result['binding_manifest_sha256']=bref['sha256'];request['integration_result']=put(request['integration_result']['file'],result)
    put(f['reqref']['file'],request);return ns['interfaces'](f['reqref']['file'])
run('Module_unique_list_imports_normalize_reversibly',lambda r:offer_fixture('modules',lambda o:o.update(required_external_import_dependencies=list(o['required_external_import_dependencies']))))
run('Module_duplicate_import_list_rejected',lambda r:offer_fixture('modules',lambda o:o.update(required_external_import_dependencies=list(o['required_external_import_dependencies'])*2)),True)
run('Module_wrong_import_digest_rejected',lambda r:offer_fixture('modules',lambda o:o['required_external_import_dependencies'].update({next(iter(o['required_external_import_dependencies'])):'0'*64})),True)
run('Module_secondary_mapped_ledger_conflict_rejected',lambda r:offer_fixture('modules',lambda o:o.update(mapped_ledger='wrong')),True)
run('Core_preexisting_mapped_ledger_collision_rejected',lambda r:offer_fixture('core',lambda o:o.update(mapped_ledger='wrong')),True)
existing_name='book/coverage/checks/root_integrate_owner25_candidates_v2.py'
run('Applied_optional_existing_evidence_merge_is_reversible',lambda r:offer_fixture('applied',lambda o:o.update(required_live_integration_evidence_sha256={existing_name:H(ROOT/existing_name)})))
run('Applied_stale_preserved_evidence_hash_rejected',lambda r:offer_fixture('applied',lambda o:o.update(required_live_integration_evidence_sha256={existing_name:'0'*64})),True)
run('global_audit_failure_rejected',lambda r:plan_fixture(r,lambda x:x.update(integrity_status='failed')),True)
run('global_domain_ledger_mismatch_rejected',lambda r:plan_fixture(r,lambda x:x['domains'][0].update(ledger_sha256='0'*64)),True)
run('independent_output_peer_errors_rejected',lambda r:plan_fixture(r,peer_edit=lambda x:x.update(errors=['synthetic error'])),True)
run('independent_output_peer_wrong_manifest_rejected',lambda r:plan_fixture(r,peer_edit=lambda x:x['live_interface_manifest'].update(sha256='0'*64)),True)
for field in ('authorized_current_future_code_updates','current_future_code_update_authorization','authorized_current_future_code_update_reference_sha256'):
    run('exact_'+field+'_mismatch_rejected',lambda r,field=field:edit_result(r,lambda d:d.update({field:{}})),True)
def auth_merge_exact(r):
    out=normalize_all(r)
    for owner,row in read(out['interface_manifest'])['owners'].items():
        live=read(row['live_offer']['file'])
        for n,h in f['auth_fields']['authorized_current_future_code_update_reference_sha256'].items():assert live['required_live_integration_evidence_sha256'][n]==h
run('all17_real_singleton_authorization_originals_retained_in_each_reversible_live_offer',auth_merge_exact)
def mutually_stale_auth(r):
    b=read(r['integration_binding']['file']);b['authorized_current_future_code_update_reference_sha256'][next(iter(b['authorized_current_future_code_update_reference_sha256']))]='0'*64
    br=put(r['integration_binding']['file'],b);r['integration_binding']=br
    res=read(r['integration_result']['file']);res['binding_manifest_sha256']=br['sha256'];res['authorized_current_future_code_update_reference_sha256']=b['authorized_current_future_code_update_reference_sha256'];r['integration_result']=put(r['integration_result']['file'],res)
    put(f['reqref']['file'],r);return ns['interfaces'](f['reqref']['file'])
run('mutually_matching_but_stale_original_provenance_digest_rejected',mutually_stale_auth,True)
# Directly exercise the exact merge block, including an otherwise unreachable
# internally inconsistent hash fixture, rather than invent a real execution.
tree=ast.parse(HELPER.read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='interfaces')
loop=next(n for n in fn.body if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and [x.id for x in n.target.elts]==['owner','entry'])
block=next(n for n in loop.body if isinstance(n,ast.If) and ast.unparse(n.test)=="'required_live_integration_evidence_sha256' in original")
code=compile(ast.Module(body=[block],type_ignores=[]),str(HELPER),'exec')
def merge_conflict(request):
    local={'original':{'required_live_integration_evidence_sha256':{'fixture-path':'old'}},'integration_evidence':{'fixture-path':'different'},'additions':{'required_live_integration_evidence_sha256':{}},'out':{},'changed_fields':[],'sha':lambda n:'old'}
    exec(code,local)
run('exact_merge_block_conflicting_existing_hash_rejected',merge_conflict,True)
reset()
selection=J(ROOT/ns['BASELINE']);assert H(ROOT/ns['BASELINE'])==ns['BASELINE_SHA']and len(selection['proof_files'])==1144
for n,row in selection['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-24'/n)==row['sha256']
held={n:f['manifest']['working_inputs_sha256'][n]for n in ['book/coverage/'+x+'.json'for x in ['core','foundations','applied','modules','applied-promotions']]}
for n,h in held.items():assert H(ROOT/n)==h
inputs={n:H(ROOT/n)for n in f['paths'].values()}
assert not any((ROOT/n).exists()for n in outputs)and not(ROOT/fx).exists()
oldhelper=ROOT/'book/coverage/prepare_checkpoint25_live_owner_interfaces_v2.py'
assert H(oldhelper)=='268d5f3b5936f968581e802473895c41e8d0699e5d33ddc109f426f040d02401'
# Restore exactly the three added authorization equality checks, provenance merge
# loop and two versioned constants; all earlier original helper code is identical.
new_tree=ast.parse(HELPER.read_text());old_tree=ast.parse(oldhelper.read_text())
for node in new_tree.body:
    if isinstance(node,ast.Assign)and ast.unparse(node.targets[0])in {'SELECTOR','RETAINER'}:
        node.value.value=node.value.value.replace('_v3.py','_v2.py')
    if isinstance(node,ast.FunctionDef)and node.name=='integration':
        node.body=[x for x in node.body if not(isinstance(x,ast.Assert)and any(k in ast.unparse(x.test)for k in ('authorized_current_future_code_updates','current_future_code_update_authorization','authorized_current_future_code_update_reference_sha256')))]
    if isinstance(node,ast.FunctionDef)and node.name=='interfaces':
        node.body=[x for x in node.body if not(isinstance(x,ast.For)and 'authorized_current_future_code_update_reference_sha256' in ast.unparse(x.iter))]
assert ast.dump(new_tree)==ast.dump(old_tree)
old_code_peer=ROOT/'book/coverage/checks/future25-core/owner25-live-interface-helper-independent-foundations-final-code-review-v1.json'
assert H(old_code_peer)=='ad3c9d68961c7455532e3505f549b872ec19d9401c2490f452cebb4658ec4df8'
old_code_body=J(old_code_peer)
prior_peer=ROOT/'book/coverage/checks/future24-core/owner24-live-interface-helper-independent-foundations-code-review-v1.json';prior_body=J(prior_peer)
assert H(prior_peer)=='813a8c1bbb8f4e0fc0b3087317ed451bddfb18d25b14ef136946c43d1ffeb6b2'
report={'status':'independent_owner25_live_interface_helper_code_and_schema_fixtures_passed','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','helper':ref(HELPER),'helper_sha256':H(HELPER),'original_unexecuted_v1_helper':ref(oldhelper),'original24_code_peer':ref(prior_peer),'entire_original24_peer_body_and_time':prior_body,'entire_original_interface_v2_code_review_body_and_time':old_code_body,'v2_to_v3_delta_only_exact_authorization_equalities_provenance_merge_and_two_constants':True,'checker':ref(Path(__file__)),'fixture_support':ref(support),'fixture_count':len(cases),'fixture_results':cases,'real_current52_original_offer_sha256':inputs,'all1144_real_baseline_sources_and_frozen_copies_exact':True,'held24_five_live_owner_sha256':held,'full_read_code_scope':['all integration authorization and command/exit/log alias guards','all four entire-offer reversible normalization paths','Core complete inventory source-map with owned subset','Module import list/dictionary normalization','Applied promotions and exact existing-evidence merge','plan actual integration and fresh independent interface/global preconditions','four original24 working-ledger aliases, source52 records and baseline24 fields','exclusive new writes and twelve-new-source disjoint union'],'scope':'Code/schema approval only. Fixtures invoke the actual helper functions using real candidate/offer bytes and explicitly synthetic in-memory binding/execution/result/peer/global objects. No synthetic record is written or represented as genuine execution. No live ledger, original offer, source HTML, inventory, production interface, plan, selection, Lean compile or publication was changed. Final actual integration and independent output review remain required.'}
out=BASE/'owner25-live-interface-helper-independent-foundations-code-review-v2.json'
with out.open('x')as file:file.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':ref(out),'fixture_count':len(cases)}))
