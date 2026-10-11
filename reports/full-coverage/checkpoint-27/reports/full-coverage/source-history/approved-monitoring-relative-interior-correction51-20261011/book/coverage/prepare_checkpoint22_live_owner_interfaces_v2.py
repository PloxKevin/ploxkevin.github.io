"""Retain candidate offers and bind a genuine reviewed four-owner copy execution.

The interfaces stage runs only after Root's actual --apply integration succeeded.
The plan stage additionally requires an independent interface peer and a fresh
global ledger pass. Neither stage compiles Lean or rewrites an original offer.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, json

ROOT=Path(__file__).resolve().parents[2]
INVENTORY='book/coverage/inventory-after-correction48.json'
INVENTORY_SHA='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
BASELINE='reports/full-coverage/checkpoint-21-selection.json'
BASELINE_SHA='bf73119b16a9fbaf22e29ae9b673f940af29b5dc3950aabbf7032ad299b7334f'
MANIFEST='reports/full-coverage/checkpoint-21-manifest.json'
AUDIT='reports/full-coverage/lean-checkpoint-21/verification-original.json'
SELECTOR='book/coverage/prepare_checkpoint22_selection.py'
RETAINER='book/coverage/retain_baseline_inputs22.py'
OWNERS={'core','modules','foundations','applied'}
KIND='actual_guarded_candidate_integration_copy'
SCOPE='Actual Root --apply copies exact independently reviewed candidate bytes to the live ledgers. It is an integration execution, not a Lean compilation, mathematical rereview or aggregate22 audit.'

def safe(name):
    assert isinstance(name,str) and name
    path=Path(name)
    assert not path.is_absolute() and '..' not in path.parts and str(path)==name
    assert (ROOT/path).resolve().is_relative_to(ROOT.resolve())
    return ROOT/path
def sha(name):return hashlib.sha256(safe(name).read_bytes()).hexdigest()
def read(name):return json.loads(safe(name).read_text())
def checked(ref):
    assert set(ref)=={'file','sha256'} and sha(ref['file'])==ref['sha256']
    return read(ref['file'])
def pointer(data,keys):
    for key in keys:data=data[key]
    return data
def write_new(name,data):
    path=safe(name);assert path.parent.is_dir()
    with path.open('x') as out:out.write(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def passed_peer(ref):
    peer=checked(ref)
    assert ('passed' in peer['status'] or 'confirmed' in peer['status']) and peer.get('errors',[])==[]
    return peer

def integration(request):
    assert request['status']=='root_authorized_postintegration_owner22_interface_preparation'
    assert request['inventory']=={'file':INVENTORY,'sha256':INVENTORY_SHA}
    assert sha(INVENTORY)==sha('book/coverage/inventory.json')==INVENTORY_SHA
    helper_ref=request['live_interface_helper']
    assert helper_ref=={'file':str(Path(__file__).relative_to(ROOT)),'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    binding=checked(request['integration_binding'])
    assert binding['status']=='all_four_reviewed_current48_owner_candidates_bound_ready_for_root_execution'
    assert set(binding['owners'])==OWNERS
    execution=checked(request['actual_integration_execution'])
    codes=[execution[k] for k in ('actual_exit_code','exit_code') if k in execution]
    assert codes and all(type(x) is int and x==0 for x in codes)
    helper=binding['helper'];assert sha(helper['file'])==helper['sha256']
    command=execution.get('command',execution.get('actual_command'))
    assert len(command)==4 and command[0] in {'python','python3'}
    assert command[1] in {helper['file'],str(safe(helper['file']))}
    assert command[2] in {request['integration_binding']['file'],str(safe(request['integration_binding']['file']))} and command[3]=='--apply'
    assert Path(execution['actual_workdir']).resolve()==ROOT.resolve()
    before=execution['helper_sha256_before'];after=execution['helper_sha256_after'];assert before==after
    if isinstance(after,dict):
        assert after.get(helper['file'],after.get(Path(helper['file']).name))==helper['sha256']
        for name,digest in after.items():assert sha(name if '/' in name else 'book/coverage/checks/'+name)==digest
    else:assert after==helper['sha256']
    log=request['actual_integration_raw_log'];assert sha(log['file'])==log['sha256']==execution.get('log_sha256',execution.get('original_log_sha256'))
    result=checked(request['integration_result'])
    assert result['status']=='four_exact_reviewed_owner22_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate22_audit'
    assert result['applied'] is True and result['actual_helper']==helper['file'] and result['actual_helper_sha256']==helper['sha256']
    assert result['binding_manifest']==request['integration_binding']['file'] and result['binding_manifest_sha256']==request['integration_binding']['sha256']
    assert result['inventory_sha256']==INVENTORY_SHA and result['all32040_frozen21_inputs_exact'] and result['all1089_selected21_root_source_hashes_exact']
    rows={x['destination']:x for x in result['exact_replacements']}
    assert set(rows)=={'book/coverage/'+owner+'.json' for owner in OWNERS}|{'book/coverage/applied-promotions.json'}
    for owner,entry in binding['owners'].items():
        ledger='book/coverage/'+owner+'.json';row=rows[ledger]
        assert row['candidate']==entry['candidate_ledger'] and row['before_sha256']==entry['held21_ledger_sha256']
        assert sha(ledger)==sha(row['candidate']['file'])==row['candidate']['sha256']
        assert sha(row['original21_byte_copy'])==row['before_sha256']
        passed_peer({'file':entry['independent_candidate_mapping_peer']['file'],'sha256':entry['independent_candidate_mapping_peer']['sha256']})
    return binding,result

def interfaces(request_name):
    request=read(request_name);binding,result=integration(request)
    assert set(request['live_offer_destinations'])==OWNERS
    destinations=list(request['live_offer_destinations'].values())+[request['interface_manifest_destination']]
    assert len(set(destinations))==5 and all(not safe(n).exists() for n in destinations)
    integration_evidence={ref['file']:ref['sha256'] for ref in [request['actual_integration_execution'],request['actual_integration_raw_log'],request['integration_result'],request['integration_binding']]}
    for row in result['exact_replacements']:integration_evidence[row['original21_byte_copy']]=row['before_sha256']
    for name,digest in request.get('historical_dry_run_evidence_sha256',{}).items():
        assert sha(name)==digest;integration_evidence[name]=digest
    for name,digest in integration_evidence.items():assert sha(name)==digest
    records={};new_offers={}
    for owner,entry in binding['owners'].items():
        ref=entry['reviewed_final_offer'];original=checked({'file':ref['file'],'sha256':ref['sha256']});out=copy.deepcopy(original)
        path_keys=entry['offer_candidate_path_pointer'];hash_keys=entry['offer_candidate_sha256_pointer']
        assert len(path_keys)==len(hash_keys)==1
        assert path_keys[0] in {'mapped_ledger','module_ledger'} and hash_keys[0]==path_keys[0]+'_sha256'
        assert pointer(original,path_keys)==entry['candidate_ledger']['file'] and pointer(original,hash_keys)==entry['candidate_ledger']['sha256']
        ledger='book/coverage/'+owner+'.json';out[path_keys[0]]=ledger;out[hash_keys[0]]=sha(ledger)
        changed_fields=[path_keys[0],hash_keys[0]]
        if owner=='applied':
            companion=entry['companion_candidates'];assert len(companion)==1
            assert original['mapped_promotions']==companion[0]['candidate']['file'] and original['mapped_promotions_sha256']==companion[0]['candidate']['sha256']
            out['mapped_promotions']=companion[0]['held21_asset'];out['mapped_promotions_sha256']=sha(out['mapped_promotions'])
            assert out['mapped_promotions_sha256']==original['mapped_promotions_sha256']
            changed_fields+=['mapped_promotions','mapped_promotions_sha256']
        additions={
            'live_interface_status':'current48_exact_reviewed_candidate_copy_pending_global_integrity_and_fresh22_audit',
            'live_interface_prepared_at_utc':datetime.now(timezone.utc).isoformat(),
            'original_isolated_candidate_offer':{'file':ref['file'],'sha256':ref['sha256']},
            'actual_guarded_live_integration':{'execution_kind':KIND,'actual_execution':request['actual_integration_execution'],'raw_log':request['actual_integration_raw_log'],'actual_helper':binding['helper'],'binding_manifest':request['integration_binding'],'integration_result':request['integration_result'],'scope':SCOPE},
            'original_candidate_mapping_peer':{'file':entry['independent_candidate_mapping_peer']['file'],'sha256':entry['independent_candidate_mapping_peer']['sha256']},
            'original_candidate_math_review_body_times_and_execution_history_retained':True,
            'required_live_integration_evidence_sha256':integration_evidence}
        assert not (set(additions)&set(original));out.update(additions)
        reverse=copy.deepcopy(out)
        for key in additions:reverse.pop(key)
        for key in changed_fields:reverse[key]=original[key]
        assert reverse==original
        assert out['source_sha256']==read(ledger)['source_sha256']
        new_offers[owner]=out
        records[owner]={'original_candidate_offer':{'file':ref['file'],'sha256':ref['sha256']},'live_ledger':{'file':ledger,'sha256':sha(ledger)},'candidate_ledger':entry['candidate_ledger'],'candidate_mapping_peer':out['original_candidate_mapping_peer'],'changed_original_fields':changed_fields,'appended_live_interface_fields':list(additions),'original_body_reversible_exact':True,'expected_owned_proof_sources':sorted(original['proof_files'])}
    for owner,out in new_offers.items():
        name=request['live_offer_destinations'][owner];write_new(name,out);records[owner]['live_offer']={'file':name,'sha256':sha(name)}
    manifest={'status':'actual_copy_only_owner22_live_interfaces_prepared_for_independent_mechanical_review','created_at_utc':datetime.now(timezone.utc).isoformat(),'preparation_request':{'file':request_name,'sha256':sha(request_name)},'preparation_helper':{'file':str(Path(__file__).relative_to(ROOT)),'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},'inventory':request['inventory'],'actual_guarded_live_integration':new_offers['modules']['actual_guarded_live_integration'],'owners':records,'original_math_body_review_times_and_actual_candidate_builds_retained':True,'requires_independent_live_interface_peer_before_selection_plan':True,'execution_kind':KIND,'scope':SCOPE,'errors':[]}
    name=request['interface_manifest_destination'];write_new(name,manifest)
    return {'interface_manifest':name,'sha256':sha(name),'owners':records}

def plan(request_name,manifest_ref,peer_ref,global_ref):
    request=read(request_name);binding,result=integration(request)
    manifest=checked(manifest_ref);peer=passed_peer(peer_ref);global_audit=checked(global_ref)
    assert manifest['preparation_request']=={'file':request_name,'sha256':sha(request_name)} and manifest['inventory']==request['inventory']
    assert peer['live_interface_manifest']==manifest_ref
    assert global_audit['integrity_status']=='passed' and global_audit['errors']==[] and global_audit['inventory_sha256']==INVENTORY_SHA
    assert {x['domain'] for x in global_audit['domains']}==OWNERS
    owners={};new_sources=set()
    replacement_rows={x['destination']:x for x in result['exact_replacements']}
    for owner,record in manifest['owners'].items():
        offer=checked(record['live_offer']);ledger=checked(record['live_ledger'])
        assert offer['original_isolated_candidate_offer']==record['original_candidate_offer']
        assert sha(record['candidate_ledger']['file'])==record['candidate_ledger']['sha256']==record['live_ledger']['sha256']
        assert offer['source_sha256']==ledger['source_sha256']
        assert next(x for x in global_audit['domains'] if x['domain']==owner)['ledger_sha256']==record['live_ledger']['sha256']
        sources=record['expected_owned_proof_sources'];assert set(sources)==set(offer['proof_files']);new_sources.update(sources)
        owners[owner]={'offer':record['live_offer'],'ledger':record['live_ledger'],'builder':binding['helper'],'actual_builder':request['actual_integration_execution'],'actual_builder_log':request['actual_integration_raw_log'],'independent_mapping_peer':peer_ref,'original_candidate_mapping_peer':record['candidate_mapping_peer'],'expected_owned_proof_sources':sources,'execution_kind':KIND,'execution_scope':SCOPE}
        original=replacement_rows[record['live_ledger']['file']]
        owners[owner]['original21_live_ledger_byte_copy']={'file':original['original21_byte_copy'],'sha256':original['before_sha256']}
        owners[owner]['integration_result']=request['integration_result']
        owners[owner]['integration_binding']=request['integration_binding']
        if owner=='applied':
            original_promotions=replacement_rows['book/coverage/applied-promotions.json']
            owners[owner]['original21_live_promotions_byte_copy']={'file':original_promotions['original21_byte_copy'],'sha256':original_promotions['before_sha256']}
        for index,(name,digest) in enumerate(sorted(request.get('historical_dry_run_evidence_sha256',{}).items())):
            owners[owner]['historical_dry_run_reference_'+str(index)]={'file':name,'sha256':digest}
        for name,digest in offer['required_live_integration_evidence_sha256'].items():assert sha(name)==digest
    selected=read(BASELINE);assert sha(BASELINE)==BASELINE_SHA and not (new_sources&set(selected['proof_files']))
    assert sha(request['selection_helper']['file'])==request['selection_helper']['sha256'] and request['selection_helper']['file']==SELECTOR
    assert sha(request['content_retainer']['file'])==request['content_retainer']['sha256'] and request['content_retainer']['file']==RETAINER
    out={'status':'independently_reviewed_installed_owner22_selection_plan','inventory':request['inventory'],'baseline_selection':{'file':BASELINE,'sha256':BASELINE_SHA},'baseline_audit':{'file':AUDIT,'sha256':sha(AUDIT)},'baseline_manifest':{'file':MANIFEST,'sha256':sha(MANIFEST)},'destination':'reports/full-coverage/checkpoint-22-selection.json','content_map':'book/coverage/checks/frozen21-input-content-bindings22-v1.json','helpers_sha256':{SELECTOR:sha(SELECTOR),RETAINER:sha(RETAINER)},'owners':owners,'expected_new_proof_sources':sorted(new_sources),'global_integrity':global_ref,'additional_frozen_inputs':request['additional_frozen_inputs'],'excluded_full_external_reference_sha256':request['excluded_full_external_reference_sha256'],'independent_live_interface_manifest':manifest_ref,'independent_live_interface_peer':peer_ref,'actual_integration_execution_kind':KIND,'scope':SCOPE}
    name=request['production_plan_destination'];assert not safe(name).exists();write_new(name,out)
    return {'selection_plan':name,'sha256':sha(name),'new_proof_sources':len(new_sources)}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--request',required=True);parser.add_argument('--stage',choices=['interfaces','plan'],required=True)
    parser.add_argument('--interface-manifest');parser.add_argument('--independent-peer');parser.add_argument('--global-integrity');args=parser.parse_args()
    if args.stage=='interfaces':
        assert args.interface_manifest is args.independent_peer is args.global_integrity is None
        result=interfaces(args.request)
    else:
        assert args.interface_manifest and args.independent_peer and args.global_integrity
        refs=[{'file':n,'sha256':sha(n)} for n in (args.interface_manifest,args.independent_peer,args.global_integrity)]
        result=plan(args.request,*refs)
    print(json.dumps(result))
