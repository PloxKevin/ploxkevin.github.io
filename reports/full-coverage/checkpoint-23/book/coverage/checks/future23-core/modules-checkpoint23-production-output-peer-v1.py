from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,re,copy
R=Path('/home/oxrexkevin/SafetyBased');sys.dont_write_bytecode=True
sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
S='reports/full-coverage/checkpoint-23-selection.json'
P='book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v3.json'
C='book/coverage/checks/frozen22-input-content-bindings23-v1.json'
O=Path('/tmp/modules-checkpoint23-production-output-independent-confirmation-v1.json')
cache={}
def path(n):
    p=Path(n);assert not p.is_absolute() and str(p)==n and '..' not in p.parts
    q=(R/p).resolve();assert q.is_relative_to(R.resolve());return q
def sha(n,fresh=False):
    if fresh or n not in cache:cache[n]=hashlib.sha256(path(n).read_bytes()).hexdigest()
    return cache[n]
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):assert sha(r['file'])==r['sha256'];return read(r['file'])
def hashes(rows):
    for n,s in rows.items():assert sha(n)==s,n
def actual(n,code):
    a=read(n);assert type(a['actual_exit_code'])is int and a['actual_exit_code']==code
    assert sha(a['log'])==a['log_sha256']
    before=a['helper_sha256_before'];after=a['helper_sha256_after'];assert before==after
    for f,s in before.items():assert sha(f)==s
    return a
assert not O.exists()
execution_name='reports/full-coverage/prepare-checkpoint23-selection-execution-v2.json'
actual_execution=actual(execution_name,0)
assert actual_execution['actual_command']==['python3','book/coverage/prepare_checkpoint23_selection_v3.py','--plan',P]
failed_execution_name='reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json';actual(failed_execution_name,1)
s=read(S);p=read(P);m=checked(p['baseline_manifest']);base=checked(p['baseline_selection']);binding=read('book/coverage/checks/root-owner23-reviewed-candidate-bindings-v1.json')
assert s['status']=='explicit_current51_source_matched_selection_requires_fresh_aggregate_audit' and s['coverage_complete'] is False
assert s['proof_file_count']==1131 and len(s['proof_files'])==1131 and s['new_file_count']==18
assert s['selection_plan']==P and s['selection_plan_sha256']==sha(P)
assert s['current_inventory']=='book/coverage/inventory-after-correction51.json'
assert s['current_inventory_sha256']==sha('book/coverage/inventory.json')==sha(s['current_inventory'])=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert s['baseline_selection']==p['baseline_selection']['file'] and s['baseline_selection_sha256']==p['baseline_selection']['sha256']=='083fe75e535ebbd37326e34407d13b90357738ea7f4244eb1cfe5da8226f9ff9'
assert s['deliberate_baseline_source_revisions']=={}
assert len(base['proof_files'])==1113 and len(m['frozen_inputs_sha256'])==34051
assert s['previous_frozen_input_content_binding']['file']==C and s['previous_frozen_input_content_binding']['sha256']==sha(C)
codepeer_name='book/coverage/checks/future23-core/checkpoint23-owner-alias-helpers-independent-foundations-review-v1.json'
assert sha(codepeer_name)=='b68086df2c8f34d2ae5d5cebf00ad82a91776dd3d6997b2ca6e1e311548f6e0e'
codepeer=read(codepeer_name);assert 'pass' in codepeer['status'] and codepeer.get('errors',[])==[]
hashes(p['helpers_sha256'])
assert p['helpers_sha256']=={'book/coverage/prepare_checkpoint23_selection_v3.py':'3d646ccd946674944edd86bf55b10c5d5a4ee3cda4a1e7498f41aae8af6f226d','book/coverage/retain_baseline_inputs23_v3.py':'904341fa346e1e76cf6914b5660b978666bf0653664e75b1517e0400b9a25068'}
authorization=p['authorized_baseline_owner_evidence_aliases']
assert set(authorization)=={'actual_integration_execution','integration_result','aliases'}
oldpaths={'book/coverage/'+o+'.json' for o in ('core','foundations','modules','applied')}
assert set(authorization['aliases'])==oldpaths
result=checked(authorization['integration_result']);integration=checked(authorization['actual_integration_execution'])
assert integration['actual_exit_code']==0 and result['applied'] is True
replaced={r['destination']:r for r in result['exact_replacements']}
for n,a in authorization['aliases'].items():
    assert a['original_sha256']==m['working_inputs_sha256'][n]==replaced[n]['before_sha256']
    assert a['immutable_byte_copy']=={'file':replaced[n]['original22_byte_copy'],'sha256':replaced[n]['before_sha256']}
    assert sha(a['immutable_byte_copy']['file'])==a['original_sha256']
    assert sha(n)==replaced[n]['candidate']['sha256']
first=sorted(base['proof_files'])[0];firstrow=s['proof_files'][first]
source_count=0;evidence_bound={}
for source,row in base['proof_files'].items():
    selected=s['proof_files'][source];assert sha(source)==selected['sha256']==row['sha256']
    if source!=first:assert selected==row
    else:
        for k,v in row.items():
            if k!='evidence_sha256':assert selected[k]==v
        changed={n:a for n,a in authorization['aliases'].items() if n in row['evidence_sha256']}
        assert len(changed)==4
        assert selected['checkpoint23_original_baseline_owner_evidence']=={'original_baseline_selection':p['baseline_selection'],'original_baseline_source':source,'original_row_body':row,'authorized_original_path_aliases':changed}
        for n,d in row['evidence_sha256'].items():
            if n in changed:
                a=changed[n];assert d==a['original_sha256']
                assert selected['evidence_sha256'][a['immutable_byte_copy']['file']]==d
                assert selected['evidence_sha256'][n]==replaced[n]['candidate']['sha256']!=d
            else:assert selected['evidence_sha256'][n]==d
    hashes(selected['evidence_sha256']);evidence_bound.update(selected['evidence_sha256']);source_count+=1
new=set(s['proof_files'])-set(base['proof_files']);assert new==set(p['expected_new_proof_sources']) and len(new)==18
for owner,r in p['owners'].items():
    offer=checked(r['offer']);ledger=checked(r['ledger'])
    assert sha(r['ledger']['file'])==r['ledger']['sha256']==binding['owners'][owner]['candidate_ledger']['sha256']
    assert s['offers_sha256'][r['offer']['file']]==r['offer']['sha256']
    assert s['independent_owner_mapping_peers'][owner]==r['independent_mapping_peer']
    for n,row in offer['proof_files'].items():
        selected=copy.deepcopy(s['proof_files'][n]);record_name=selected.pop('original_actual_zero_record')
        assert selected==row and sha(n)==row['sha256'];hashes(row['evidence_sha256']);evidence_bound.update(row['evidence_sha256'])
        assert record_name in row['evidence_sha256']
        record=read(record_name);assert record.get('actual_exit_code',record.get('exit_code'))==0
        command=record.get('command',record.get('actual_command'));assert command[:3]==['lake','env','lean'] and len(command)==4
        assert record['source_sha256_before']==record['source_sha256_after']==row['sha256']
    hashes(offer.get('required_external_import_dependencies',{}))
global_record=read(s['global_integrity']);assert sha(s['global_integrity'])==s['global_integrity_sha256']==p['global_integrity']['sha256']
assert global_record['integrity_status']=='passed' and global_record['errors']==[] and global_record['inventory_sha256']==s['current_inventory_sha256']
assert {r['domain']:r['ledger_sha256'] for r in global_record['domains']}=={o:r['ledger']['sha256'] for o,r in p['owners'].items()}
allnames=set();public=0;typed=0;imports=0
for n,row in s['proof_files'].items():
    text=path(n).read_text();ds=declarations(text);allnames.update(d['name'] for d in ds);typed+=len(ds);public+=sum(d['kind']in('theorem','lemma') for d in ds)
    for line in re.findall(r'^import[^\n]*',text,re.M):
        for module in line.split()[1:]:
            if module.startswith('SafeLearning.'):
                assert 'verification/lean/'+module.replace('.','/')+'.lean' in s['proof_files'];imports+=1
assert public==9193
claims=0
for owner,r in p['owners'].items():
    ledger=checked(r['ledger'])
    for c in ledger['material_claims']+[c for e in ledger['exercises'] for c in e['claims']]:assert set(c['lean_declarations'])<=allnames;claims+=1
for n,row in base['extra_frozen_inputs'].items():assert s['extra_frozen_inputs'][n]==row
for n,row in p['additional_frozen_inputs'].items():assert s['extra_frozen_inputs'][n]==row
for n,row in s['extra_frozen_inputs'].items():assert sha(n)==row['sha256'];evidence_bound[n]=row['sha256']
evidence_bound.update({n:r['sha256'] for n,r in s['proof_files'].items()})
content=read(C)
assert content['status']=='all_original_frozen_inputs_retained_by_exact_content_fingerprints'
assert content['authorized_baseline_owner_evidence_aliases']==authorization
assert content['baseline_selection']==s['baseline_selection'] and content['baseline_selection_sha256']==s['baseline_selection_sha256']
assert content['baseline_manifest']==p['baseline_manifest']['file'] and content['baseline_manifest_sha256']==p['baseline_manifest']['sha256']
assert content['original_input_count']==len(content['input_bindings'])==34051
assert {r['original_frozen_path']:r['sha256'] for r in content['input_bindings']}==m['frozen_inputs_sha256']
assert len({r['original_frozen_path'] for r in content['input_bindings']})==34051
assert len(content['new_unique_snapshot_aliases'])==content['new_unique_snapshot_alias_count']
for n,d in content['new_unique_snapshot_aliases'].items():assert sha(n)==d==firstrow['evidence_sha256'][n]
for row in content['input_bindings']:
    original=m['snapshot']+'/'+row['original_frozen_path'];retained=row['retained_input'];digest=row['sha256']
    assert sha(original)==digest==sha(retained)==evidence_bound[retained]
assert content['new_unique_snapshot_alias_bytes']==sum(path(n).stat().st_size for n in content['new_unique_snapshot_aliases'])
assert content['retained_existing_content_rows']+content['new_unique_snapshot_alias_count']==34051
print('All1131/9193 sources, original rows and four aliases, actual36 records and34051 content bindings exact.',flush=True)
for n,d in binding['exact_current51_safelearning_assets_sha256'].items():assert sha(n,fresh=True)==d
for n,row in replaced.items():assert sha(n,fresh=True)==row['candidate']['sha256']
assert sha(S,fresh=True)==sha(S) and sha(P,fresh=True)==s['selection_plan_sha256']
out={'status':'independent_actual_checkpoint23_production_selection_and_original_content_map_confirmation_passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),'actual_selection':ref(S),'actual_production_execution':ref(execution_name),'preserved_first_production_failure':ref(failed_execution_name),'selection_plan':ref(P),'content_map':ref(C),'independent_v3_alias_helper_code_peer':ref(codepeer_name),'baseline22_manifest':p['baseline_manifest'],'current_inventory':p['inventory'],'proof_file_count':1131,'new_proof_file_count':18,'public_theorem_or_lemma_count':public,'all_public_typed_declaration_count':typed,'mapped_claim_count':claims,'local_import_reference_count':imports,'original_frozen22_input_count':34051,'strict_old_owner_evidence_alias_count':4,'actual_original_baseline_row_body_retained':True,'additional_frozen_input_count':len(p['additional_frozen_inputs']),'new_unique_snapshot_alias_count':content['new_unique_snapshot_alias_count'],'current_live_owner_and_promotions_asset_count':5,'current_source51_asset_count':31,'errors':[],'coverage_complete':False,'scope':'Read-only actual production output confirmation. Preserved original baseline row bodies/historical paths/hashes use only the exact four authorized genuine old-working-owner archive bytes, while fresh live refs use their installed hashes. Original review/compiler commands and times remain historical. New sources still require a fresh frozen23 aggregate, kernel replay and all-theorem axiom audit; no such pass is inferred here.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':hashlib.sha256(O.read_bytes()).hexdigest()}))
