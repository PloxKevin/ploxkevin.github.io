from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.dont_write_bytecode=True
sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
P='book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v1.json'
O=Path('/tmp/root23-installed-owner-selection-plan-independent-modules-confirmation-v1.json')
cache={}
def sha(n):
    p=Path(n);assert not p.is_absolute() and str(p)==n and '..' not in p.parts
    assert (R/p).resolve().is_relative_to(R.resolve())
    if n not in cache:cache[n]=hashlib.sha256((R/p).read_bytes()).hexdigest()
    return cache[n]
def read(n):return json.loads((R/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):assert sha(r['file'])==r['sha256'];return read(r['file'])
def hashes(rows):
    for n,s in rows.items():assert sha(n)==s,n
def zero(a):
    codes=[a[k] for k in ('actual_exit_code','exit_code') if k in a]
    assert codes and all(type(c)is int and c==0 for c in codes)
assert not O.exists()
p=read(P)
assert p['status']=='independently_reviewed_installed_owner23_selection_plan'
assert p['inventory']==ref('book/coverage/inventory-after-correction51.json')
assert p['inventory']['sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'==sha('book/coverage/inventory.json')
assert p['destination']=='reports/full-coverage/checkpoint-23-selection.json' and p['content_map']=='book/coverage/checks/frozen22-input-content-bindings23-v1.json'
assert not (R/p['destination']).exists() and not (R/p['content_map']).exists()
hashes(p['helpers_sha256'])
assert p['helpers_sha256']['book/coverage/prepare_checkpoint23_selection_v1.py']=='5811fc10687074862bfbb273017eb72c2f8990b4e44a18a4f2cf05c7037a8f67'
assert (R/'book/coverage/retain_baseline_inputs23.py').read_bytes()==(R/'book/coverage/retain_baseline_inputs22.py').read_bytes()
base=checked(p['baseline_selection']);manifest=checked(p['baseline_manifest']);audit=checked(p['baseline_audit'])
assert len(base['proof_files'])==1113 and len(manifest['frozen_inputs_sha256'])==34051
assert audit['status']=='passed' and audit['proof_file_count']==1113 and audit['theorem_count']==9002 and all(r['exit_code']==0 for r in audit['checks'])
assert p['baseline_selection']['sha256']=='083fe75e535ebbd37326e34407d13b90357738ea7f4244eb1cfe5da8226f9ff9'
interfaces=checked(p['independent_live_interface_manifest']);ip=checked(p['independent_live_interface_peer'])
assert ip['status']=='independent_actual_four_owner23_live_interface_outputs_confirmation_passed' and ip['errors']==[]
assert ip['live_interface_manifest']==p['independent_live_interface_manifest']
assert p['independent_live_interface_peer']['sha256']=='02ba2d4348b05bf0b6300116d9ff3b825d8952da1e12d341852fa25726756c79'
request=checked(interfaces['preparation_request'])
binding=checked(request['integration_binding']);g=checked(p['global_integrity'])
assert g['integrity_status']=='passed' and g['errors']==[] and g['inventory_sha256']==p['inventory']['sha256']
assert p['actual_integration_execution_kind']=='actual_guarded_candidate_integration_copy'
assert set(p['owners'])==set(binding['owners'])=={'core','foundations','applied','modules'}
assert p['additional_frozen_inputs']==request['additional_frozen_inputs']
assert p['excluded_full_external_reference_sha256']==request['excluded_full_external_reference_sha256']
offers={};selection=dict(base['proof_files']);new=set();record_count=0
for owner,r in p['owners'].items():
    ir=interfaces['owners'][owner];offer=checked(r['offer']);offers[owner]=offer;ledger=checked(r['ledger'])
    assert r['offer']==ir['live_offer'] and r['ledger']==ir['live_ledger']
    assert r['builder']==binding['helper'] and r['actual_builder']==request['actual_integration_execution'] and r['actual_builder_log']==request['actual_integration_raw_log']
    assert r['execution_kind']=='actual_guarded_candidate_integration_copy'
    assert r['independent_mapping_peer']==p['independent_live_interface_peer'] and r['original_candidate_mapping_peer']==ir['candidate_mapping_peer']
    assert r['integration_result']==request['integration_result'] and r['integration_binding']==request['integration_binding']
    builder=checked(r['actual_builder']);zero(builder)
    assert builder['actual_command'][-1]=='--apply' and sha(r['actual_builder_log']['file'])==r['actual_builder_log']['sha256']==builder['log_sha256']
    assert r['ledger']['sha256']==next(q['ledger_sha256'] for q in g['domains'] if q['domain']==owner)
    assert set(r['expected_owned_proof_sources'])==set(offer['proof_files'])==set(binding['owners'][owner]['new_immutable_proof_sources'])
    assert sha(r['original22_live_ledger_byte_copy']['file'])==r['original22_live_ledger_byte_copy']['sha256']==binding['owners'][owner]['held22_ledger_sha256']
    if owner=='applied':
        assert sha(r['original22_live_promotions_byte_copy']['file'])==r['original22_live_promotions_byte_copy']['sha256']==manifest['working_inputs_sha256']['book/coverage/applied-promotions.json']
    for source,row in offer['proof_files'].items():
        assert source not in selection and sha(source)==row['sha256'];hashes(row['evidence_sha256'])
        selection[source]=row;new.add(source)
        br=binding['owners'][owner]['new_immutable_proof_sources'][source]
        assert br['sha256']==row['sha256']
        for pair in br['actual_pair']:
            a=checked({'file':pair['file'],'sha256':pair['sha256']});zero(a)
            assert a['source_sha256_before']==a['source_sha256_after']==row['sha256']
            assert pair['sha256'] in row['evidence_sha256'].values()
            assert pair['canonical_raw_log']['sha256'] in row['evidence_sha256'].values()
            record_count+=1
    hashes(offer.get('required_external_import_dependencies',{}))
for source,row in base['proof_files'].items():assert sha(source)==row['sha256'];hashes(row['evidence_sha256'])
assert len(selection)==1131 and len(new)==18 and record_count==36
assert set(p['expected_new_proof_sources'])==new
names=set();public_count=0;typed_count=0
for source in selection:
    text=(R/source).read_text();ds=declarations(text);names.update(d['name'] for d in ds)
    public_count+=sum(d['kind'] in ('theorem','lemma') for d in ds);typed_count+=len(ds)
    for line in re.findall(r'^import[^\n]*',text,re.M):
        for dep in line.split()[1:]:
            if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in selection,(source,dep)
assert public_count==9193
claim_count=0
for owner,r in p['owners'].items():
    ledger=checked(r['ledger'])
    for claim in ledger['material_claims']+[c for e in ledger['exercises'] for c in e['claims']]:
        assert set(claim['lean_declarations'])<=names,(owner,claim['id']);claim_count+=1
    assert set(offers[owner].get('required_external_import_dependencies',{}))<=set(selection)
allowed={'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'}
for n,row in p['additional_frozen_inputs'].items():
    assert set(row)=={'sha256','scope'} and row['scope']=='immutable_audit_or_local_source_evidence'
    assert n.startswith(('book/coverage/','reports/full-coverage/source-history/')) and Path(n).suffix in allowed
    assert sha(n)==row['sha256'] and row['sha256'] not in p['excluded_full_external_reference_sha256']
for n,row in base['extra_frozen_inputs'].items():assert sha(n)==row['sha256']
print('1131 sources/9193 public exports, all36 actual records, import closure and every literal declaration checked.',flush=True)
out={'status':'independent_actual_installed_owner23_selection_plan_confirmation_passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),'selection_plan':ref(P),'live_interface_manifest':p['independent_live_interface_manifest'],'live_interface_peer':p['independent_live_interface_peer'],'fresh_global_integrity':p['global_integrity'],'selection_helper_sha256':p['helpers_sha256'],'baseline22_manifest':p['baseline_manifest'],'owner_offers':{o:r['offer'] for o,r in p['owners'].items()},'proof_file_count':1131,'new_proof_file_count':18,'public_theorem_or_lemma_count':public_count,'all_public_typed_declaration_count':typed_count,'actual_paired_record_count':36,'all_mapped_claim_count':claim_count,'additional_frozen_input_count':len(p['additional_frozen_inputs']),'errors':[],'scope':'Independent read-only check of the genuinely installed current51 four-owner selection plan. All18 fresh proof sources have unchanged paired actual compiler records; every original candidate/semantic review time remains historical. The production selector/content retainer was not executed. Fresh frozen23 aggregate/kernel/axiom verification remains required.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':hashlib.sha256(O.read_bytes()).hexdigest()}))
