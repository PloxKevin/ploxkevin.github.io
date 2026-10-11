"""Independent read-only actual checkpoint27 selection/content closure reader."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,copy,ast,importlib.util
R=Path('/home/oxrexkevin/SafetyBased')
SELECTION='reports/full-coverage/checkpoint-27-selection.json'
BASELINE='reports/full-coverage/checkpoint-26-selection.json'
MANIFEST='reports/full-coverage/checkpoint-26-manifest.json'
AUDIT='reports/full-coverage/lean-checkpoint-26/verification-original.json'
MAP='book/coverage/checks/frozen26-input-content-bindings27-v1.json'
ACTUAL='reports/full-coverage/prepare-checkpoint27-selection-execution-v1.json'
DRAFT='book/coverage/checks/future27-core/checkpoint27-installed-owner-selection-plan-draft-v1.json'
PLANPEER='book/coverage/checks/future27-core/checkpoint27-installed-selection-plan-independent-modules-confirmation-v1.json'
FREEZER='book/coverage/freeze_checkpoint27_v2.py'
OUT=Path('/tmp/modules-checkpoint27-production-output-check-result-v1.json')
CACHE={}
def path(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts and Path(n).as_posix()==n,n
    p=R/n;assert not p.is_symlink() and p.resolve().is_relative_to(R.resolve()),n
    return p
def sha(n):
    if n not in CACHE:CACHE[n]=hashlib.sha256(path(n).read_bytes()).hexdigest()
    return CACHE[n]
def read(n):return json.loads(path(n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(d):
    assert isinstance(d,dict) and set(d)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',d['sha256'])
    assert sha(d['file'])==d['sha256'],d['file'];return read(d['file'])
def zero(d):
    v=[d[k] for k in ['actual_exit_code','exit_code'] if k in d];assert v and all(type(x) is int and x==0 for x in v)
def commands(d):
    c=[d[k] for k in ['actual_command','command'] if k in d];assert c and all(x==c[0] for x in c);return c[0]
def exact(m):
    for n,h in m.items():assert sha(n)==h,n
def add(m,n,h):assert n not in m or m[n]==h,(n,m.get(n),h);m[n]=h
def rowsha(d):return hashlib.sha256(json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
assert not OUT.exists()
assert sha(BASELINE)=='12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f'
assert sha(MANIFEST)=='ef777b585d9654e5dd784160dd4e9502eaae230d1f4fefcd9bdb2458c347f896'
assert sha(AUDIT)=='41e872c24a3c0e33e1e284d5247353815984df529ecd479041a8ed3eca0d206e'
assert sha(FREEZER)=='4c964b933eac26217b6965efb9b5f4e27649402f63b0a77662de0b5692af0e14'
constants={}
for node in ast.parse(path(FREEZER).read_text()).body:
    if isinstance(node,ast.Assign) and isinstance(node.targets[0],ast.Name) and node.targets[0].id.startswith('CHECKPOINT27_'):
        try:constants[node.targets[0].id]=ast.literal_eval(node.value)
        except(ValueError,TypeError):assert node.targets[0].id=='CHECKPOINT27_SELECTION_SHA256'
assert constants['CHECKPOINT27_SELECTION']==SELECTION
exceptions=constants['CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS'];assert len(exceptions)==7;exact(exceptions)
selected=read(SELECTION);baseline=read(BASELINE);manifest=read(MANIFEST);audit=read(AUDIT);content=read(MAP)
actual=read(ACTUAL);zero(actual);assert actual['status']=='passed'
assert actual['helper_sha256_before']==actual['helper_sha256_after'];exact(actual['helper_sha256_after'])
assert actual['helper_sha256_after']['book/coverage/prepare_checkpoint27_selection_v2.py']=='1cdb720a1380e6a36aff457f2587d01123fd8455b1beed35a576dd501605efb9'
assert actual['helper_sha256_after']['book/coverage/retain_baseline_inputs27_v1.py']=='159d6f53b2a2a05cbc68155d2925a14dc46e90b2d47392ab32c6b822877e2d33'
assert sha(actual['log'])==actual['log_sha256']
plan_name=selected['selection_plan'];assert sha(plan_name)==selected['selection_plan_sha256'];plan=read(plan_name)
assert commands(actual)==['python3','book/coverage/prepare_checkpoint27_selection_v2.py','--plan',plan_name,'--apply']
assert actual['actual_workdir']==str(R)
assert sha(DRAFT)=='d2f99ec31b5e110f0f2ab0a68f5b316b90ca85c2a78dbba35e53e3b7fc80ef92'
draft=read(DRAFT);assert draft['status']=='installed_current55_owner27_selection_inputs_awaiting_independent_plan_review'
assert sha(PLANPEER)=='bbda8313b6f6230b6d464f21476266c34e171e13e8e9b1f0bd3fc3066d802a73'
planpeer=read(PLANPEER);assert planpeer['status']=='passed' and planpeer['errors']==[] and planpeer['reviewed_plan']==ref(DRAFT)
assert plan['status']=='independently_reviewed_installed_current55_owner27_selection_plan'
for k,v in draft.items():
    if k not in {'status','helpers_sha256'}:assert plan[k]==v,k
expected_helpers=dict(draft['helpers_sha256']);expected_helpers.pop('book/coverage/export_audit27_v2.py');expected_helpers['book/coverage/export_audit27_v3.py']='f1f99c8ae8809dcebf715b308b0d40e5c03bca650cd7db72532269adef1ed8a4'
assert plan['helpers_sha256']==expected_helpers;exact(expected_helpers)
new_plan_fields={k:v for k,v in plan.items() if k not in draft};assert ref(PLANPEER) in new_plan_fields.values(),new_plan_fields
assert selected['status']=='explicit_current55_source_matched_selection_requires_fresh_aggregate_audit'
assert selected['coverage_complete'] is False and selected['deliberate_baseline_source_revisions']=={}
assert selected['proof_file_count']==1175 and selected['new_file_count']==8
assert selected['baseline_selection']==BASELINE and selected['baseline_selection_sha256']==sha(BASELINE)
assert selected['actual_passing_baseline_audit']==AUDIT and selected['actual_passing_baseline_audit_sha256']==sha(AUDIT)
assert len(baseline['proof_files'])==audit['proof_file_count']==1167 and audit['theorem_count']==9503 and audit['status']=='passed'
assert all(type(x['exit_code']) is int and x['exit_code']==0 for x in audit['checks'])
assert manifest['proof_files']==baseline['proof_files'] and manifest['status']=='formal_verification_passed_partial_coverage'
assert len(manifest['frozen_inputs_sha256'])==47277
assert plan['baseline_selection']==ref(BASELINE) and plan['baseline_manifest']==ref(MANIFEST) and plan['baseline_audit']==ref(AUDIT)
assert selected['current_inventory']==plan['inventory']['file']=='book/coverage/inventory-after-correction55.json'
assert selected['current_inventory_sha256']==plan['inventory']['sha256']==sha(selected['current_inventory'])==sha('book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
assert {n for n,h in assets.items() if sha(n)!=h}=={'SafeLearning/lyapunov-mpc.html','SafeLearning/verification.html'}
assert sha('SafeLearning/lyapunov-mpc.html')=='63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f'
assert sha('SafeLearning/verification.html')=='d01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53'
integration=checked(plan['integration_result']);installation=checked(plan['actual_integration_execution']);zero(installation)
assert integration['applied'] is True and integration['coverage_complete'] is False
assert integration['status']=='four_exact_reviewed_owner27_candidate_bytes_integrated_pending_fresh_current55_global_integrity_and_aggregate27_audit'
assert integration['actual_helper']['file']=='book/coverage/checks/root_integrate_owner27_candidates_v2.py'
assert sha(integration['actual_helper']['file'])==integration['actual_helper']['sha256']=='89a0933368edb7c0aeac1926a3d99cda97c81e8e309f531e759501bcb118cff5'
binding_ref={'file':integration['binding_manifest'],'sha256':integration['binding_manifest_sha256']};binding=checked(binding_ref)
assert commands(installation)==['python3',integration['actual_helper']['file'],binding_ref['file'],'--apply']
assert installation['helper_sha256_before']==installation['helper_sha256_after'];exact(installation['helper_sha256_after']);assert sha(installation['log'])==installation['log_sha256']
replacements={r['destination']:r for r in integration['exact_replacements']};assert set(replacements)=={'book/coverage/'+x+'.json' for x in ['core','foundations','applied','applied-promotions','modules']}
for n,row in replacements.items():
    assert sha(n)==row['candidate']['sha256']==sha(row['candidate']['file'])
    assert row['before_sha256']==manifest['working_inputs_sha256'][n]==sha(row['original26_byte_copy'])
authorization=plan['authorized_baseline_evidence_aliases'];assert set(authorization)=={'integration_result','actual_integration_execution','source_application','actual_source_application_execution','aliases'}
assert authorization['integration_result']==plan['integration_result'] and authorization['actual_integration_execution']==plan['actual_integration_execution']
application=checked(authorization['source_application']);app_execution=checked(authorization['actual_source_application_execution']);zero(app_execution)
assert authorization['source_application']['sha256']=='845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528' and authorization['actual_source_application_execution']['sha256']=='a255862de464e0f1acf284807c4a48b732bc69055cf71b445ea2df5920494805'
assert [r['correction_id'] for r in application['applications']]==[54,55]
assert application['selected26_proof_sources_unchanged']==1167 and application['five_installed26_owner_ledgers_unchanged'] is True
assert app_execution['helper_sha256_before']==app_execution['helper_sha256_after'];exact(app_execution['helper_sha256_after']);assert sha(app_execution['log'])==app_execution['log_sha256']
aliases=authorization['aliases'];assert set(aliases)==set(replacements)-{'book/coverage/applied-promotions.json'}|{'SafeLearning/lyapunov-mpc.html'}
for n,a in aliases.items():
    assert set(a)=={'original_sha256','immutable_byte_copy'} and a['original_sha256']==manifest['working_inputs_sha256'][n]
    assert sha(a['immutable_byte_copy']['file'])==a['immutable_byte_copy']['sha256']==a['original_sha256']
    if n in replacements:assert a['immutable_byte_copy']['file']==replacements[n]['original26_byte_copy']
    else:assert a['immutable_byte_copy']['file']=='reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root/'+n
first_name=sorted(baseline['proof_files'])[0];expected_first={};changed=[];initial_bound={}
for n,old in baseline['proof_files'].items():
    new=selected['proof_files'][n];assert sha(n)==old['sha256']==new['sha256'];normalized=dict(old['evidence_sha256']);used={}
    for original,a in aliases.items():
        if original in normalized:
            assert normalized.pop(original)==a['original_sha256'];add(normalized,a['immutable_byte_copy']['file'],a['immutable_byte_copy']['sha256']);used[original]=a
    for k,v in old.items():
        if k!='evidence_sha256':assert new[k]==v,(n,k)
    keys=set(old)
    if used:
        keys.add('checkpoint27_original_baseline_evidence');changed.append(n)
        assert new['checkpoint27_original_baseline_evidence']=={'original_baseline_selection':ref(BASELINE),'original_baseline_source':n,'original_row_canonical_json_sha256':rowsha(old),'authorized_original_path_aliases':used}
    assert set(new)==keys,(n,set(new)^keys)
    if n==first_name:expected_first=normalized
    else:assert new['evidence_sha256']==normalized
pairs=checked(plan['actual_canonical_readiness']);assert pairs['errors']==[] and pairs['source_count']==8 and pairs['public_theorem_count']==141 and pairs['actual_compiler_command_count']==16
expected_new={r['canonical_source']:r['source']['sha256'] for r in pairs['sources']};assert len(expected_new)==8
new_sources=set();owners={}
for owner,row in binding['owners'].items():
    offer=checked(row['reviewed_offer']);peer=checked(row['final_mapping_peer']);assert peer['status']==row['expected_final_mapping_peer_status'] and peer['errors']==[]
    assert row['destination']=='book/coverage/'+owner+'.json' and replacements[row['destination']]['candidate']==row['candidate']
    assert set(offer['proof_files'])==set(row['new_sources']);exact(offer['source_sha256']);zero(checked(row['actual_finalizer']))
    for source,proof in offer['proof_files'].items():
        assert source not in new_sources and source not in baseline['proof_files'];new_sources.add(source);assert proof['sha256']==expected_new[source]
        chosen=selected['proof_files'][source];expected=copy.deepcopy(proof)
        source_pairs=[p for p in pairs['actual_paired_records'] if p['source']['file']==source];assert len(source_pairs)==2 and {p['kind'] for p in source_pairs}=={'standalone','named'}
        expected['original_actual_zero_record']=next(p['actual_record']['file'] for p in source_pairs if p['kind']=='standalone');assert chosen==expected
        for p in source_pairs:
            rec=checked(p['actual_record']);zero(rec);assert rec['source']==source and rec['source_sha256_before']==rec['source_sha256_after']==proof['sha256']
            command=['lake','env','lean','SafeLearning/'+Path(source).name] if p['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(source).stem]
            assert commands(rec)==command and rec['actual_workdir']==str(R/'verification/lean')
            assert p['raw_log']=={'file':rec['log'],'sha256':rec['log_sha256']} and sha(rec['log'])==rec['log_sha256']
            assert sha(p['source_snapshot']['file'])==p['source_snapshot']['sha256']==proof['sha256']
            for key in ['actual_record','raw_log']:assert proof['evidence_sha256'][p[key]['file']]==p[key]['sha256']
    for x in [row['reviewed_offer'],row['final_mapping_peer'],row['actual_finalizer'],row['candidate']]:add(expected_first,x['file'],x['sha256'])
    owners[owner]={'offer':row['reviewed_offer'],'ledger':ref(row['destination']),'mapping_peer':row['final_mapping_peer'],'new_sources':len(offer['proof_files'])}
assert new_sources==set(expected_new) and set(selected['proof_files'])==set(baseline['proof_files'])|new_sources
assert selected['offers_sha256']=={r['reviewed_offer']['file']:r['reviewed_offer']['sha256'] for r in binding['owners'].values()}
assert selected['independent_owner_mapping_peers']=={o:r['final_mapping_peer'] for o,r in binding['owners'].items()}
global_data=checked(plan['global_integrity']);assert global_data['integrity_status']=='passed' and global_data['errors']==[] and global_data['inventory_sha256']==selected['current_inventory_sha256'] and global_data['mathematical_coverage_complete'] is False
assert selected['global_integrity']==plan['global_integrity']['file'] and selected['global_integrity_sha256']==plan['global_integrity']['sha256']
for d in global_data['domains']:assert d['ledger_sha256']==replacements['book/coverage/'+d['domain']+'.json']['candidate']['sha256']
extras=copy.deepcopy(baseline['extra_frozen_inputs'])
for n,row in plan['additional_frozen_inputs'].items():
    assert set(row)=={'sha256','scope'} and row['scope']=='immutable_audit_or_local_source_evidence'
    assert any(path(n).resolve().is_relative_to((R/base).resolve()) for base in ['book/coverage','reports/full-coverage/source-history'])
    assert Path(n).suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'} or exceptions.get(n)==row['sha256']
    assert row['sha256'] not in set(plan['excluded_full_external_reference_sha256']);assert n not in extras or extras[n]==row;extras[n]=row
assert selected['extra_frozen_inputs']==extras
for n,row in extras.items():assert sha(n)==row['sha256'],n
for x in [plan['global_integrity'],plan['integration_result'],plan['actual_integration_execution'],binding_ref,plan['actual_canonical_readiness'],plan['independent_selection_helper_review']]:add(expected_first,x['file'],x['sha256'])
add(expected_first,plan_name,sha(plan_name))
for n,h in plan['helpers_sha256'].items():add(expected_first,n,h)
# Reconstruct retention using the same specified content-addressed ordering,
# independently of retainer implementation; verify exact physical old47277 bytes.
for n,row in selected['proof_files'].items():
    add(initial_bound,n,row['sha256'])
    evidence=expected_first if n==first_name else row['evidence_sha256']
    for e,h in evidence.items():add(initial_bound,e,h)
for n,row in extras.items():add(initial_bound,n,row['sha256'])
by_digest={}
for n,h in sorted(initial_bound.items()):by_digest.setdefault(h,n)
added={};rows=[];reused=0
for n,h in sorted(manifest['frozen_inputs_sha256'].items()):
    frozen=manifest['snapshot']+'/'+n;assert sha(frozen)==h,n
    retained=by_digest.get(h)
    if retained is None:
        retained=frozen;by_digest[h]=retained;added[retained]=h;add(expected_first,retained,h)
    else:reused+=1
    assert sha(retained)==h;rows.append({'original_frozen_path':n,'sha256':h,'retained_input':retained})
assert content['status']=='all_original_frozen_inputs_retained_by_exact_content_fingerprints'
assert content['baseline_selection']==BASELINE and content['baseline_selection_sha256']==sha(BASELINE)
assert content['baseline_manifest']==MANIFEST and content['baseline_manifest_sha256']==sha(MANIFEST)
assert content['baseline_actual_audit']==ref(AUDIT) and content['original_snapshot']==manifest['snapshot']
assert content['original_input_count']==len(content['input_bindings'])==47277 and content['input_bindings']==rows
assert content['authorized_baseline_evidence_aliases']==authorization
assert content['retained_existing_content_rows']==reused and content['new_unique_snapshot_aliases']==added and content['new_unique_snapshot_alias_count']==len(added)
assert content['new_unique_snapshot_alias_bytes']==sum(path(n).stat().st_size for n in added)
for n in [BASELINE,MANIFEST,AUDIT]:add(expected_first,n,sha(n))
add(expected_first,MAP,sha(MAP));assert selected['proof_files'][first_name]['evidence_sha256']==expected_first
assert selected['previous_frozen_input_content_binding']=={'file':MAP,'sha256':sha(MAP),'original_inputs':47277,'new_snapshot_aliases':len(added)}
spec=importlib.util.spec_from_file_location('output27names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
bound={};public_names=[];theorem_names=[];imports=0
for n,row in selected['proof_files'].items():
    assert sha(n)==row['sha256'];add(bound,n,row['sha256']);exact(row['evidence_sha256'])
    for e,h in row['evidence_sha256'].items():add(bound,e,h)
    src=path(n).read_text();decl=names.declarations(src);public_names.extend(d['name'] for d in decl);theorem_names.extend(d['name'] for d in decl if d['kind'] in ['theorem','lemma'])
    for line in names.without_comments(src).splitlines():
        if re.match(r'^\s*import\s',line):
            for module in line.split()[1:]:
                if module.startswith('SafeLearning.'):
                    assert 'verification/lean/'+module.replace('.','/')+'.lean' in selected['proof_files'];imports+=1
for n,row in extras.items():add(bound,n,row['sha256'])
assert len(public_names)==len(set(public_names))==12589 and len(theorem_names)==len(set(theorem_names))==9644
for row in rows:assert bound[row['retained_input']]==row['sha256']
for owner,row in binding['owners'].items():
    ledger=read(row['destination'])
    for claim in ledger['material_claims']+[c for e in ledger['exercises'] for c in e['claims']]:assert set(claim['lean_declarations'])<=set(public_names),(owner,claim['id'])
    assert sha(row['destination'])==row['candidate']['sha256']
assert sha('book/coverage/applied-promotions.json')==replacements['book/coverage/applied-promotions.json']['candidate']['sha256']
report={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','selection':ref(SELECTION),'selection_plan':ref(plan_name),'original_pending_plan':ref(DRAFT),'independent_original_plan_review':ref(PLANPEER),'actual_selection_execution':ref(ACTUAL),'actual_selection_raw_log':ref(actual['log']),'content_map':ref(MAP),'baseline26_selection':ref(BASELINE),'baseline26_manifest':ref(MANIFEST),'baseline26_actual_audit':ref(AUDIT),'actual_owner27_integration':plan['actual_integration_execution'],'actual_integration_result':plan['integration_result'],'source54_55_actual_application':authorization['source_application'],'global_integrity':plan['global_integrity'],'owners':owners,'proof_files':1175,'new_sources':8,'public_theorem_or_lemma_exports':9644,'all_typed_public_names':12589,'old_frozen_paths_retained_exact':47277,'baseline_source_rows_with_exact_five_original_aliases_and_compact_full_row_SHA':changed,'all_proof_and_evidence_bytes_rehashed':len(bound),'safelearning_imports_resolved':imports,'extra_frozen_inputs':len(extras),'all_claim_declarations_selected':True,'freezer':ref(FREEZER),'exact_seven_extra_suffix_exceptions':exceptions,'all_extra_inputs_eligible_under_checkpoint_specific_freezer':True,'coverage_complete':False,'actual_aggregate_or_publication_claim':False,'scope':'Independent actual production selection verification. Exact1167 baseline sources/full prior rows retrieved by original selection+sourcekey+fullrow SHA, genuine old owner/Lyapunov archives and47277 frozen paths/content bindings, current55 two source changes/current31 assets, installed five candidates/original review status/times, all1175 imports/claims and16 actual canonical records checked. Requires fresh frozen27 aggregate/kernel/all9644 axiom audit and actual publication.'}
OUT.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':'passed','result':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'sources':1175,'exports':9644,'frozen_paths':47277}))
