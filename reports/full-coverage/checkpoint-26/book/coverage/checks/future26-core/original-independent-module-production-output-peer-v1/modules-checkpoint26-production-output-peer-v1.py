"""Read-only independent actual checkpoint26 selection/content-map checker."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,importlib.util,sys,copy,ast
R=Path('/home/oxrexkevin/SafetyBased')
SELECTION='reports/full-coverage/checkpoint-26-selection.json'
BASELINE='reports/full-coverage/checkpoint-25-selection.json'
MANIFEST='reports/full-coverage/checkpoint-25-manifest.json'
MAP='book/coverage/checks/frozen25-input-content-bindings26-v1.json'
NATIVE='reports/full-coverage/owner26-reviewed-candidate-integration-v1.json'
ACTUAL='reports/full-coverage/prepare-checkpoint26-selection-execution-v1.json'
OUT=Path('/tmp/modules-checkpoint26-production-output-independent-confirmation-v1.json')
CACHE={}
def path(n):
    p=Path(n);assert isinstance(n,str) and n and not p.is_absolute() and '..' not in p.parts and str(p)==n,n
    assert (R/p).resolve().is_relative_to(R.resolve()),n
    return R/p
def sha(n):
    if n not in CACHE:CACHE[n]=hashlib.sha256(path(n).read_bytes()).hexdigest()
    return CACHE[n]
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):
    assert isinstance(r,dict) and set(r)=={'file','sha256'}
    assert sha(r['file'])==r['sha256'];return read(r['file'])
def zero(d):
    a=[d[k] for k in ['actual_exit_code','exit_code'] if k in d]
    assert a and all(type(v)==int and v==0 for v in a)
def exact(d):
    for n,h in d.items():assert sha(n)==h,n
def add(dest,n,h):assert n not in dest or dest[n]==h;dest[n]=h
assert not OUT.exists()
FREEZER='book/coverage/freeze_checkpoint26_v1.py'
FREEZER_SHA='c166cdbb81d19d47aa629b658e944250dab2cf401b2aa4f9d4956d3852ce2e6e'
assert sha(FREEZER)==FREEZER_SHA
freezer_tree=ast.parse(path(FREEZER).read_text())
freezer_constants={}
for node in freezer_tree.body:
    if not(isinstance(node,ast.Assign) and isinstance(node.targets[0],ast.Name) and node.targets[0].id.startswith('CHECKPOINT26_')):continue
    try:value=ast.literal_eval(node.value)
    except (ValueError,TypeError):
        assert node.targets[0].id=='CHECKPOINT26_SELECTION_SHA256' and ast.unparse(node.value)=='args.selection_sha256'
        continue
    assert node.targets[0].id not in freezer_constants
    freezer_constants[node.targets[0].id]=value
assert "parser.add_argument('--selection-sha256', required=True)" in path(FREEZER).read_text()
assert freezer_constants['CHECKPOINT26_SELECTION']==SELECTION
assert freezer_constants['CHECKPOINT26_SELECTION_SHA256'] is None
FREEZER_EXCEPTIONS=freezer_constants['CHECKPOINT26_EXACT_EXTRA_SUFFIX_EXCEPTIONS']
assert len(FREEZER_EXCEPTIONS)==6 and sorted(Path(n).suffix for n in FREEZER_EXCEPTIONS)==['.olean','.olean','.olean','.yml','.yml','.yml']
exact(FREEZER_EXCEPTIONS)

assert sha(BASELINE)=='3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'
assert sha(MANIFEST)=='0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'
selected=read(SELECTION);baseline=read(BASELINE);manifest=read(MANIFEST);content=read(MAP)
actual=read(ACTUAL);zero(actual);assert actual['status']=='passed'
assert sha(actual['log'])==actual['log_sha256']
assert actual['helper_sha256_before']==actual['helper_sha256_after']
exact(actual['helper_sha256_after'])
assert actual['helper_sha256_after']['book/coverage/prepare_checkpoint26_selection_v2.py']=='9e130aa89131e3fb9cd860ee898d95a9fd92e6fbe33723913c5ff5c86dcde3d9'
assert actual['helper_sha256_after']['book/coverage/retain_baseline_inputs26_v2.py']=='86ecc3a33de29841aaa6e117d56390305502e6f238151674890ce2e67c60302e'
plan_name=selected['selection_plan'];assert sha(plan_name)==selected['selection_plan_sha256'];plan=read(plan_name)
assert plan_name=='book/coverage/checks/future26-core/checkpoint26-installed-owner-selection-plan-v2.json'
old_plan=checked(plan['original_installed_owner_selection_plan_v1'])
assert plan['entire_original_installed_owner_selection_plan_v1_body_and_time']==old_plan
reverse_plan=copy.deepcopy(plan)
for key in ['original_installed_owner_selection_plan_v1','entire_original_installed_owner_selection_plan_v1_body_and_time','closed_interface_and_plan_original_byte_aliases','plan_closure_prepared_at_utc']:reverse_plan.pop(key)
reverse_plan['additional_frozen_inputs']=old_plan['additional_frozen_inputs'];reverse_plan['helpers_sha256']=old_plan['helpers_sha256'];assert reverse_plan==old_plan
closed_aliases=checked(plan['closed_interface_and_plan_original_byte_aliases'])
assert len(closed_aliases['aliases'])==6
for row in closed_aliases['aliases']:
    a,b=row['original'],row['immutable_original_byte_copy']
    assert sha(a['file'])==a['sha256']==b['sha256']==sha(b['file'])
    assert plan['additional_frozen_inputs'][b['file']]['sha256']==b['sha256']
    if a['file'].endswith('.json'):zero(read(a['file']))
closure_actual=read('reports/full-coverage/close-owner26-selection-plan-execution-v1.json');zero(closure_actual)
assert sha(closure_actual['log'])==closure_actual['log_sha256']
assert closure_actual['helper_sha256_before']==closure_actual['helper_sha256_after']
exact(closure_actual['helper_sha256_after'])
assert actual['actual_command']==['python3','book/coverage/prepare_checkpoint26_selection_v2.py','--plan',plan_name]
assert plan['status']=='independently_reviewed_installed_owner26_selection_plan'
assert selected['status']=='explicit_current53_source_matched_selection_requires_fresh_aggregate_audit'
assert selected['coverage_complete'] is False and selected['deliberate_baseline_source_revisions']=={}
assert selected['proof_file_count']==1167 and selected['new_file_count']==11
assert selected['current_inventory']==plan['inventory']['file']=='book/coverage/inventory-after-correction53.json'
assert selected['current_inventory_sha256']==plan['inventory']['sha256']==sha('book/coverage/inventory.json')==sha(selected['current_inventory'])=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
zero(checked(plan['actual_source53_apply']));application=checked(plan['actual_source53_application']);assert 'passed' in application['status'] and application['inventory_after']==plan['inventory']
assert selected['baseline_selection']==BASELINE and selected['baseline_selection_sha256']==sha(BASELINE)
assert plan['baseline_selection']==ref(BASELINE) and plan['baseline_manifest']==ref(MANIFEST)
assert len(baseline['proof_files'])==1156 and len(manifest['frozen_inputs_sha256'])==44111
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31
changed_assets={n for n,h in assets.items() if sha(n)!=h}
assert changed_assets=={'SafeLearning/lyapunov-mpc.html'};assert sha('SafeLearning/lyapunov-mpc.html')=='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
assert sha('SafeLearning/nn-in-the-loop.html')=='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
native=read(NATIVE);assert native['applied'] is True and native['status']=='four_exact_reviewed_owner26_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate26_audit'
authorization=plan['authorized_baseline_owner_evidence_aliases']
assert checked(authorization['integration_result'])==native
installation=checked(authorization['actual_integration_execution']);zero(installation)
assert sha(installation['log'])==installation['log_sha256']
assert native['actual_helper']=='book/coverage/checks/root_integrate_owner26_candidates_v2.py'
assert sha(native['actual_helper'])==native['actual_helper_sha256']=='0ad44698e172d8d3b9c52794d2d5a6531c0d19c7828cdad22cd380c26a44fe5c'
replacements={d['destination']:d for d in native['exact_replacements']}
assert set(replacements)=={'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules']}|{'book/coverage/applied-promotions.json'}
for n,row in replacements.items():
    assert sha(n)==row['candidate']['sha256']==sha(row['candidate']['file'])
    assert row['before_sha256']==manifest['working_inputs_sha256'][n]==sha(row['original25_byte_copy'])
assert not any('future_code_update' in k for k in native)
aliases=authorization['aliases'];assert set(aliases)==set(replacements)-{'book/coverage/applied-promotions.json'}
for n,a in aliases.items():
    assert a=={'original_sha256':manifest['working_inputs_sha256'][n],'immutable_byte_copy':{'file':replacements[n]['original25_byte_copy'],'sha256':manifest['working_inputs_sha256'][n]}}
global_data=checked(plan['global_integrity'])
assert global_data['integrity_status']=='passed' and global_data['errors']==[] and global_data['inventory_sha256']==selected['current_inventory_sha256']
assert selected['global_integrity']==plan['global_integrity']['file'] and selected['global_integrity_sha256']==plan['global_integrity']['sha256']
interfaces=checked(plan['independent_live_interface_manifest']);interface_peer=checked(plan['independent_live_interface_peer'])
assert 'passed' in interface_peer['status'] and interface_peer.get('errors',[])==[]
assert interface_peer['live_interface_manifest']==plan['independent_live_interface_manifest']
assert interfaces['execution_kind']=='actual_guarded_candidate_integration_copy'
for owner,entry in interfaces['owners'].items():
    original=checked(entry['original_candidate_offer']);live=checked(entry['live_offer'])
    reverse=copy.deepcopy(live)
    for k in entry['appended_live_interface_fields']:reverse.pop(k)
    for k in entry['changed_original_fields']:reverse[k]=original[k]
    assert reverse==original
    assert plan['owners'][owner]['offer']==entry['live_offer']
    assert plan['owners'][owner]['ledger']==entry['live_ledger']
    assert entry['live_ledger']['sha256']==entry['candidate_ledger']['sha256']
    assert sha(entry['live_ledger']['file'])==sha(entry['candidate_ledger']['file'])==entry['live_ledger']['sha256']
first_name=sorted(baseline['proof_files'])[0];first=selected['proof_files'][first_name]
expected_first={};changed_alias_sources=[]
for n,old in baseline['proof_files'].items():
    new=selected['proof_files'][n];assert sha(n)==old['sha256']==new['sha256']
    normalized=dict(old['evidence_sha256']);used={}
    for original,a in aliases.items():
        if original in normalized:
            assert normalized.pop(original)==a['original_sha256']
            immutable=a['immutable_byte_copy'];add(normalized,immutable['file'],immutable['sha256']);used[original]=a
    for k,v in old.items():
        if k!='evidence_sha256':assert new[k]==v,(n,k)
    expected_keys=set(old)
    if used:
        expected_keys.add('checkpoint26_original_baseline_owner_evidence');changed_alias_sources.append(n)
        assert new['checkpoint26_original_baseline_owner_evidence']=={'original_baseline_selection':ref(BASELINE),'original_baseline_source':n,'original_row_body':old,'authorized_original_path_aliases':used}
    if n==first_name:
        expected_keys.add('checkpoint26_inherited_snapshot_provenance_scope');expected_first=normalized
    else:assert new['evidence_sha256']==normalized
    assert set(new)==expected_keys,(n,set(new)^expected_keys)
assert first['checkpoint26_inherited_snapshot_provenance_scope']=='Every frozen25 original path and byte hash is retained by the exact content binding map. Original audits, commands and times remain historical.'
for n in [BASELINE,MANIFEST,plan['baseline_audit']['file'],plan_name]:add(expected_first,n,sha(n))
for r in plan['prior_checkpoint25_selection_provenance'].values():
    assert set(r)=={'file','sha256'} and sha(r['file'])==r['sha256'];add(expected_first,r['file'],r['sha256'])
r=plan['baseline_owner_evidence_alias_plan_preparation_helper'];assert sha(r['file'])==r['sha256'];add(expected_first,r['file'],r['sha256'])
for p in path('reports/full-coverage/lean-checkpoint-25').rglob('*'):
    if p.is_file():n=str(p.relative_to(R));add(expected_first,n,sha(n))
owners={};newproofs={};all_decl=set();public=0
spec=importlib.util.spec_from_file_location('names26_output',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
for owner,refs in plan['owners'].items():
    offer=checked(refs['offer']);ledger=checked(refs['ledger']);peer=checked(refs['independent_mapping_peer'])
    assert 'passed' in peer['status'] or 'confirmed' in peer['status'];assert peer.get('errors',[])==[]
    assert refs['ledger']['file']=='book/coverage/'+owner+'.json'
    assert offer.get('mapped_ledger',offer.get('module_ledger'))==refs['ledger']['file']
    assert offer.get('mapped_ledger_sha256',offer.get('module_ledger_sha256'))==refs['ledger']['sha256']
    exact(offer['source_sha256'])
    build=checked(refs['actual_builder']);zero(build);assert refs.get('execution_kind')=='actual_guarded_candidate_integration_copy'
    assert build==installation and refs['builder']=={'file':native['actual_helper'],'sha256':native['actual_helper_sha256']}
    assert sha(refs['actual_builder_log']['file'])==refs['actual_builder_log']['sha256']==installation['log_sha256']
    for r in refs.values():
        if isinstance(r,dict) and set(r)=={'file','sha256'}:assert sha(r['file'])==r['sha256'];add(expected_first,r['file'],r['sha256'])
    assert set(offer['proof_files'])==set(refs['expected_owned_proof_sources'])
    for n,row in offer['proof_files'].items():
        assert n not in baseline['proof_files'] and n not in newproofs
        chosen=selected['proof_files'][n];expected=dict(row);assert chosen['original_actual_zero_record'] in row['evidence_sha256']
        expected['original_actual_zero_record']=chosen['original_actual_zero_record'];assert chosen==expected
        rec=read(chosen['original_actual_zero_record']);zero(rec)
        assert rec['source_sha256_before']==rec['source_sha256_after']==row['sha256']
        command=rec.get('command',rec.get('actual_command'));assert command[:3]==['lake','env','lean'] and len(command)==4
        if command[-1]!='SafeLearning/'+Path(n).name:
            assert Path(command[-1]).is_absolute() and rec.get('source_snapshot_sha256',rec.get('preserved_source_sha256'))==row['sha256']
        newproofs[n]=row
    owners[owner]={'offer':refs['offer'],'ledger':refs['ledger'],'mapping_peer':refs['independent_mapping_peer'],'new_sources':len(offer['proof_files'])}
assert len(newproofs)==11 and set(newproofs)==set(plan['expected_new_proof_sources'])
assert set(selected['proof_files'])==set(baseline['proof_files'])|set(newproofs)
assert selected['offers_sha256']=={r['offer']['file']:r['offer']['sha256'] for r in plan['owners'].values()}
assert selected['independent_owner_mapping_peers']=={o:r['independent_mapping_peer'] for o,r in plan['owners'].items()}
extras=dict(baseline['extra_frozen_inputs'])
for n,row in plan['additional_frozen_inputs'].items():
    assert set(row)=={'sha256','scope'} and row['scope']=='immutable_audit_or_local_source_evidence'
    assert path(n).resolve().is_relative_to((R/'book/coverage').resolve()) or path(n).resolve().is_relative_to((R/'reports/full-coverage/source-history').resolve())
    assert Path(n).suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'} or (n in FREEZER_EXCEPTIONS and FREEZER_EXCEPTIONS[n]==row['sha256'])
    assert row['sha256'] not in set(plan['excluded_full_external_reference_sha256']);assert n not in extras or extras[n]==row;extras[n]=row
assert selected['extra_frozen_inputs']==extras
for n,row in extras.items():assert sha(n)==row['sha256'],n
add(expected_first,plan['global_integrity']['file'],plan['global_integrity']['sha256'])
assert content['status']=='all_original_frozen_inputs_retained_by_exact_content_fingerprints'
assert content['baseline_selection']==BASELINE and content['baseline_selection_sha256']==sha(BASELINE)
assert content['baseline_manifest']==MANIFEST and content['baseline_manifest_sha256']==sha(MANIFEST)
assert content['authorized_baseline_owner_evidence_aliases']==authorization
assert content['original_snapshot']==manifest['snapshot'] and content['original_input_count']==44111
maprows=content['input_bindings'];assert len(maprows)==44111 and len({r['original_frozen_path'] for r in maprows})==44111
assert {r['original_frozen_path']:r['sha256'] for r in maprows}==manifest['frozen_inputs_sha256']
for n,h in content['new_unique_snapshot_aliases'].items():assert sha(n)==h;add(expected_first,n,h)
assert content['new_unique_snapshot_alias_count']==len(content['new_unique_snapshot_aliases'])
add(expected_first,MAP,sha(MAP));assert first['evidence_sha256']==expected_first
assert selected['previous_frozen_input_content_binding']=={'file':MAP,'sha256':sha(MAP),'original_inputs':44111,'new_snapshot_aliases':content['new_unique_snapshot_alias_count']}
bound={};all_imports=0
for n,row in selected['proof_files'].items():
    assert sha(n)==row['sha256'];add(bound,n,row['sha256']);exact(row['evidence_sha256'])
    for e,h in row['evidence_sha256'].items():add(bound,e,h)
    source=path(n).read_text();decl=names.declarations(source);all_decl.update(d['name'] for d in decl);public+=sum(d['kind'] in ['theorem','lemma'] for d in decl)
    for line in names.without_comments(source).splitlines():
        if re.match(r'^\s*import\s',line):
            for module in line.split()[1:]:
                if module.startswith('SafeLearning.'):
                    assert 'verification/lean/'+module.replace('.','/')+'.lean' in selected['proof_files'];all_imports+=1
for n,row in extras.items():add(bound,n,row['sha256'])
assert public==9503
for row in maprows:
    assert row['retained_input'] in bound and bound[row['retained_input']]==row['sha256']==sha(row['retained_input'])
    assert sha(manifest['snapshot']+'/'+row['original_frozen_path'])==row['sha256']
for owner,refs in plan['owners'].items():
    ledger=read(refs['ledger']['file'])
    for claim in ledger['material_claims']+[c for e in ledger['exercises'] for c in e['claims']]:assert set(claim['lean_declarations'])<=all_decl,(owner,claim['id'])
    assert sha(refs['ledger']['file'])==refs['ledger']['sha256']
assert sha('book/coverage/applied-promotions.json')==replacements['book/coverage/applied-promotions.json']['candidate']['sha256']
report={'status':'independent_actual_checkpoint26_selection_and_baseline_content_map_confirmation_passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','selection':ref(SELECTION),'selection_plan':ref(plan_name),'actual_selection_execution':ref(ACTUAL),'actual_selection_raw_log':ref(actual['log']),'actual_plan_closure_execution':ref('reports/full-coverage/close-owner26-selection-plan-execution-v1.json'),'original_plan1_entire_body_and_time_reverse_exact':True,'content_map':ref(MAP),'baseline25_selection':ref(BASELINE),'baseline25_manifest':ref(MANIFEST),'inventory':plan['inventory'],'actual_owner26_integration':authorization['actual_integration_execution'],'actual_integration_result':authorization['integration_result'],'global_integrity':plan['global_integrity'],'owners':owners,'proof_files':1167,'new_sources':11,'public_theorem_or_lemma_exports':9503,'old_frozen_paths_retained_exact':44111,'baseline_source_rows_with_exact_four_owner_original_row_provenance':changed_alias_sources,'all_proof_and_evidence_bytes_rehashed':len(bound),'safelearning_imports_resolved':all_imports,'extra_frozen_inputs':len(extras),'all_claim_declarations_selected':True,'freezer':ref(FREEZER),'exact_six_extra_suffix_exceptions':FREEZER_EXCEPTIONS,'all_extra_inputs_eligible_under_checkpoint_specific_freezer':True,'errors':[],'coverage_complete':False,'scope':'Read-only independent actual production output verification. Preserves entire baseline25 row bodies and prior alias provenance, original review/compiler times, exact44111 old frozen bytes plus genuine current installed ledger bytes, Source53 sole Lyapunov revision and current31 assets. Verifies proof/evidence/import/claim closure without implying a fresh frozen26 aggregate/kernel/axiom audit or publication.'}
OUT.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'report':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'proof_files':1167,'exports':9503,'frozen_paths':44111}))
