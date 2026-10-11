"""Read-only independent owner24 preparation code and actual binding review."""
import ast, copy, hashlib, importlib.util, json, re, sys
from datetime import datetime, timezone
from pathlib import Path
R=Path('/home/oxrexkevin/SafetyBased')
HNAME='book/coverage/checks/prepare_root_owner24_bindings_v1.py'
INPUT='book/coverage/checks/root-owner24-binding-preparation-inputs-v1.json'
BINDING='book/coverage/checks/root-owner24-reviewed-candidate-bindings-v1.json'
ACTUAL='reports/full-coverage/prepare-owner24-bindings-execution-v1.json'
OUT=Path('/tmp/owner24-binding-independent-modules-confirmation-v1.json')
EXPECTED={'core':1,'foundations':5,'applied':4,'modules':3}
CACHE={}
def digest(name):
    p=Path(name); p=p if p.is_absolute() else R/p
    return hashlib.sha256(p.read_bytes()).hexdigest()
def sha(name):
    if name not in CACHE: CACHE[name]=digest(name)
    return CACHE[name]
def read(name): return json.loads((R/name).read_text())
def ref(name): return {'file':name,'sha256':sha(name)}
def checked(row):
    assert isinstance(row,dict) and set(row)=={'file','sha256'}
    assert sha(row['file'])==row['sha256'],row
    return read(row['file'])
def pointer(body,path):
    for key in path: body=body[key]
    return body
def agree(body,names):
    values=[body[n] for n in names if n in body]
    assert values and len({json.dumps(v,sort_keys=True) for v in values})==1,names
    return values[0]
def zero(body):
    values=[body[n] for n in ['actual_exit_code','exit_code'] if n in body]
    assert values and all(type(v)==int and v==0 for v in values)
def reject(label,fn):
    try: fn()
    except (AssertionError,ValueError): fixtures.append(label); return
    raise AssertionError('Fixture unexpectedly accepted '+label)
def independent_pair(source,proof):
    digest=proof['sha256']; assert sha(source)==digest
    evidence=proof['evidence_sha256']
    for n,h in evidence.items(): assert sha(n)==h,n
    canonical_input=source.removeprefix('verification/lean/')
    commands=[['lake','env','lean',canonical_input],['lake','build','SafeLearning.'+Path(source).stem]]
    found=[]
    for command in commands:
        eligible=[]
        for n,h in evidence.items():
            if not n.endswith('.json'): continue
            row=read(n)
            if not isinstance(row,dict) or row.get('source')!=source: continue
            if row.get('source_sha256_before')!=digest or row.get('source_sha256_after')!=digest: continue
            if not any(k in row for k in ('command','actual_command')): continue
            actual_command=agree(row,['command','actual_command'])
            if actual_command!=command: continue
            zero(row); assert row.get('source_unchanged',True) is True
            assert row['actual_workdir']==str(R/'verification/lean')
            logsha=agree(row,['log_sha256','raw_log_sha256'])
            raw=[row[k] for k in ['log','raw_log'] if k in row]
            assert raw
            logs=sorted(k for k,v in evidence.items() if k.endswith('.log') and v==logsha)
            assert logs
            for log in raw:
                assert isinstance(log,str)
                if not Path(log).is_absolute(): assert sha(log)==logsha
            if any(k in row for k in ['source_snapshot_sha256','preserved_source_sha256']):
                snapshotsha=agree(row,['source_snapshot_sha256','preserved_source_sha256'])
                assert snapshotsha==digest
                assert any(k.endswith('.lean') and v==digest for k,v in evidence.items())
                for k in ['source_snapshot','preserved_source']:
                    if k in row and not Path(row[k]).is_absolute(): assert sha(row[k])==digest
            preferred=next((n for n in raw if n in logs),logs[0])
            eligible.append({'file':n,'sha256':h,'actual_source':source,'actual_command':command,
                             'actual_workdir':str(R/'verification/lean'),
                             'canonical_raw_log':{'file':preferred,'sha256':logsha}})
        assert len(eligible)==1,(source,command,len(eligible))
        found.extend(eligible)
    return {'sha256':digest,'actual_pair':found}

assert not OUT.exists()
assert sha(HNAME)=='8882c9cfca0e7f3a00299dd590186d95c782428954d0520181c66666ce695fac'
assert sha(INPUT)=='cc9655bc38794a734333c50021a416cf3f08417fcc3db2c1296cf70e56dc3e53'
assert sha(BINDING)=='3d2693f3db4dfb5bd6ba2848fba62f434812d606595d6a102fc2d790c137b3ae'
spec=importlib.util.spec_from_file_location('binding24_reviewed',R/HNAME)
helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
tree=ast.parse((R/HNAME).read_text())
assert not any(isinstance(n,(ast.Import,ast.ImportFrom)) and any(a.name in ['subprocess','shutil'] for a in n.names) for n in ast.walk(tree))
opens=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='open']
assert len(opens)==1 and isinstance(opens[0].args[0],ast.Constant) and opens[0].args[0].value=='x'
fixtures=[]
for bad in ['', '/tmp/x','../x','book/../x','book//coverage/x']:
    reject('noncanonical_path_'+repr(bad),lambda bad=bad:helper.safe(bad))
reject('conflicting_command_alias',lambda:helper.alias({'command':['a'],'actual_command':['b']},('command','actual_command')))
reject('conflicting_log_alias',lambda:helper.alias({'log_sha256':'a','raw_log_sha256':'b'},('log_sha256','raw_log_sha256')))
for body in [{'actual_exit_code':False},{'actual_exit_code':0,'exit_code':1},{}]:
    reject('not_genuine_integer_zero_'+str(body),lambda body=body:helper.zero(body))
assert helper.alias({'actual_command':['lake']},('command','actual_command'))==['lake']; fixtures.append('native_actual_command_accepted')
helper.zero({'exit_code':0});fixtures.append('native_exit_code_accepted')
helper.zero({'exit_code':0,'actual_exit_code':0});fixtures.append('matching_exit_aliases_accepted')

inputs=read(INPUT);binding=read(BINDING);actual=read(ACTUAL)
assert inputs['destination']==BINDING and set(inputs['offers'])==set(EXPECTED)
zero(actual);assert actual['status']=='passed'
assert actual['actual_command']==['python3',HNAME,'--input',INPUT,'--input-sha256',sha(INPUT),'--root-authorized-binding-preparation']
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={HNAME:sha(HNAME)}
assert sha(actual['log'])==actual['log_sha256']
assert binding['status']=='all_four_reviewed_current52_owner_candidates_bound_ready_for_root_execution'
assert binding['preparation_helper']==ref(HNAME) and binding['preparation_input']==ref(INPUT)
assert binding['coverage_complete'] is False and binding['inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
baseline=checked(binding['baseline23_manifest'])
assert len(baseline['proof_files'])==1131 and len(baseline['frozen_inputs_sha256'])==36910
assert sha(baseline['selection'])==baseline['selection_sha256']
assert sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction52.json')==binding['inventory_sha256']
for n,h in binding['exact_current52_safelearning_assets_sha256'].items(): assert sha(n)==h,n
assert len(binding['exact_current52_safelearning_assets_sha256'])==31
for row in [binding['actual_source52_apply'],binding['actual_source52_postwrite']]: zero(checked(row))
assert checked(binding['actual_source52_postwrite'])['inventory_after_sha256']==binding['inventory_sha256']
assert sha('book/coverage/material-corrections.json')==binding['source52_corrections_sha256']
names=importlib.util.spec_from_file_location('lean_names_independent_review',R/'book/coverage/lean_names.py')
index=importlib.util.module_from_spec(names);names.loader.exec_module(index)
owner_findings={};new_sources={};new_public=[];canonical_records=set();semantic_hashes={}
for owner in sorted(EXPECTED):
    row=binding['owners'][owner];offer=checked(inputs['offers'][owner]);candidate=checked(row['candidate_ledger']);peer=checked(row['independent_candidate_mapping_peer'])
    assert row['reviewed_final_offer']==inputs['offers'][owner]
    assert row['ready'] is True and 'passed' in peer['status'] and peer.get('errors',[])==[]
    assert pointer(offer,row['offer_candidate_path_pointer'])==row['candidate_ledger']['file']
    assert pointer(offer,row['offer_candidate_sha256_pointer'])==row['candidate_ledger']['sha256']
    assert pointer(peer,row['peer_candidate_path_pointer'])==row['candidate_ledger']['file']
    assert pointer(peer,row['peer_candidate_sha256_pointer'])==row['candidate_ledger']['sha256']
    assert row['held23_ledger']=='book/coverage/'+owner+'.json'
    assert sha(row['held23_ledger'])==row['held23_ledger_sha256']==baseline['working_inputs_sha256'][row['held23_ledger']]
    build=checked(row['actual_candidate_builder']);zero(build)
    log=agree(build,['log','raw_log']);logsha=agree(build,['log_sha256','raw_log_sha256']);assert sha(log)==logsha
    if owner=='core': assert row['actual_candidate_builder']==peer['actual_identity_execution']['actual_record']
    if owner=='foundations': assert row['actual_candidate_builder']=={'file':offer['actual_builder_record'],'sha256':offer['actual_builder_record_sha256']}
    if owner=='applied': assert row['actual_candidate_builder']==offer['actual_isolated_candidate_preparation']
    if owner=='modules': assert row['actual_candidate_builder']=={k:offer['actual_builder'][k] for k in ['file','sha256']}
    if owner=='core': semantic_refs=offer['whole_source_reviews']
    elif owner=='foundations': semantic_refs=[{'file':n,'sha256':h} for n,h in offer['exact_source_reviews_sha256'].items()]
    else:
        key='original_independent_review_references' if owner=='applied' else 'original_full_or_precise_source_reviews'
        semantic_refs=[{k:r[k] for k in ['file','sha256']} for r in offer[key]]
    expected_semantics=[]
    for semantic_ref in semantic_refs:
        original=checked(semantic_ref);assert original.get('errors',[])==[]
        time=original.get('reviewed_at_utc',original.get('checked_at_utc'));assert time is not None
        expected_semantics.append(dict(semantic_ref,original_review_status=original['status'],original_review_time=time))
        semantic_hashes[semantic_ref['file']]=semantic_ref['sha256']
    assert row['original_full_source_semantic_reviews']==expected_semantics
    assert len(offer['proof_files'])==EXPECTED[owner]
    normalized={};evidence={}
    for key in ['required_evidence_artifacts_sha256','required_live_integration_evidence_sha256','canonical_readiness_sha256','canonical_source_peer_bindings_sha256','actual_canonical_execution_records_sha256']:
        for n,h in offer.get(key,{}).items(): assert n not in evidence or evidence[n]==h;evidence[n]=h
    public=[]
    for source,proof in offer['proof_files'].items():
        assert source not in baseline['proof_files'] and source not in new_sources
        normalized[source]=independent_pair(source,proof)
        assert normalized[source]==helper.canonical_pair(source,proof)
        new_sources[source]=proof['sha256']
        declarations=index.declarations((R/source).read_text())
        public.extend(d['name'] for d in declarations if d['kind'] in ['theorem','lemma'])
        for rec in normalized[source]['actual_pair']: assert rec['file'] not in canonical_records;canonical_records.add(rec['file'])
        for n,h in proof['evidence_sha256'].items(): assert n not in evidence or evidence[n]==h;evidence[n]=h
        bad=copy.deepcopy(proof);bad['sha256']='0'*64
        reject('wrong_source_digest_'+source,lambda bad=bad,source=source:helper.canonical_pair(source,bad))
    assert row['new_immutable_proof_sources']==normalized
    for extra in inputs['extra_closed_evidence'][owner]: assert sha(extra['file'])==extra['sha256'];evidence[extra['file']]=extra['sha256']
    evidence[row['actual_candidate_builder']['file']]=row['actual_candidate_builder']['sha256'];evidence[log]=logsha
    assert row['additional_exact_provenance']==[{'file':n,'sha256':h} for n,h in sorted(evidence.items())]
    for n,h in evidence.items(): assert sha(n)==h,n
    for n,h in candidate['source_sha256'].items(): assert sha(n)==h
    if owner=='applied':
        assert len(row['companion_candidates'])==1
        cp=row['companion_candidates'][0];assert cp['held23_asset']=='book/coverage/applied-promotions.json'
        assert cp['held23_asset_sha256']==sha(cp['held23_asset'])==baseline['working_inputs_sha256'][cp['held23_asset']]
        assert cp['candidate']=={'file':offer['mapped_promotions'],'sha256':offer['mapped_promotions_sha256']};checked(cp['candidate'])
    else: assert row['companion_candidates']==[]
    new_public.extend(public)
    owner_findings[owner]={'candidate':row['candidate_ledger'],'offer':row['reviewed_final_offer'],'peer':row['independent_candidate_mapping_peer'],'new_sources':len(normalized),'public_theorem_or_lemma_exports':len(public),'canonical_actual_records':2*len(normalized),'original_semantic_review_refs_and_times_exact':len(expected_semantics),'closed_provenance_files':len(evidence)}
assert len(new_sources)==binding['new_proof_sources']==13 and len(canonical_records)==binding['original_canonical_execution_records']==26
assert len(new_public)==86 and len(set(new_public))==86
all_sources={n:p['sha256'] for n,p in baseline['proof_files'].items()}|new_sources
all_public=0;imports_checked=0
for source,h in all_sources.items():
    assert sha(source)==h
    text=(R/source).read_text();decls=index.declarations(text)
    all_public+=sum(d['kind'] in ['theorem','lemma'] for d in decls)
    for line in index.without_comments(text).splitlines():
        if re.match(r'^\s*import\s',line):
            for module in line.split()[1:]:
                if module.startswith('SafeLearning.'):
                    path='verification/lean/'+module.replace('.','/')+'.lean'
                    assert path in all_sources,(source,path);imports_checked+=1
assert len(all_sources)==1144 and all_public==9279
snapshot=R/baseline['snapshot']
for n,h in baseline['frozen_inputs_sha256'].items(): assert digest(snapshot/n)==h,n
assert sha(BINDING)=='3d2693f3db4dfb5bd6ba2848fba62f434812d606595d6a102fc2d790c137b3ae'
for owner,row in binding['owners'].items(): assert digest(row['held23_ledger'])==row['held23_ledger_sha256']
report={'status':'independent_owner24_binding_helper_and_actual_output_mechanical_confirmation_passed','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'binding_manifest':ref(BINDING),'preparation_helper':ref(HNAME),'preparation_input':ref(INPUT),'actual_binding_preparation':ref(ACTUAL),'actual_preparation_raw_log':ref(actual['log']),'baseline23_manifest':binding['baseline23_manifest'],'immutable_inventory_after':ref('book/coverage/inventory-after-correction52.json'),'owners':owner_findings,'new_sources':13,'original_canonical_actual_records':26,'new_public_theorem_or_lemma_exports':86,'expected_selection_sources':1144,'expected_public_theorem_or_lemma_exports':9279,'safelearning_imports_resolved':imports_checked,'baseline_frozen_inputs_rehashed':36910,'independent_accept_reject_fixtures':fixtures,'all_original_semantic_review_file_bytes_statuses_times_exact':semantic_hashes,'errors':[],'coverage_complete':False,'scope':'Read-only independent code/schema and actual prepared-output review. Exact source/canonical compiler/log/provenance bytes, full original semantic review references/status/time, candidate peers and old held assets checked. No live install, candidate builder rerun, Lean compilation, global24, production selection, kernel replay or publication is claimed.'}
OUT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'report':str(OUT),'sha256':digest(OUT),'new_sources':13,'canonical_actual_records':26,'public_exports':86,'expected_files':1144,'expected_public_exports':9279,'fixtures':len(fixtures)}))
