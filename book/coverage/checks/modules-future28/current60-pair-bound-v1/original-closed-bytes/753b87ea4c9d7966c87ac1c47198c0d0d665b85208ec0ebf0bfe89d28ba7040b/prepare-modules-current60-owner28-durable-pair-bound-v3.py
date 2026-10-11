from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re,collections

R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1'
V2=Path('/tmp/modules-current60-owner28-candidate-v2/modules-current60-owner28-five-proof-pending-canonical-pairs.json')
MECH=Path('/tmp/modules28-current60-pending-candidate-independent-applied-confirmation-final-v1.json')
OLD_OFFER=R/'book/coverage/checks/modules-future27/source55/modules-audit27-candidate-current55-additions-v1-reviewed.json'
PRIOR=R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json'
COMMISSION=R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json'
CAND=B/'modules28-current60-five-source-pair-bound-candidate-v1.json'
OFFER=B/'modules28-current60-five-source-pair-bound-offer-draft-v1.json'
REPORT=B/'modules28-current60-pair-binding-preparation-v1.json'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def P(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':H(p)}
def zero(d):
    codes=[v for k,v in d.items()if k in ('actual_exit_code','exit_code','actual_runner_exit_code')]
    assert codes and all(type(x)is int and x==0 for x in codes)
def checkref(v):
    p=P(v['file']);assert p.is_file()and H(p)==v['sha256'];return p
def put(p,raw):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb')as f:f.write(raw)
def putj(p,d):put(p,(json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
assert not B.exists()
assert H(V2)=='e1d7dc6ecbd108df97d891852c2bb64d1913c563e4cdf5c1656d921fb1e01c5a'
assert H(MECH)=='8cb12668342b75bbe32ca5bf9b0e96a27b579b508e3638ae18ce23657f88c89a'
assert H(PRIOR)=='209f306bc9c9b70b51a4eca063f453d546353bd9860ac3a96c6a3e4e037cc453'
assert H(COMMISSION)=='d8d913167cf4bc803f6d8c5808d62350d216f70bb95a171ab1993f43313121be'
assert H(OLD_OFFER)=='2f69bcf130c058877083d863e5ed2c4243f95c226f012e6bed44ae33be692530'
assert H(R/'book/coverage/modules.json')=='7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487'
assert H(R/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
old=J(R/'book/coverage/modules.json');v2=J(V2);mech=J(MECH);o=J(OLD_OFFER)
assert mech['status']=='passed_independent_isolated_modules28_current60_pending_pair_candidate_mechanics'and mech['errors']==[]
assert mech['candidate']=={'file':str(V2),'sha256':H(V2)}
prior=J(PRIOR);commission=J(COMMISSION)
assert prior['source_count']==10 and prior['actual_compiler_command_count']==20 and prior['errors']==[]
assert commission['source_count']==1 and commission['actual_compiler_command_count']==2 and commission['errors']==[]
inherited=dict(o['required_evidence_artifacts_sha256']);assert len(inherited)==383
for n,h in inherited.items():assert not Path(n).is_absolute()and H(R/n)==h,n

# Pin every retained baseline source/page/owner plus all11 newly compiled sources and22 native pairs.
selection=J(R/'reports/full-coverage/checkpoint-27-selection.json')
held={R/n:r['sha256']for n,r in selection['proof_files'].items()};assert len(held)==1175
held.update({p:H(p)for p in (R/'SafeLearning').glob('*')if p.is_file()})
held.update({R/'book/coverage'/n:H(R/'book/coverage'/n)for n in ('modules.json','core.json','foundations.json','applied.json','applied-promotions.json','inventory.json','material-corrections.json')})
held[R/'reports/full-coverage/checkpoint-27-selection.json']=H(R/'reports/full-coverage/checkpoint-27-selection.json')
held[Path(__file__)]=H(Path(__file__))
for readiness in (prior,commission):
    for row in readiness['sources']:held[R/row['canonical_source']]=row['original_tmp_source']['sha256']
    for pair in readiness['actual_paired_records']:
        for field in ('actual_record','raw_log','source_snapshot'):
            p=checkref(pair[field]);held[p]=H(p)
def guard():
    for p,h in held.items():assert H(p)==h,str(p)
guard()

# Resolve and retain all new original evidence as exact files, never recursively embedding histories.
refs={};queue=[];scan_seen=set();existing_aliases={};historical_resolutions=[]
for readiness in (prior,commission):existing_aliases.update(readiness['original_closed_byte_aliases'])
historical=R/'reports/full-coverage/source-history/approved-corrections56-60-20261011/source55-original-root'
def resolve(n,h):
    p=P(n)
    if p.is_file()and H(p)==h:return p
    candidates=[]
    if p.is_relative_to(R):candidates.append(historical/p.relative_to(R))
    candidates.extend(R/k for k,v in inherited.items()if v==h)
    if str(p)in existing_aliases and existing_aliases[str(p)]['sha256']==h:candidates.append(P(existing_aliases[str(p)]['file']))
    for candidate in candidates:
        if candidate.is_file()and H(candidate)==h:
            historical_resolutions.append({'original_historical_file':str(p),'historical_sha256':h,'exact_archive':ref(candidate),'reason':'Original historical body retained; this archive does not assert current60 identity.'})
            return candidate
    raise AssertionError(('missing exact historical evidence',n,h))
def register(n,h,scan=True):
    p=resolve(n,h)
    normalized=str(p)
    if normalized in refs:assert refs[normalized]==h;return
    refs[normalized]=h
    if scan and p.suffix=='.json'and p!=V2 and p.name!='material-corrections.json'and p.stat().st_size<10_000_000:queue.append(p)
def discover(v):
    if isinstance(v,dict):
        if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str)and re.fullmatch('[0-9a-f]{64}',v['sha256']):register(v['file'],v['sha256'])
        for k,x in v.items():
            if isinstance(x,str)and re.fullmatch('[0-9a-f]{64}',x)and ('/'in k)and not k.startswith(('http:','https:')):
                p=P(k)
                if p.is_file():register(k,x)
            discover(x)
    elif isinstance(v,list):
        for x in v:discover(x)
seeds=[Path(__file__),V2,MECH,PRIOR,COMMISSION,Path('/tmp/modules-current60-owner28-candidate-v2/modules-current60-owner28-candidate-preparation-v2.json'),Path('/tmp/modules-current60-owner28-candidate-preparation-actual-v2.json'),Path('/tmp/modules-current60-owner28-candidate-preparation-actual-v1.json'),Path('/tmp/modules-owner28-approved-scope-plan-v1.json'),Path('/tmp/root28-commissioning17-executor-independent-modules28-closed-v1.json'),R/'reports/full-coverage/current60-canonical-pairs28-execution-v1.json',R/'reports/full-coverage/current60-commissioning17-canonical-pair28-execution-v1.json']
for p in seeds:register(str(p),H(p))
for field in ('source60_literal_identity','inventory_identity_rebase60'):
    if field in v2:discover(v2[field])
for e in v2['exercises']:
    if 'entire_literal_closure28'in e:discover(e['entire_literal_closure28'])
    discover(e['source60_literal_identity'])
    for c in e['claims']:
        for key in ('independent_source_review','reviewed_owner28_transition'):
            if key in c and 'reviewed_owner28_transition'in c:discover(c[key])
for c in v2['material_claims']:
    discover(c['source60_literal_identity'])
    for key in ('independent_source_review','reviewed_owner28_transition'):
        if key in c and 'reviewed_owner28_transition'in c:discover(c[key])
for n in set(v2['proof_files'])-set(old['proof_files']):discover(v2['proof_files'][n])
while queue:
    p=queue.pop()
    if str(p)in scan_seen:continue
    scan_seen.add(str(p));discover(J(p))
guard();B.mkdir(parents=True)
aliases={};required=dict(inherited)
for n,h in refs.items():
    p=Path(n)
    if p.is_relative_to(R):r={'file':p.relative_to(R).as_posix(),'sha256':h}
    elif n in existing_aliases and checkref(existing_aliases[n]):r=existing_aliases[n]
    else:
        target=B/'original-closed-bytes'/h/p.name
        if target.exists():assert H(target)==h
        else:put(target,p.read_bytes())
        r=ref(target)
    aliases[n]=r
    assert r['file']not in required or required[r['file']]==h
    required[r['file']]=h
required[ref(OLD_OFFER)['file']]=H(OLD_OFFER)
def durable(v):
    if isinstance(v,dict):
        if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str)and re.fullmatch('[0-9a-f]{64}',v['sha256']):
            p=resolve(v['file'],v['sha256']);return {**v,'file':aliases.get(str(p),ref(p)if p.is_relative_to(R)else{})['file']}
        return {k:durable(x)for k,x in v.items()}
    if isinstance(v,list):return[durable(x)for x in v]
    return v

out=copy.deepcopy(v2);original_new_fields=[]
# Only new28 typed references are rebound. All installed27 bodies/history/metadata remain exact.
def transform_added(before,after,path):
    if isinstance(after,dict):
        for k in list(after):
            if not isinstance(before,dict)or k not in before:
                transformed=durable(after[k])
                if transformed!=after[k]:original_new_fields.append({'path':path+[k],'original_v2_value':after[k]});after[k]=transformed
            else:transform_added(before[k],after[k],path+[k])
    elif isinstance(after,list)and isinstance(before,list)and len(after)==len(before):
        for i,(x,y)in enumerate(zip(before,after)):transform_added(x,y,path+[i])
transform_added(old,out,[])
newkeys=set(out['proof_files'])-set(old['proof_files']);assert len(newkeys)==5
proofs={};pairrows=prior['actual_paired_records']+commission['actual_paired_records']
rows=prior['sources']+commission['sources'];by_source={r['canonical_source']:r for r in rows}
for n in sorted(newkeys):
    meta=out['proof_files'][n];source=R/n;row=by_source[n];names=meta['declarations']
    assert H(source)==meta['sha256']==row['original_tmp_source']['sha256']and names==row['public_declarations']
    pairs={p['kind']:p for p in pairrows if p['source']['file']==n};assert set(pairs)=={'standalone','named'}
    native={}
    for kind,pair in pairs.items():
        zero(pair);record=J(checkref(pair['actual_record']));zero(record)
        assert record['source']==n and record['source_sha256_before']==record['source_sha256_after']==H(source)
        expected=['lake','env','lean','SafeLearning/'+source.name]if kind=='standalone'else['lake','build','SafeLearning.'+source.stem]
        assert record['command']==expected and record['actual_workdir']==str(R/'verification/lean')
        assert H(checkref(pair['source_snapshot']))==H(source)and H(checkref(pair['raw_log']))==record['log_sha256']
        native[kind]=record
    meta.pop('canonical_paired_evidence_not_yet_available');meta['standalone_compile_status']='passed_source_matched_actual_canonical_pair'
    meta['standalone_compile_evidence']={'file':n,'sha256':H(source),'exit_code':0,'log':native['standalone']['log'],'log_sha256':native['standalone']['log_sha256'],'source_unchanged':True,'actual_record':pairs['standalone']['actual_record']}
    meta['actual_pair']={'standalone':pairs['standalone'],'named':pairs['named']}
    meta['evidence_sha256']=pairs['standalone']['actual_record']['sha256']
    meta['canonical_pair_evidence_directory_assigned_by_root']=str((R/pairs['standalone']['source_snapshot']['file']).parent.parent.relative_to(R))+'/'
    proofs[n]={'sha256':H(source),'evidence_sha256':pairs['standalone']['actual_record']['sha256'],'theorem_count':len(names),'public_theorem_names':names,'mapped_named_declarations':names,'actual_pair':meta['actual_pair'],'declarations':names,'standalone_compile_status':meta['standalone_compile_status'],'standalone_compile_evidence':meta['standalone_compile_evidence'],'original_tmp_source':meta['original_tmp_source'],'original_tmp_trial':meta['original_tmp_trial'],'independent_whole_scope_peer':durable(row['independent_whole_scope_peer'])}
assert sum(x['theorem_count']for x in proofs.values())==153
assert all(out['proof_files'][n]==v for n,v in old['proof_files'].items())and out['declarations'][:len(old['declarations'])]==old['declarations']
transitions=[]
for e in out['exercises']:
    if 'entire_literal_closure28'in e:
        e['entire_literal_closure28']['canonical_pair_and_owner_integration_pending']=False
        e['entire_literal_closure28']['canonical_pairs_available_owner_integration_pending']=True
    for c in e['claims']:
        if 'reviewed_owner28_transition'in c and c['reviewed_owner28_transition'].get('canonical_pair_pending')is True:c['reviewed_owner28_transition']['canonical_pair_pending']=False
for c in out['material_claims']:
    if 'reviewed_owner28_transition'in c and c['reviewed_owner28_transition'].get('canonical_pair_pending')is True:c['reviewed_owner28_transition']['canonical_pair_pending']=False
out['status']='reviewed_current60_owner28_five_source_actual_pair_candidate_pending_root_owner_integration'
out['generated_at_utc']=datetime.now(timezone.utc).isoformat()
out['actual_current60_pair_binding28']={'status':'passed_actual_five_source153_declaration_pair_binding_pending_independent_mapping_and_owner_integration','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_pending_v2_candidate':aliases[str(V2)],'original_pending_v2_full_mapping_peer':aliases[str(MECH)],'original_installed27_owner':ref(R/'reports/full-coverage/checkpoint-27/book/coverage/modules.json'),'ten_source_readiness':ref(PRIOR),'commissioning17_readiness':ref(COMMISSION),'five_new_sources':sorted(newkeys),'public_declaration_count':153,'whole_exercises':4,'whole_material_units':26,'original_math_peer_body_or_time_reinterpreted':False,'owner_integrated':False,'coverage_complete':False}
putj(CAND,out);required[ref(CAND)['file']]=H(CAND)
manifest=B/'modules28-original-new-reference-rebinding-manifest-v1.json';putj(manifest,{'status':'exact_new28_reference_rebinding_manifest','original_v2_candidate':aliases[str(V2)],'installed27_owner':ref(R/'book/coverage/modules.json'),'changed_new_reference_fields':original_new_fields,'original_closed_byte_aliases':aliases,'original_historical_context_exact_archive_resolutions':historical_resolutions,'scope':'Only added28 typed evidence refs become durable. Raw original candidate and full semantic/read body/time artifacts remain exact byte snapshots.'});required[ref(manifest)['file']]=H(manifest)
offer={'status':'prepared_current60_modules28_five_source_actual_pair_offer_awaiting_independent_final_mapping','errors':[],'candidate':ref(CAND),'candidate_builder':aliases[str(Path(__file__))]if str(Path(__file__))in aliases else None,'inventory':ref(R/'book/coverage/inventory-after-correction60.json'),'inventory_sha256':H(R/'book/coverage/inventory-after-correction60.json'),'base_selection':ref(R/'reports/full-coverage/checkpoint-27-selection.json'),'source_sha256':out['source_sha256'],'proof_files':proofs,'counts':out['counts'],'original_installed27_reviewed_offer':ref(OLD_OFFER),'original_pending_v2_candidate':aliases[str(V2)],'original_pending_v2_independent_mapping_peer':aliases[str(MECH)],'durable_new_reference_manifest':ref(manifest),'actual_ten_source_canonical_readiness':ref(PRIOR),'actual_commissioning17_canonical_readiness':ref(COMMISSION),'whole_exercise_keys':[e['inventory_key']for e in out['exercises']if 'entire_literal_closure28'in e],'whole_material_keys':[c['source_unit_keys'][0]for c in out['material_claims']if c.get('whole_current60_source_unit_approved')is True],'whole976_approved':False,'required_evidence_artifacts_sha256':required,'original_closed_byte_aliases':aliases,'final_independent_candidate_mapping_peer':None,'actual_isolated_candidate_preparation':None,'coverage_complete':False,'scope':'Five exact reviewed sources153 public declarations, four whole exercises26 units with genuine canonical standalone/named pairs. All installed27 proof metadata/declaration prefix/history retained. Current60 source identities explicit, original full math/read times preserved. Root owner installation, selection and aggregate audit remain separate.'}
assert len(offer['whole_exercise_keys'])==4 and len(offer['whole_material_keys'])==26
putj(OFFER,offer)
report={'status':'passed_actual_modules28_current60_durable_pair_bound_preparation_awaiting_independent_mapping','errors':[],'candidate':ref(CAND),'offer':ref(OFFER),'manifest':ref(manifest),'counts':out['counts'],'new_source_count':5,'new_public_theorem_count':153,'whole_exercises':4,'whole_material_units':26,'required_durable_evidence_count':len(required),'original_closed_alias_count':len(aliases),'old_proof_metadata_and_declarations_exact':True,'whole976_approved':False,'live_owner_or_selection_or_publication_written':False,'coverage_complete':False}
putj(REPORT,report);guard();print(json.dumps({'report':ref(REPORT),'offer':ref(OFFER),'candidate':ref(CAND),'closed_refs':len(required),'aliases':len(aliases)}))
