from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re

R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1'
O=B/'modules28-current60-five-source-pair-bound-offer-draft-v5.json'
C=B/'modules28-current60-five-source-pair-bound-candidate-v1.json'
OUT=Path('/tmp/modules28-current60-final-pair-bound-independent-applied-findings-v5.json')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def P(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):return {'file':str(p),'sha256':H(p)}
def checked(r):
    assert isinstance(r,dict) and isinstance(r.get('file'),str) and re.fullmatch('[0-9a-f]{64}',r['sha256'])
    p=P(r['file']);assert p.is_file() and H(p)==r['sha256'],r
    if 'bytes' in r:assert p.stat().st_size==r['bytes']
    return p
def rooted(n):
    p=Path(n);assert not p.is_absolute() and '..' not in p.parts and p.as_posix()==n
    p=R/p;assert p.resolve().is_relative_to(R) and not p.is_symlink()
    return p
def zero(d):
    exits=[d[k] for k in ('exit_code','actual_exit_code','actual_runner_exit_code') if k in d]
    assert exits and all(type(x)is int and x==0 for x in exits)
def eq(a,b,label):assert a==b,label
assert not OUT.exists()
assert H(O)=='e59929813701ed182418e8d4ae34210f4f45b4dee3a00bac8f64ff456d372996'
assert H(C)=='2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715'
offer=J(O);candidate=J(C);old=J(R/'book/coverage/modules.json')
original2=J(B/'modules28-current60-five-source-pair-bound-offer-draft-v2.json')
original3=J(B/'modules28-current60-five-source-pair-bound-offer-draft-v3.json')
original4=J(B/'modules28-current60-five-source-pair-bound-offer-draft-v4.json')
assert set(offer)==set(original4) and offer['required_evidence_artifacts_sha256']==original4['required_evidence_artifacts_sha256']
changed_aliases=[n for n,v in original4['original_closed_byte_aliases'].items() if offer['original_closed_byte_aliases'][n]!=v]
assert len(changed_aliases)==11
four_inverse=copy.deepcopy(offer)
for n in changed_aliases:
    assert n.startswith(str(R/'verification/lean/.lake/packages/mathlib')+'/')
    rel=str(Path(n).relative_to(R))
    eq(offer['original_closed_byte_aliases'][n],offer['original_closed_byte_aliases'][rel],'absolute/relative original exact same retained primary byte alias')
    four_inverse['original_closed_byte_aliases'][n]=original4['original_closed_byte_aliases'][n]
eq(four_inverse,original4,'ENTIRE outer offer5 inverse restores original offer4')
removed=set(original3['required_evidence_artifacts_sha256'])-set(offer['required_evidence_artifacts_sha256'])
added=set(offer['required_evidence_artifacts_sha256'])-set(original3['required_evidence_artifacts_sha256'])
assert len(removed)==len(added)==11 and all(n.startswith('verification/lean/.lake/packages/mathlib/')for n in removed)
newaliases=set(offer['original_closed_byte_aliases'])-set(original3['original_closed_byte_aliases'])
assert newaliases==removed
outer_inverse=copy.deepcopy(four_inverse)
for n in removed:
    r=offer['original_closed_byte_aliases'][n]
    assert r['file']in added and r['sha256']==original3['required_evidence_artifacts_sha256'][n]
    assert H(rooted(r['file']))==r['sha256']==H(R/n)
    outer_inverse['original_closed_byte_aliases'].pop(n)
for n in added:outer_inverse['required_evidence_artifacts_sha256'].pop(n)
for n in removed:outer_inverse['required_evidence_artifacts_sha256'][n]=original3['required_evidence_artifacts_sha256'][n]
eq(outer_inverse,original3,'ENTIRE outer offer4 inverse restores original offer3')
closure_added=set(original3['required_evidence_artifacts_sha256'])-set(original2['required_evidence_artifacts_sha256'])
assert len(closure_added)==5
for n in closure_added:outer_inverse['required_evidence_artifacts_sha256'].pop(n)
eq(outer_inverse,original2,'ENTIRE outer offer3 inverse restores original offer2')
assert H(R/'book/coverage/modules.json')=='7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487'
assert offer['errors']==[] and offer['coverage_complete']is False and offer['whole976_approved']is False
eq(offer['candidate'],{'file':C.relative_to(R).as_posix(),'sha256':H(C)},'exact candidate pointer')
base=J(checked(offer['original_pending_v2_candidate']));priorpeer=J(checked(offer['original_pending_v2_independent_mapping_peer']))
assert priorpeer['status']=='passed_independent_isolated_modules28_current60_pending_pair_candidate_mechanics' and priorpeer['errors']==[]
assert priorpeer['candidate']['sha256']==H(checked(offer['original_pending_v2_candidate']))
manifest=J(checked(offer['durable_new_reference_manifest']))
aliases=manifest['original_closed_byte_aliases']
historical={(x['original_historical_file'],x['historical_sha256']):x['exact_archive'] for x in manifest['original_historical_context_exact_archive_resolutions']}
for (_,h),r in historical.items():assert r['sha256']==h;checked(r)
def durable(v):
    if isinstance(v,dict):
        if isinstance(v.get('file'),str) and isinstance(v.get('sha256'),str) and re.fullmatch('[0-9a-f]{64}',v['sha256']):
            n=str(P(v['file']));h=v['sha256'];r=aliases.get(n)
            if r is None:
                hist=historical.get((n,h))
                if hist is not None:r=aliases.get(str(P(hist['file'])),hist)
            assert r is not None and r['sha256']==h,(n,h)
            checked(r);return {**v,'file':r['file']}
        return {k:durable(x) for k,x in v.items()}
    if isinstance(v,list):return [durable(x) for x in v]
    return v
computed_paths=[]
def normalize_added(before,after,path):
    if isinstance(after,dict):
        for k in list(after):
            if not isinstance(before,dict) or k not in before:
                x=durable(after[k])
                if x!=after[k]:computed_paths.append({'path':path+[k],'original_v2_value':copy.deepcopy(after[k])});after[k]=x
            else:normalize_added(before[k],after[k],path+[k])
    elif isinstance(after,list) and isinstance(before,list) and len(after)==len(before):
        for i,(x,y) in enumerate(zip(before,after)):normalize_added(x,y,path+[i])
expected=copy.deepcopy(base);normalize_added(old,expected,[])
eq(computed_paths,manifest['changed_new_reference_fields'],'independently derived exact new-reference manifest')
readiness=[J(checked(offer[k])) for k in ('actual_ten_source_canonical_readiness','actual_commissioning17_canonical_readiness')]
rows={r['canonical_source']:r for d in readiness for r in d['sources']}
pairs=[p for d in readiness for p in d['actual_paired_records']]
assert len(rows)==11 and len(pairs)==22 and sum(d['public_theorem_count'] for d in readiness)==252
new=set(candidate['proof_files'])-set(old['proof_files']);assert len(new)==5 and new==set(offer['proof_files'])
eq(candidate['declarations'],base['declarations'],'all declaration ordering and bodies retained')
eq(candidate['counts'],base['counts'],'same prepair counts')
eq(candidate['source_sha256'],base['source_sha256'],'current60 source map retained')
eq(candidate['scope_pages'],old['scope_pages'],'owner scope unchanged')
assert all(candidate['proof_files'][n]==v for n,v in old['proof_files'].items())
assert len(old['proof_files'])==495 and len(candidate['proof_files'])==500
total=0;pair_summaries=[]
for n in sorted(new):
    source=rooted(n);row=rows[n];meta=expected['proof_files'][n];om=offer['proof_files'][n]
    eq(H(source),meta['sha256'],'source matches prepair reviewed body')
    eq(meta['declarations'],row['public_declarations'],'readiness exact name order')
    text=source.read_text();ns=re.findall(r'^namespace\s+([^\s]+)',text,re.M)
    public=re.findall(r'^(?:theorem|lemma)\s+([\w\u0080-\uffff]+)',text,re.M)
    assert ns and len(set(ns))==1
    eq([ns[0]+'.'+x for x in public],meta['declarations'],'full actual source public names')
    pp=[p for p in pairs if p['source']['file']==n]
    assert len(pp)==2 and [p['kind'] for p in pp]==['standalone','named']
    natives={}
    for p in pp:
        zero(p);a=J(checked(p['actual_record']));zero(a)
        eq(a['source'],n,'native source');eq(a['source_sha256_before'],H(source),'source before');eq(a['source_sha256_after'],H(source),'source after')
        cmd=['lake','env','lean','SafeLearning/'+source.name] if p['kind']=='standalone' else ['lake','build','SafeLearning.'+source.stem]
        eq(a['command'],cmd,'actual command');eq(a['actual_workdir'],str(R/'verification/lean'),'actual cwd')
        eq(p['raw_log'],{'file':a['log'],'sha256':a['log_sha256']},'native raw log pointer')
        assert H(checked(p['source_snapshot']))==H(source);checked(p['raw_log'])
        for k in ('actual_record','raw_log','source_snapshot'):
            assert offer['required_evidence_artifacts_sha256'][p[k]['file']]==p[k]['sha256']
        natives[p['kind']]=a
        raw=checked(p['raw_log']).read_text()
        pair_summaries.append({'source':n,'kind':p['kind'],'actual_record':p['actual_record'],'original_warning_diagnostics':len(re.findall(r'^.*warning:',raw,re.M))})
    assert isinstance(om['evidence_sha256'],str) and om['evidence_sha256']==pp[0]['actual_record']['sha256']
    assert om['theorem_count']==len(public) and om['public_theorem_names']==om['mapped_named_declarations']==meta['declarations']
    meta.pop('canonical_paired_evidence_not_yet_available')
    meta['standalone_compile_status']='passed_source_matched_actual_canonical_pair'
    meta['standalone_compile_evidence']={'file':n,'sha256':H(source),'exit_code':0,'log':natives['standalone']['log'],'log_sha256':natives['standalone']['log_sha256'],'source_unchanged':True,'actual_record':pp[0]['actual_record']}
    meta['actual_pair']=pp;meta['evidence_sha256']=pp[0]['actual_record']['sha256']
    meta['canonical_pair_evidence_directory_assigned_by_root']=str((R/pp[0]['source_snapshot']['file']).parent.parent.relative_to(R))+'/'
    eq(candidate['proof_files'][n],meta,'exact new proof metadata native pair update')
    for k in ('sha256','declarations','actual_pair','standalone_compile_status','standalone_compile_evidence','original_tmp_source','original_tmp_trial'):eq(om[k],meta[k],'offer/candidate '+k)
    eq(om['independent_whole_scope_peer'],durable(row['independent_whole_scope_peer']),'same exact whole peer reference')
    total+=len(public)
assert total==153
for e in expected['exercises']:
    if 'entire_literal_closure28' in e:
        e['entire_literal_closure28']['canonical_pair_and_owner_integration_pending']=False
        e['entire_literal_closure28']['canonical_pairs_available_owner_integration_pending']=True
    for c in e['claims']:
        if 'reviewed_owner28_transition'in c and c['reviewed_owner28_transition'].get('canonical_pair_pending')is True:c['reviewed_owner28_transition']['canonical_pair_pending']=False
for c in expected['material_claims']:
    if 'reviewed_owner28_transition'in c and c['reviewed_owner28_transition'].get('canonical_pair_pending')is True:c['reviewed_owner28_transition']['canonical_pair_pending']=False
expected['status']='reviewed_current60_owner28_five_source_actual_pair_candidate_pending_root_owner_integration'
expected['generated_at_utc']=candidate['generated_at_utc']
binding=candidate['actual_current60_pair_binding28']
eq(binding['five_new_sources'],sorted(new),'exact five pair-bound sources')
assert binding['public_declaration_count']==153 and binding['whole_exercises']==4 and binding['whole_material_units']==26
assert binding['owner_integrated']is False and binding['coverage_complete']is False and binding['original_math_peer_body_or_time_reinterpreted']is False
eq(binding['original_pending_v2_candidate'],offer['original_pending_v2_candidate'],'old full pending candidate')
eq(binding['original_pending_v2_full_mapping_peer'],offer['original_pending_v2_independent_mapping_peer'],'old full mapping peer')
eq(binding['ten_source_readiness'],offer['actual_ten_source_canonical_readiness'],'actual10 readiness')
eq(binding['commissioning17_readiness'],offer['actual_commissioning17_canonical_readiness'],'actual17 readiness')
expected['actual_current60_pair_binding28']=binding
eq(candidate,expected,'ENTIRE independent forward reconstruction')
# An independently derived inverse removes only typed pointer and availability updates.
inverse=copy.deepcopy(candidate)
inverse.pop('actual_current60_pair_binding28')
inverse['status']=base['status'];inverse['generated_at_utc']=base['generated_at_utc']
for n in new:inverse['proof_files'][n]=copy.deepcopy(base['proof_files'][n])
for dst,src in zip(inverse['exercises'],base['exercises']):
    if 'entire_literal_closure28'in src:dst['entire_literal_closure28']=copy.deepcopy(src['entire_literal_closure28'])
    for a,b in zip(dst['claims'],src['claims']):
        if 'reviewed_owner28_transition'in b:a['reviewed_owner28_transition']=copy.deepcopy(b['reviewed_owner28_transition'])
for a,b in zip(inverse['material_claims'],base['material_claims']):
    if 'reviewed_owner28_transition'in b:a['reviewed_owner28_transition']=copy.deepcopy(b['reviewed_owner28_transition'])
for r in manifest['changed_new_reference_fields']:
    parent=inverse
    for k in r['path'][:-1]:parent=parent[k]
    parent[r['path'][-1]]=copy.deepcopy(r['original_v2_value'])
eq(inverse,base,'ENTIRE inverse restores original e1d7 candidate')
expected_ex={'lipsdp.html#book-m12-b1','verification.html::exercise-15','verification.html::exercise-16','viability.html::exercise-15'}
expected_units={f'{p}::node-{i}' for p,ii in [('lipsdp.html',[964,965,969,971,972,974,987,994,998]),('verification.html',[191,192,193,195,725,1157,1161,1162,1166,1170,1172]),('viability.html',[1095,1099,1101,1103,1104,1109])] for i in ii}
assert set(offer['whole_exercise_keys'])==expected_ex
assert set(offer['whole_material_keys'])==expected_units
for c in candidate['material_claims']:
    if 'lipsdp.html::node-976'in c.get('source_unit_keys',[]):assert c.get('whole_current60_source_unit_approved')is not True
for n,h in offer['required_evidence_artifacts_sha256'].items():assert H(rooted(n))==h,n
assert len(offer['required_evidence_artifacts_sha256'])==922 and len(offer['original_closed_byte_aliases'])==634
for n,r in offer['original_closed_byte_aliases'].items():
    assert isinstance(n,str) and set(r)=={'file','sha256'}
    checked(r);assert offer['required_evidence_artifacts_sha256'][r['file']]==r['sha256']
assert not set(offer['required_evidence_artifacts_sha256']).intersection('book/coverage/'+n+'.json' for n in ('core','foundations','applied','applied-promotions','modules'))
actual=J(checked(offer['actual_isolated_candidate_preparation']));zero(actual)
assert actual['protection_errors']==[] and actual['source_owner_selection_bytes_unchanged']is True and actual['live_owner_or_proof_source_or_publication_written']is False
eq(actual['actual_command'],['python3','/tmp/prepare-modules-current60-owner28-durable-pair-bound-v5.py'],'exact native preparation command')
for k,ok in [('helper','candidate_builder'),('runner','actual_isolated_candidate_preparation_runner'),('raw_log','actual_isolated_candidate_preparation_raw_log')]:
    assert actual[k]['sha256']==offer[ok]['sha256'];checked(offer[ok])
for t in (candidate['generated_at_utc'],binding['prepared_at_utc']):assert datetime.fromisoformat(actual['started_at_utc'])<=datetime.fromisoformat(t)<=datetime.fromisoformat(actual['finished_at_utc'])
assert len(binding['preserved_true_preflight_failures'])==2
for r in binding['preserved_true_preflight_failures']:
    d=J(checked(r));assert type(d['actual_exit_code'])is int and d['actual_exit_code']!=0
offer1=J(checked(offer['original_preparation_offer']))
for k in set(offer1)-{'actual_isolated_candidate_preparation','required_evidence_artifacts_sha256','original_closed_byte_aliases'}:eq(offer[k],offer1[k],'original offer field '+k)
report={'status':'passed_independent_exact_modules28_current60_five_source_pair_bound_candidate_mechanics','errors':[],'candidate':offer['candidate'],'offer':ref(O),'actual_isolated_candidate_preparation':offer['actual_isolated_candidate_preparation'],'original_pending_candidate':offer['original_pending_v2_candidate'],'original_mapping_peer':offer['original_pending_v2_independent_mapping_peer'],'counts':candidate['counts'],'new_source_count':5,'new_public_declarations':153,'genuine_actual_pair_count':10,'old_proof_metadata_rows_exact':495,'whole_exercises':offer['whole_exercise_keys'],'whole_material_units':offer['whole_material_keys'],'entire_forward_and_inverse_exact':True,'new_reference_rebinding_count':len(computed_paths),'closed_root_relative_artifacts':922,'exact_original_aliases':634,'original_semantic_body_or_time_changed':False,'native_pair_summaries':pair_summaries,'native_schema_note':'evidence_sha256 is the original standalone native-record SHA string; the full actual_pair typed-list and all six source/native/raw/snapshot evidence rows are exact. A consumer requiring a map needs an explicit distinct native-schema adaptation; no production installer executed by this reader.','coverage_complete':False}
with OUT.open('x')as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'status':report['status'],'findings':ref(OUT),'forward_inverse_exact':True,'sources':5,'names':153,'pairs':10,'closed_refs':922}))
