from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

R=Path('/home/oxrexkevin/SafetyBased')
B=Path('/tmp/applied28-source60-identity-v1')
OUT=Path('/tmp/applied60-identity-independent-modules28-reader-v1.json')
START=datetime.now(timezone.utc).isoformat()
def H(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(p): return Path(p) if Path(p).is_absolute() else R/p
def J(p): return json.loads(Path(p).read_bytes())
def ref(p): return {'file':str(p),'sha256':H(p),'bytes':Path(p).stat().st_size}
def check_ref(v):
    assert isinstance(v,dict) and H(P(v['file']))==v['sha256'],v
    return P(v['file'])
def zero(v):
    assert type(v['actual_exit_code']) is int and v['actual_exit_code']==0

OFFER=B/'applied28-source60-identity-additions-draft-v2.json'
assert H(OFFER)=='7f2476de7f7894e6567929a4acf294f5a50ddfb3d31a32e82e3a5332a4d44534'
o=J(OFFER)
for k in ('candidate','candidate_promotions','candidate_builder','identity_sidecar','identity_integrity','original_reviewed_source55_offer','actual_isolated_candidate_preparation','original_preparation_offer'):
    check_ref(o[k])
builder=check_ref(o['candidate_builder']).read_text()
assert len(builder.splitlines())>=100 and 'B.mkdir(exist_ok=False)' in builder
c=J(R/'book/coverage/applied.json');q=J(R/'book/coverage/applied-promotions.json')
n=J(check_ref(o['candidate']));nq=J(check_ref(o['candidate_promotions']))
s=J(check_ref(o['identity_sidecar']));i=J(check_ref(o['identity_integrity']))
original=J(check_ref(o['original_reviewed_source55_offer']))
native=J(check_ref(o['actual_isolated_candidate_preparation']))
old=J(R/'book/coverage/inventory-after-correction55.json')
new=J(R/'book/coverage/inventory-after-correction60.json')
page='SafeLearning/primer-probability.html';key='primer-probability.html::node-386'
assert H(R/'book/coverage/inventory.json')==H(R/'book/coverage/inventory-after-correction60.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert H(R/'book/coverage/applied.json')=='31b6af21c8ba9d214380ba5c116046bf7587eba3d736e1a536266c5fbfe61e68'
assert H(R/'book/coverage/applied-promotions.json')=='72ee23132c02823bc13fa513d2892e79d748b6617b0d3fe52b3de7e29735a5a2'
scope=set(c['scope_pages']);assert len(scope)==3
unchanged={}
physical={}
for section,count in [('exercises',128),('material_source_units',2059)]:
    a={r['key']:r for r in old[section] if r['source'] in scope}
    b={r['key']:r for r in new[section] if r['source'] in scope}
    assert a.keys()==b.keys() and len(a)==count
    changed=[]
    for k in a:
        row=copy.deepcopy(b[k]);row['source_sha256']=a[k]['source_sha256']
        if row!=a[k]:changed.append(k)
    assert changed==([] if section=='exercises' else [key])
    unchanged[section]=count-len(changed);physical[section]=(a,b)
oldrow,newrow=(physical['material_source_units'][x][key] for x in (0,1))
oldlast='change any of them and every probability changes.'
newlast='changes to those inputs can change the trajectory law and probabilities computed from it.'
assert newrow['source_text']==oldrow['source_text'].replace(oldlast,newlast)
assert hashlib.sha256(newrow['source_text'].encode()).hexdigest()==newrow['text_sha256']
idx=next(j for j,r in enumerate(c['material_claims']) if r['id']=='material.'+key)
prior=c['material_claims'][idx]
assert prior['status']=='pending' and prior['lean_declarations']==[] and key not in q['material']
assert len(c['proof_files'])==312 and sum(len(x['claims']) for x in c['exercises'])==468 and len(c['material_claims'])==1954
assert s['entire_original_pending386_claim_body']==prior and s['original_physical386_record']==oldrow and s['current_physical386_record']==newrow
for name, live in [('ledger',R/'book/coverage/applied.json'),('promotions',R/'book/coverage/applied-promotions.json')]:
    p=check_ref(s['original_installed27_exact_bytes'][name]);assert p.read_bytes()==live.read_bytes()
assert s['unchanged_owned_literal_counts']=={'exercises':128,'physical_units':2058,'exercise_claims':468,'other_material_claims':1953,'unpruned_proof_metadata_rows':312}
assert s['direct_probability_page_hash_bindings_rebased']=={'exercises':44,'material_claims':596}
app=J(check_ref(s['source56_to60_native_application']));appnative=J(check_ref(s['source56_to60_actual_execution']));zero(appnative)
assert app['status']=='passed_actual_source56_to60_corrections_full29_inventory_owner_identity_rebase_pending'
assert [r['correction_id'] for r in app['applications']]==[56,57,58,59,60]
receipt=next(r for r in app['applications'] if r['correction_id']==57)
assert receipt==s['exact_actual_source57_receipt'] and receipt['source_after']=={'file':page,'sha256':new['source_sha256'][page]}
assert receipt['exact_changed_text_keys']=={'exercises':[],'material_source_units':[key]}

# Independent forward construction restricts every entire candidate body, including all old history.
expected=copy.deepcopy(c);expectedq=copy.deepcopy(q)
expected['source_sha256'][page]=new['source_sha256'][page]
rebound={}
for section in ('exercises','material_claims'):
    rows=[r for r in expected[section] if r.get('source')==page]
    rebound[section]=len(rows)
    for row in rows:
        assert row['source_sha256']==old['source_sha256'][page]
        row['source_sha256']=new['source_sha256'][page]
assert rebound=={'exercises':44,'material_claims':596}
updated=expected['material_claims'][idx]
updated['text_sha256']=newrow['text_sha256'];updated['statement_in_prose']=newrow['source_text']
for field in ('source_clauses','remaining_gaps'):
    updated[field]=[x.replace(oldlast,newlast) for x in prior[field]]
assert s['entire_current_pending386_claim_body']==updated
overlay={'inventory':'book/coverage/inventory-after-correction60.json','inventory_sha256':H(R/'book/coverage/inventory-after-correction60.json'),'identity_sidecar':o['identity_sidecar'],'original_installed27_ledger':s['original_installed27_exact_bytes']['ledger'],'original_installed27_promotions':s['original_installed27_exact_bytes']['promotions'],'original_reviewed_source55_offer':o['original_reviewed_source55_offer'],'changed_pending_unit':key,'new_proof_sources':0,'new_material_or_exercise_decisions':0,'scope':'Source60 identity bindings; only pending386 adopts actual correction57, retaining its pending status and complete original claim history. Every earlier proof, promotion, hypothesis, semantic review body/time and every other literal is preserved.'}
expected['current60_owner_identity']=overlay;expectedq['current60_owner_identity']=copy.deepcopy(overlay)
inherited=original['required_evidence_artifacts_sha256'];assert len(inherited)==192
required=o['required_evidence_artifacts_sha256'];assert len(required)==210
assert all(required.get(k)==v for k,v in inherited.items())
for k,v in required.items():assert H(P(k))==v,k

def validate(a,b,offer,execution):
    assert a==expected and b==expectedq,'entire candidate differs outside exact authorized transformation'
    assert offer['proof_files']=={} and offer['new_actual_paired_records']==[] and offer['new_material_keys']==[]
    assert offer['coverage_complete'] is False and offer['final_independent_candidate_mapping_peer'] is None
    assert offer['errors']==[] and offer['counts']==c['counts'] and offer['source_sha256']==expected['source_sha256']
    assert offer['baseline27_owner_sha256']==s['installed27_owner_sha256']
    assert offer['inventory_sha256']==H(R/'book/coverage/inventory.json') and offer['base_selection_sha256']=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
    assert len(offer['required_evidence_artifacts_sha256'])==210
    assert all(offer['required_evidence_artifacts_sha256'].get(k)==v for k,v in inherited.items())
    zero(execution)
    assert execution['actual_command']==['/home/oxrexkevin/.local/oss-cad-suite/bin/tabbypy3',o['candidate_builder']['file']]
    assert execution['actual_workdir']==str(R) and execution['helper_sha256_before']==execution['helper_sha256_after']=={o['candidate_builder']['file']:o['candidate_builder']['sha256']}
    assert H(P(execution['log']))==execution['log_sha256'] and execution['live_owner_or_proof_source_or_publication_written'] is False
validate(n,nq,o,native)
assert i['exact_inverse_recovers_installed27_entire_ledger_and_promotions'] is True and i['new_proof_sources']==0 and i['new_mathematical_promotions']==0 and i['coverage_complete'] is False

rev=copy.deepcopy(n);revq=copy.deepcopy(nq)
rev.pop('current60_owner_identity');revq.pop('current60_owner_identity');rev['source_sha256'][page]=old['source_sha256'][page]
for section in ('exercises','material_claims'):
    for row in rev[section]:
        if row.get('source')==page:row['source_sha256']=old['source_sha256'][page]
rev['material_claims'][idx]=copy.deepcopy(prior)
assert rev==c and revq==q
assert (json.dumps(rev,ensure_ascii=False,indent=2)+'\n').encode()==(R/'book/coverage/applied.json').read_bytes()
assert (json.dumps(revq,ensure_ascii=False,indent=2)+'\n').encode()==(R/'book/coverage/applied-promotions.json').read_bytes()

fixtures=[]
def reject(label,which,mutate):
    a,b,offer,execution=n,nq,o,native
    if which=='claim':
        a=dict(n);a['material_claims']=list(n['material_claims']);a['material_claims'][idx]=copy.deepcopy(n['material_claims'][idx]);mutate(a['material_claims'][idx])
    elif which=='ledger':a=copy.deepcopy(n);mutate(a)
    elif which=='promotions':b=copy.deepcopy(nq);mutate(b)
    elif which=='offer':offer=copy.deepcopy(o);mutate(offer)
    elif which=='execution':execution=copy.deepcopy(native);mutate(execution)
    else:raise AssertionError(which)
    try:validate(a,b,offer,execution)
    except AssertionError:fixtures.append({'case':label,'rejected':True})
    else:raise AssertionError('negative accepted: '+label)
reject('pending386 falsely promoted','claim',lambda d:d.update(status='proved'))
reject('pending386 fabricated Lean declaration','claim',lambda d:d.update(lean_declarations=['FalseProof']))
reject('pending386 wrong corrected full text','claim',lambda d:d.update(statement_in_prose=prior['statement_in_prose']))
reject('pending386 wrong text digest','claim',lambda d:d.update(text_sha256=oldrow['text_sha256']))
reject('pending386 source clauses remain universal','claim',lambda d:d.update(source_clauses=prior['source_clauses']))
reject('pending386 gaps remain universal','claim',lambda d:d.update(remaining_gaps=prior['remaining_gaps']))
reject('pending386 direct page hash stale','claim',lambda d:d.update(source_sha256=old['source_sha256'][page]))
reject('old proof metadata changed','ledger',lambda d:d['proof_files'].pop(next(iter(d['proof_files']))))
reject('old exercise claim changed','ledger',lambda d:d['exercises'][0]['claims'][0].update(status='pending'))
reject('foreign material claim inserted','ledger',lambda d:d['material_claims'].append({'id':'foreign'}))
reject('historical identity metadata removed','ledger',lambda d:d.pop('current55_owner_identity'))
reject('identity overlay invents new proof','ledger',lambda d:d['current60_owner_identity'].update(new_proof_sources=1))
reject('pending386 becomes promotion','promotions',lambda d:d['material'].update({key:{'status':'proved'}}))
reject('old promotion history removed','promotions',lambda d:d.pop('current55_owner_identity'))
reject('offer falsely complete','offer',lambda d:d.update(coverage_complete=True))
reject('offer invents paired record','offer',lambda d:d.update(new_actual_paired_records=[{}]))
reject('inherited old evidence pruned','offer',lambda d:d['required_evidence_artifacts_sha256'].pop(next(iter(inherited))))
reject('native boolean masquerades as zero','execution',lambda d:d.update(actual_exit_code=False))
reject('native command differs','execution',lambda d:d.update(actual_command=['python3','unexecuted.py']))
reject('native helper hash differs','execution',lambda d:d['helper_sha256_after'].update({o['candidate_builder']['file']:'0'*64}))
reject('native log hash differs','execution',lambda d:d.update(log_sha256='0'*64))
reject('native says live write','execution',lambda d:d.update(live_owner_or_proof_source_or_publication_written=True))
assert not OUT.exists()
result={'status':'passed_independent_applied28_current60_zero_proof_candidate_mechanics','errors':[],'reader_started_at_utc':START,'reader_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(OFFER),'candidate':o['candidate'],'candidate_promotions':o['candidate_promotions'],'candidate_builder':o['candidate_builder'],'identity_sidecar':o['identity_sidecar'],'original_reviewed55_offer':o['original_reviewed_source55_offer'],'native_author_preparation':o['actual_isolated_candidate_preparation'],'independent_exact_forward_and_raw_inverse':True,'all_inherited_evidence_retained_and_read_hashes':192,'all_required_refs_hash_verified':210,'full_owned_inventory_literals_compared':{'exercises':128,'physical_units':2059},'unchanged_old_claims_and_metadata':{'exercise_claims':468,'other_material_claims':1953,'proof_metadata':312},'only_pending_literal_changed':{'key':key,'status':'pending','declarations':[],'new_text_sha256':newrow['text_sha256'],'entire_old_claim':prior,'entire_current_claim':updated},'negative_fixtures':fixtures,'new_mathematical_promotions':0,'new_proof_sources':0,'original_review_bodies_and_times_reinterpreted':False,'live_owner_or_source_or_selection_or_publication_written':False,'coverage_complete':False,'scope':'Independent mechanical identity/correction review only; every original full mathematical decision and review time remains exact. Root canonical integration and global closure are separate.'}
OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'result':ref(OUT),'negative_fixtures':len(fixtures),'new_proofs':0,'new_promotions':0}))
