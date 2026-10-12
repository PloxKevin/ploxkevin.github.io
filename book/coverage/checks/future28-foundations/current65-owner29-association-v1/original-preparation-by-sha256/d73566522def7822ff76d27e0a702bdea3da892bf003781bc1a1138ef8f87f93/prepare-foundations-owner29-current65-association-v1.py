from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

R = Path('/home/oxrexkevin/SafetyBased')
D = R/'book/coverage/checks/future28-foundations/current65-owner29-association-v1'
assert not D.exists()
B = R/'book/coverage/checks/future28-foundations/current64-owner29-provisional-v3'
CTX = Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
IN64 = R/'book/coverage/inventory-after-correction64.json'
IN65 = R/'book/coverage/inventory-after-correction65.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def data(x): return (json.dumps(x, indent=2)+'\n').encode()
def path(n): return Path(n) if Path(n).is_absolute() else R/n
def ref(p):
    p=Path(p)
    return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def check(r):
    p=path(r['file']); assert sha(p)==r['sha256'],str(p)
    return read(p)
assert sha(CTX)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
c=read(CTX)
def guard():
    for field in ['pins_sha256','held_current_source_sha256','owners_sha256']:
        for n,h in c[field].items(): assert sha(path(n))==h,n
    assert sha(IN65)==sha(R/'book/coverage/inventory.json')=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
    assert len(read(R/'book/coverage/material-corrections.json')['corrections'])==65
    return {field:copy.deepcopy(c[field]) for field in ['pins_sha256','held_current_source_sha256','owners_sha256']}
started=datetime.now(timezone.utc).isoformat();before=guard()
oldpath=B/'foundations29-current64-provisional-candidate-v3.json'
oldofferpath=B/'foundations29-current64-provisional-offer-draft-v3.json'
old=read(oldpath);offer64=read(oldofferpath)
assert sha(oldpath)=='29e32a9400994e54fd9b2c8709f8545012e80de999e8dc1d1c4a6d137f4949bd'
assert sha(oldofferpath)=='a92428b92364e181108717bfd1eed852c9d4c9314d9aece7bea6eeb23306a3ef'
assert check(offer64['candidate'])==old and offer64['all_new_actual_canonical_pairs_pending'] is True
inv64=read(IN64);inv65=read(IN65);pages=set(old['scope_pages'])
owned64=[u for u in inv64['material_source_units'] if u['source'] in pages]
owned65=[u for u in inv65['material_source_units'] if u['source'] in pages]
ex64=[u for u in inv64['exercises'] if u['source'] in pages]
ex65=[u for u in inv65['exercises'] if u['source'] in pages]
assert owned64==owned65 and len(owned65)==1756
assert ex64==ex65 and len(ex65)==119
assert all(inv64['source_sha256'][p]==inv65['source_sha256'][p]==old['source_sha256'][p]==sha(R/p) for p in pages)
assert len(old['exercises'])==119 and old['counts']['material_claim_statuses']=={'not_a_formal_claim':532,'proved':1141,'pending':446}
app=check(c['actual_source65_application']);native=check(c['actual_source65_application_native'])
for n in ['actual_exit_code','exit_code']:
    if n in native: assert type(native[n]) is int and native[n]==0
assert native['actual_exit_code']==0 and native.get('status')=='passed'
archives={};planned={}
def archived(r):
    p=path(r['file']); assert sha(p)==r['sha256']
    out=D/'original-association-inputs-by-sha256'/r['sha256']/p.name
    rr={'file':out.relative_to(R).as_posix(),'sha256':r['sha256']}
    if out in planned: assert planned[out]==p.read_bytes()
    planned[out]=p.read_bytes();archives[r['file']]=rr
    return rr
contextref=archived(ref(CTX));appref=archived(c['actual_source65_application']);nativeref=archived(c['actual_source65_application_native'])
rawname=R/'reports/full-coverage/source65-correction-application29-execution-v1.log'
rawref=archived(ref(rawname));assert rawref['sha256']==c['pins_sha256'][rawname.relative_to(R).as_posix()]
prior={k:ref(B/k) for k in ['foundations29-current64-provisional-candidate-v3.json','foundations29-current64-provisional-offer-draft-v3.json','foundations29-current64-exact-identity-and-sixteen-row-inverse-v3.json','foundations29-current64-provisional-preparation-closure-v3.json']}
candidate=copy.deepcopy(old)
candidate['current65_owner_identity']={
    'inventory':ref(IN65),'original_current64_candidate':ref(oldpath),
    'actual_source65_application':appref,'actual_source65_application_native':nativeref,
    'current65_guard_context':contextref,'owned_material_units_exactly_unchanged':1756,
    'owned_exercises_exactly_unchanged':119,'owned_source_sha256_unchanged':True,
    'original_current64_identity_mapping_support_and_all_body_times_retained_exactly':True,
    'scope':'Inventory association only after actual Source65 corrections on a disjoint Module page. Every Foundation literal, exercise, mathematical/classification row, proof body, original Source64 association and historical receipt is exactly unchanged. Canonical pairs and final independent candidate mapping remain pending.'}
reverse=copy.deepcopy(candidate);reverse.pop('current65_owner_identity');assert reverse==old and data(reverse)==oldpath.read_bytes()
base=D.relative_to(R).as_posix();candidatepath=R/(base+'/foundations29-current65-provisional-candidate-v1.json')
candidatebytes=data(candidate);candidateref={'file':candidatepath.relative_to(R).as_posix(),'sha256':hashlib.sha256(candidatebytes).hexdigest()}
interface={'status':'prepared_current65_inventory_only_association_overlay_pending_canonical_pairs_and_final_mapping','errors':[],
    'started_at_utc':started,'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'original_current64_candidate':ref(oldpath),'candidate':candidateref,'current_inventory':ref(IN65),
    'exact_changes':[{'field':'current65_owner_identity','before_present':False,'after':candidate['current65_owner_identity']}],
    'remove_single_overlay_restores_exact_original_current64_candidate_bytes':True,
    'all1756_owned_material_units_all119_exercise_records_and_owned_source_bytes_identical_between64_and65':True,
    'unchanged_counts':candidate['counts'],'old_exact_source_identity_and_sixteen_row_inverse':offer64['exact_interface'],
    'new_canonical_pairs_pending':True,'final_independent_mapping_review_pending':True,'coverage_complete':False}
interfacepath=R/(base+'/foundations29-current65-inventory-association-exact-inverse-v1.json')
interfacebytes=data(interface);interfaceref={'file':interfacepath.relative_to(R).as_posix(),'sha256':hashlib.sha256(interfacebytes).hexdigest()}
offer=copy.deepcopy(offer64)
offer.update(status='prepared_current65_foundations29_provisional_candidate_pending_canonical_pairs_and_final_mapping',
    started_at_utc=started,prepared_at_utc=datetime.now(timezone.utc).isoformat(),candidate=candidateref,
    mapped_ledger=candidateref['file'],mapped_ledger_sha256=candidateref['sha256'],inventory=ref(IN65),inventory_sha256=sha(IN65),
    original_current64_offer=ref(oldofferpath),current65_inventory_association_interface=interfaceref,
    current65_original_context=contextref,actual_source65_application=appref,actual_source65_application_native=nativeref,
    source65_or_later_inventory_identity_not_inferred=False,
    source65_association_is_actual_but_later_source_identity_not_inferred=True,
    all_source65_owned_literals_exercises_math_and_classification_exactly_unchanged=True)
additional=dict(offer64['additional_frozen_inputs'])
for r in list(prior.values())+[ref(IN65),contextref,appref,nativeref,rawref]:
    if r['file'] in additional: assert additional[r['file']]==r['sha256']
    additional[r['file']]=r['sha256']
offer['additional_frozen_inputs']=additional
offerpath=R/(base+'/foundations29-current65-provisional-offer-draft-v1.json')
planned.update({candidatepath:candidatebytes,interfacepath:interfacebytes,offerpath:data(offer)})
assert guard()==before
for p,b in planned.items(): assert p.is_relative_to(D) and not p.exists()
for p,b in planned.items(): p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
assert guard()==before
print(json.dumps({'status':offer['status'],'candidate':candidateref,'draft_offer':ref(offerpath),'association_interface':interfaceref,
    'owned_material_exercise_counts':[1756,119],'counts':candidate['counts'],'exact_original64_bytes_restored_by_removing_overlay':True,
    'original64_candidate_offer_interface_closure':prior,'exact_input_archive_aliases':archives,'coverage_complete':False}))
