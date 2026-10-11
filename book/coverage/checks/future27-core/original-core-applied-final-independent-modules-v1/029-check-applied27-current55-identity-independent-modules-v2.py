from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');O=Path('/tmp/applied27-current55-identity-independent-modules-confirmation-v2.json');P=Path('/tmp/applied27-source55-identity-v1/applied-audit27-source55-identity-additions-draft-v1.json');assert not O.exists()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def rd(n):return json.loads(path(n).read_text())
def checked(ref):assert set(ref)=={'file','sha256'} and sha(ref['file'])==ref['sha256'];return rd(ref['file'])
assert sha(str(P))=='10623286d794816ad3a78cc4a83c16cbc62cefc2ac62e440549a2ede99daf0d2'
d=rd(str(P));candidate=checked(d['candidate']);prom=checked(d['candidate_promotions']);side=checked(d['identity_sidecar']);integrity=checked(d['identity_integrity'])
assert d['mapped_ledger']==d['candidate']['file'] and d['mapped_ledger_sha256']==d['candidate']['sha256'] and d['mapped_promotions']==d['candidate_promotions']['file'] and d['mapped_promotions_sha256']==d['candidate_promotions']['sha256']
old=rd('book/coverage/applied.json');oldprom=rd('book/coverage/applied-promotions.json');assert sha('book/coverage/applied.json')=='a0e087260288c8e8abc45eb0806eb3b09d17da463f5e918966c3a0686f3976a6' and sha('book/coverage/applied-promotions.json')=='fa58595aacac0b82f9cd9d3bfe41718365113a2ebf76879001edcf3ab4b68fcb'
a=copy.deepcopy(candidate);b=copy.deepcopy(prom);meta=a.pop('current55_owner_identity');assert b.pop('current55_owner_identity')==meta and a==old and b==oldprom
assert checked(d['original_installed26_exact_byte_copies']['ledger'])==old and checked(d['original_installed26_exact_byte_copies']['promotions'])==oldprom
original=checked(d['original_source53_final_offer']);assert original==d['entire_original_source53_final_offer_body_and_time']==side['entire_original_source53_final_offer_body_and_time']
assert d['errors']==side['errors']==integrity['errors']==[] and d['proof_files']=={} and d['new_actual_paired_records']==[] and d['new_material_keys']==[] and d['coverage_complete'] is False
assert integrity['new_proof_sources']==integrity['new_material_or_exercise_decisions']==0 and integrity['live_owner_written'] is False
iv=checked(side['current_inventory']);hist=checked(side['historical_inventory']);assert d['inventory_sha256']==sha(d['inventory'])=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
owned=set(old['scope_pages']);counts={}
for field in ['exercises','material_source_units']:
 oldindex={r['key']:r for r in hist[field] if r['source'] in owned};newindex={r['key']:r for r in iv[field] if r['source'] in owned};assert oldindex==newindex
 native=side['entire_owned_inventory_records']['exercises' if field=='exercises' else 'material_source_units'];assert native==newindex;counts[field]=len(newindex)
assert counts=={'exercises':128,'material_source_units':2059}
assert len(old['exercises'])==128 and sum(len(e['claims']) for e in old['exercises'])==468 and len(old['material_claims'])==1954 and len(old['proof_files'])==312
actual_path=Path('/tmp/applied27-source55-identity-candidate-actual-v1.json');actual=rd(str(actual_path));assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
assert actual['actual_command']==['python3',d['candidate_builder']['file']] and actual['helper_sha256_before']==actual['helper_sha256_after']==d['candidate_builder']['sha256']==sha(d['candidate_builder']['file'])
assert sha(actual['raw_log'])==actual['raw_log_sha256'] and sha(actual['original_runner']['file'])==actual['original_runner']['sha256']
sel=rd(d['base_selection']);assert sha(d['base_selection'])==d['base_selection_sha256'] and len(sel['proof_files'])==1167
protected={n:r['sha256'] for n,r in sel['proof_files'].items()}
manifest=rd('reports/full-coverage/checkpoint-26-manifest.json');assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};app=rd('reports/full-coverage/source54-55-corrections-application-v1.json')
assert sha('reports/full-coverage/source54-55-corrections-application-v1.json')=='845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528'
for row in app['applications']:assets[row['source_after']['file']]=row['source_after']['sha256']
assert len(assets)==31;protected.update(assets);protected.update(d['baseline26_owner_sha256']);assert len(d['baseline26_owner_sha256'])==5
for n,h in protected.items():assert sha(n)==h,n
closed=dict(d['required_evidence_artifacts_sha256'])
for n,h in original['required_evidence_artifacts_sha256'].items():
 assert n not in closed or closed[n]==h
 closed[n]=h
assert len(original['required_evidence_artifacts_sha256'])==144
for n,h in closed.items():assert path(n).is_file() and not path(n).is_symlink() and sha(n)==h,n
for n in [str(P),d['candidate']['file'],d['candidate_promotions']['file'],str(actual_path),actual['raw_log'],actual['original_runner']['file'],d['candidate_builder']['file'],str(Path(__file__))]:closed[n]=sha(n)
failure=rd('/tmp/applied27-current55-identity-independent-modules-actual-v1.json');assert type(failure['actual_exit_code']) is int and failure['actual_exit_code']==1 and sha(failure['raw_log'])==failure['raw_log_sha256']
assert sha(failure['checker']['file'])==failure['checker']['sha256'] and sha(failure['actual_runner']['file'])==failure['actual_runner']['sha256']
for n in [failure['checker']['file'],failure['actual_runner']['file'],'/tmp/applied27-current55-identity-independent-modules-actual-v1.json',failure['raw_log']]:closed[n]=sha(n)
result={'preserved_initial_reader_failure':failure,'reader_delta':'Reader v1 unnecessarily required inherited evidence to be duplicated at the outer offer level. Reader v2 explicitly hashes and retains the immutable original144 plus outer10 union, rejecting conflicting digests. Producer and original offer bodies are unchanged.','status':'passed_independent_exact_current55_identity_only_candidate_mechanics','errors':[],'reviewer':'independent Modules agent','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':d['candidate'],'candidate_ledger':d['candidate'],'candidate_promotions':d['candidate_promotions'],'reviewed_offer':{'file':str(P),'sha256':sha(str(P))},'original_source53_reviewed_offer':d['original_source53_final_offer'],'identity_sidecar':d['identity_sidecar'],'exact_inverse_restores_entire_installed26_ledger_and_promotions':True,'whole_128_exercises_and2059_physical_records_equal_source53_to55':True,'all468_claims1954_material_bodies312_unpruned_proof_metadata_exact':True,'original_source53_offer_body_time_and144_evidence_refs_unchanged':True,'entire_original_reviewed_draft_offer_body_and_time':d,'entire_original_source53_final_offer_body_and_time':original,'entire_original_actual_identity_preparation_record_and_time':actual,'new_proof_sources':0,'new_material_or_exercise_decisions':0,'protected_selected26_source_count':1167,'protected_current55_asset_count':31,'protected_installed26_owner_count':5,'closed_evidence_sha256':closed,'scope':'Independent read-only current55 Applied identity-only mechanics. Remove exactly current55_owner_identity from both candidate bodies to recover entire installed26 bytes semantically. Original math/evidence/review/status/time retained. Viability42 is separate explicit Module-owned mapping/proof supply, absent from Applied owner additions. No semantic rereview, compiler, canonical owner copy or live integration executed.'}
with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','peer':str(O),'sha256':sha(str(O)),'new_proofs':0,'owned_exercises':128,'owned_material':2059}))
