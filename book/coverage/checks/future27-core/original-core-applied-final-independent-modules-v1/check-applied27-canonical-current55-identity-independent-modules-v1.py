from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');O=Path('/tmp/applied27-canonical-current55-identity-independent-modules-check-result-v1.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def read(n):return json.loads(path(n).read_bytes())
def ref(p):return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def checked(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'],r;return p
def zero(d):
 cs=[d[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in d];assert cs and all(type(x)is int and x==0 for x in cs)
P=R/'book/coverage/checks/applied-future27/current55-identity-v1/applied27-current55-identity-offer-canonical-v1.json';assert sha(P)=='0be877c77792c53e548054a3abb7222c02b2df89d42e425fc4cbfc1f2be7648a'
a=read(P);meta=a['root_exact_canonical_identity_copy'];old=read(checked(meta['original_final_offer']));pack=read(checked(meta['original_pack']));peer=read(checked(a['final_independent_candidate_mapping_peer']))
assert pack['final_reviewed_offer']['sha256']==meta['original_final_offer']['sha256']=='b98f3690edc0a88473258545ff2ae8f18d2cc786da08aa9d5fd483d536f3514d'
assert old==pack['entire_original_final_reviewed_offer_body_and_time'] and peer==old['entire_original_independent_identity_peer_body_and_time']==a['entire_original_independent_identity_peer_body_and_time']
assert a['final_independent_candidate_mapping_peer']['sha256']=='acf2bd0c04e30124109507023d7db14e0a0bfd54ce961fc61306296035f2e5f6' and 'passed' in peer['status'] and peer['errors']==[]
inverse=copy.deepcopy(a);inverse.pop('root_exact_canonical_identity_copy')
fields=['candidate','candidate_promotions','candidate_builder','identity_sidecar','identity_integrity','original_source53_final_offer','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation','preserved_original_draft_offer','mapped_ledger','mapped_promotions','original_installed26_exact_byte_copies','original_closed_byte_aliases','required_evidence_artifacts_sha256','scope']
for k in fields:inverse[k]=copy.deepcopy(old[k])
assert inverse==old
assert a['candidate']=={'file':a['mapped_ledger'],'sha256':a['mapped_ledger_sha256']} and a['candidate_promotions']=={'file':a['mapped_promotions'],'sha256':a['mapped_promotions_sha256']}
assert a['candidate']['sha256']=='31b6af21c8ba9d214380ba5c116046bf7587eba3d736e1a536266c5fbfe61e68' and a['candidate_promotions']['sha256']=='72ee23132c02823bc13fa513d2892e79d748b6617b0d3fe52b3de7e29735a5a2'
c=read(checked(a['candidate']));pr=read(checked(a['candidate_promotions']));oc=read(checked(a['original_installed26_exact_byte_copies']['ledger']));opr=read(checked(a['original_installed26_exact_byte_copies']['promotions']))
ci=copy.deepcopy(c);pi=copy.deepcopy(pr);ci.pop('current55_owner_identity');pi.pop('current55_owner_identity');assert ci==oc==read('book/coverage/applied.json') and pi==opr==read('book/coverage/applied-promotions.json')
assert len(c['exercises'])==128 and len(c['material_claims'])==1954 and len(c['proof_files'])==312
assert a['counts']=={'exercises':128,'complete_math':128,'partial':0,'pending':0,'exercise_claims':468,'material_claim_records':1954,'material_source_units':2059}
assert a['proof_files']=={} and a['new_actual_paired_records']==[] and a['new_material_keys']==[] and meta['new_proof_sources']==0 and meta['owner_installation_claimed'] is False
assert a['inventory_sha256']==sha(R/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert a['source_sha256']==old['source_sha256']
for n,h in a['source_sha256'].items():checked({'file':n,'sha256':h})
assert len(pack['original_closed_byte_aliases'])==39 and len(a['original_closed_byte_aliases'])==42
expected=set(pack['original_closed_byte_aliases'])|{str(path('/tmp/applied27-current55-reviewed-offer-original-byte-pack-v1/applied27-current55-reviewed-offer-original-byte-pack-v1.json'))}|{str(Path('/tmp')/n) for n in ['prepare-applied27-current55-reviewed-offer-original-byte-pack-v1.py','run-applied27-current55-reviewed-offer-original-byte-pack-v1.py','applied27-current55-reviewed-offer-original-byte-pack-actual-v1.json','applied27-current55-reviewed-offer-original-byte-pack-actual-v1.log']}
assert set(a['original_closed_byte_aliases'])==expected
for n,r in a['original_closed_byte_aliases'].items():
 cp=checked(r);assert cp.is_relative_to(R) and cp.read_bytes()==path(n).read_bytes()
 assert r['file'].startswith('book/coverage/checks/applied-future27/current55-identity-v1/original-closed-bytes/')
for n,h in a['required_evidence_artifacts_sha256'].items():
 assert not Path(n).is_absolute();checked({'file':n,'sha256':h})
assert len(a['required_evidence_artifacts_sha256'])==192
for n,h in pack['unchanged_root_evidence_sha256'].items():checked({'file':n,'sha256':h})
actualp=R/'reports/full-coverage/applied27-current55-canonical-copy-execution-v1.json';actual=read(actualp);zero(actual)
assert actual['actual_command']==['python3','book/coverage/checks/root_copy_applied27_identity_v2.py'] and actual['actual_workdir']==str(R)
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={meta['root_copy_helper']['file']:meta['root_copy_helper']['sha256']};checked(meta['root_copy_helper']);checked({'file':actual['log'],'sha256':actual['log_sha256']})
codep=Path('/tmp/root-applied27-identity-copy2-independent-modules-review-v3.json');assert sha(codep)=='e57538b4e33094e08f39654817ec8a2e6b49ed6d1391cdd2bc45f991deef4ea9';code=read(codep);assert 'passed' in code['status'] and code['errors']==[] and code['helper']==meta['root_copy_helper']
assert code['canonical_copy_total_alias_count']==42 and code['original_alias_count']==39
sel=read('reports/full-coverage/checkpoint-26-selection.json');assert len(sel['proof_files'])==1167
protected={n:r['sha256'] for n,r in sel['proof_files'].items()}
assets={n:h for n,h in read('reports/full-coverage/checkpoint-26-manifest.json')['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for r in read('reports/full-coverage/source54-55-corrections-application-v1.json')['applications']:assets[r['source_after']['file']]=r['source_after']['sha256']
protected.update(assets);protected.update(a['baseline26_owner_sha256']);protected['book/coverage/inventory.json']=a['inventory_sha256']
newpairs=read('book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json');assert len(newpairs['sources'])==8
for r in newpairs['sources']:protected[r['canonical_source']]=r['source']['sha256']
for n,h in protected.items():checked({'file':n,'sha256':h})
closed=copy.deepcopy(a['required_evidence_artifacts_sha256']);closed.update(code['closed_evidence_sha256']);closed[str(codep)]=sha(codep)
for p in [P,actualp,checked(meta['root_copy_helper']),path(actual['log'])]:closed[ref(p)['file']]=sha(p)
for n,h in closed.items():checked({'file':n,'sha256':h})
d={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Modules agent; Root executed canonical copy of Applied authored identity offer','candidate':a['candidate'],'candidate_ledger':a['candidate'],'candidate_promotions':a['candidate_promotions'],'reviewed_offer':ref(P),'original_reviewed_offer':meta['original_final_offer'],'original_independent_identity_peer':a['final_independent_candidate_mapping_peer'],'entire_original_independent_identity_peer_body_and_time':peer,'entire_original_helper_code_peer_body_and_time':code,'actual_canonical_identity_copy':ref(actualp),'whole_canonical_offer_inverse_restores_original_b98f_exact':True,'candidate_and_promotions_bytes_exact31b6_and72ee':True,'entire_candidate_inverse_restores_installed26_ledger_and_promotions':True,'all128_exercises2059_owned_records468claims1954material312proof_metadata_original_body_time_exact':True,'copied_original_aliases':42,'unchanged_root_evidence_refs':150,'active_required_artifacts':192,'new_proof_sources':0,'new_material_or_exercise_decisions':0,'all1167_selected31_current55_assets5_live26_owners8_new_sources_exact':True,'closed_evidence_sha256':closed,'scope':'Read-only exact output mechanics and original offer/candidate/promotions inverses. Original acf2 independent decisions/body/time and code-reader failures retained; canonical typed candidate refs only. No owner installation, compiler, aggregate or global selection claim.'}
with O.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'status':'passed','result':ref(O),'candidate':a['candidate'],'new_proof_sources':0}))
