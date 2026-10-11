from pathlib import Path
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1';OLD=B/'modules28-current60-five-source-pair-bound-offer-draft-v5.json';NEW=B/'modules28-current60-five-source-final-offer-v1.json';PEER=R/'book/coverage/checks/future28-core/modules28-current60-final-pair-bound-independent-applied-review-v1.json'
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)),'sha256':h(p)}
assert h(OLD)=='e59929813701ed182418e8d4ae34210f4f45b4dee3a00bac8f64ff456d372996' and h(PEER)=='551b46799ca996cf2f136c8a0f6cf2b17e56adaccad6dd2ffa107a85eb7c45e6' and not NEW.exists()
old=json.loads(OLD.read_bytes());peer=json.loads(PEER.read_bytes());d=copy.deepcopy(old)
assert peer['status']=='passed_independent_exact_modules28_current60_five_source_pair_bound_candidate_mechanics' and peer['errors']==[] and peer['candidate']==old['candidate']
assert Path(peer['offer']['file'])==OLD and peer['offer']['sha256']==h(OLD) and peer['entire_forward_and_inverse_exact'] is True
assert (peer['new_source_count'],peer['new_public_declarations'],peer['genuine_actual_pair_count'],peer['whole_exercises'],peer['whole_material_units'])==(5,153,10,4,26)
native=json.loads((R/peer['actual_finalizer']['file']).read_bytes());assert type(native['actual_exit_code']) is int and native['actual_exit_code']==0 and native['protection_errors']==[]
assert h(R/old['candidate']['file'])==old['candidate']['sha256']=='2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715'
closure=d['required_evidence_artifacts_sha256']
def add(n,s):
 p=R/n;assert not Path(n).is_absolute() and '..' not in Path(n).parts and p.resolve().is_relative_to(R) and not p.is_symlink() and h(p)==s,n
 assert n not in closure or closure[n]==s;closure[n]=s
for n,s in peer['closed_evidence_sha256'].items():add(n,s)
for r in [ref(PEER),peer['original_byte_alias_catalog'],peer['actual_finalizer']]:add(r['file'],r['sha256'])
for v in range(2,6):
 r=ref(B/f'modules28-current60-five-source-pair-bound-offer-draft-v{v}.json');add(r['file'],r['sha256'])
repair_catalogs=[]
for dirname,name in [('commissioning-direct-closure-originals-v3','original-closed-byte-aliases-v3.json'),('primary-real-root-closure-originals-v4','original-closed-byte-aliases-v4.json'),('primary-absolute-alias-closure-originals-v5','original-closed-byte-aliases-v5.json')]:
 p=B/dirname/name;r=ref(p);add(r['file'],r['sha256']);repair_catalogs.append(r)
 for original,a in json.loads(p.read_bytes())['original_closed_byte_aliases'].items():add(a['file'],a['sha256']);d['original_closed_byte_aliases'][original]=a
for original,a in peer['original_closed_byte_aliases'].items():add(a['file'],a['sha256']);d['original_closed_byte_aliases'][original]=a
mutable={'book/coverage/'+n+'.json' for n in ['core','foundations','applied','modules','applied-promotions']}
assert not mutable.intersection(closure)
for n,s in closure.items():add(n,s)
d['status']='passed_current60_modules28_five_source_actual_pair_offer_independently_reviewed';d['final_independent_candidate_mapping_peer']=ref(PEER);d['final_independent_mapping_actual']=peer['actual_finalizer'];d['original_final_mapping_draft_offer']=ref(OLD);d['original_closure_repair_catalogs']=repair_catalogs;d['final_mapping_scope']='Independent canonical pair/declaration/whole claim mapping and exact forward/inverse closure, preserving the exact original mathematical peers and genuine failed readers. Candidate unchanged; Root owner/selection/aggregate/publication execution remains separate.'
assert d['candidate']==old['candidate'] and d['proof_files']==old['proof_files'] and d['whole976_approved'] is False
with NEW.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'final_offer':ref(NEW),'candidate':d['candidate'],'independent_peer':ref(PEER),'actual_independent_mapping':peer['actual_finalizer'],'closed_evidence_count':len(closure),'original_alias_count':len(d['original_closed_byte_aliases'])}))
