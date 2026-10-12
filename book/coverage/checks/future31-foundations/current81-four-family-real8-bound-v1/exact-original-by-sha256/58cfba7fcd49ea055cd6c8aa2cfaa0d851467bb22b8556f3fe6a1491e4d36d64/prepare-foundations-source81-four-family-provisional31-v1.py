"""Unexecuted candidate author: no live/canonical/owner/publication writes.

The eventual fresh-context wrapper must guard actual Source81 inputs. This
provisional output requests actual canonical pairs and a final mapping review.
"""
from pathlib import Path
import copy, hashlib, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
DEST=Path('/tmp/foundations-source81-four-family-provisional31-v1')
BASE=ROOT/'book/coverage/checks/future30-foundations/current79-completed90-association-v1/foundations30-completed90-current79-pair-bound-candidate-v1.json'
BASE_SHA='4e84206199aa241e1e4ee95f59062bcbe78035bb6443281e398a02c1b3f3ae03'
SUPPLY=Path('/tmp/foundations-four-compiled-families-supply31-v1.json')
SUPPLY_SHA='ce0e312879506aaf79933dce0cf6ecfcaa60575f184f1b690639e3dc01133dbb'
INV=ROOT/'book/coverage/inventory-after-correction81.json'
INV_SHA='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 return p
def put(p,d):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
assert not DEST.exists()
assert sha(BASE)==BASE_SHA and sha(SUPPLY)==SUPPLY_SHA and sha(INV)==INV_SHA
old=json.loads(BASE.read_bytes());candidate=copy.deepcopy(old)
supply=json.loads(SUPPLY.read_bytes());inventory=json.loads(INV.read_bytes())
units={r['key']:r for r in inventory['material_source_units']}
assert inventory['counts']['exercises']==556 and inventory['counts']['material_source_units']==12774
assert len(supply['families'])==4 and supply['direct_public_theorems']==41
patches=[]
def change(container,key,value,pointer):
 if container[key]!=value:
  patches.append({'pointer':pointer,'before':copy.deepcopy(container[key]),'after':copy.deepcopy(value)})
  container[key]=copy.deepcopy(value)
for name,digest in list(candidate['source_sha256'].items()):
 if name.startswith('SafeLearning/'):
  assert name in inventory['source_sha256']
  change(candidate['source_sha256'],name,inventory['source_sha256'][name],['source_sha256',name])
for field in ['exercises','material_claims','surrounding_prose_reviews']:
 for i,row in enumerate(candidate[field]):
  if isinstance(row,dict) and row.get('source') in inventory['source_sha256']:
   name=row['source']
   if 'source_sha256' in row:change(row,'source_sha256',inventory['source_sha256'][name],[field,i,'source_sha256'])
   keys=row.get('source_unit_keys',[])
   if row.get('locator')=='::node-421' and name=='SafeLearning/primer-linalg.html':
    unit=units['primer-linalg.html::node-421']
    for own,invkey in [('source_text','source_text'),('source_text_sha256','text_sha256')]:
     if own in row:change(row,own,unit[invkey],[field,i,own])
approved=['primer-linalg.html::node-421','primer-basics.html::node-1306','primer-basics.html::node-1437','primer-basics.html::node-1452']
descriptions={
 'spectral_induction11':'Entire corrected proof sketch: real unit eigenvector, invariant orthogonal complement and restricted symmetric map, one-lower finrank, actual finite-dimensional dimension induction, and arbitrary full eigenspace orthonormal-basis extension. Nonunique orthogonal eigenvector matrix is correctly scoped to n>=1; dimension0 uniqueness retained.',
 'logcube_crossover13':'Entire1306: actual little-o limits, unique strict24M-to24.5M upper crossing with the every-real-point finite interval comparison and no later recross, plus finite-budget modifications preserving little-o. Numerical range is proved separately from asymptotic behavior.',
 'explorer_captions7':'Both complete1437/1452 captions: true shifted invariant-domain Banach posterior bound, exact geometric fractions and first1percent horizon including gamma0, actual source widget/JS colors and off-plot marker scope, with independent exact checks of all200 admitted slider horizons.',
}
families=[]
for f in supply['families']:
 checked(f['final_actual_passed_TMP_source'])
 peerref=f.get('independent_full_math_scope_peer')
 peer=json.loads(checked(peerref).read_bytes()) if peerref else None
 if peer:assert peer['status'].startswith('passed') and peer.get('errors',[])==[]
 wholekeys=(['primer-linalg.html::node-421'] if f['id']=='spectral_induction11' else f['approved_current_whole_keys'])
 if f['id']=='growth_examples_logdet10':wholekeys=[]
 for key in wholekeys:
  assert key in approved
  matches=[(i,r) for i,r in enumerate(candidate['material_claims']) if key in r.get('source_unit_keys',[]) and r['status']=='pending']
  assert len(matches)==1,key
  i,row=matches[0]
  revised=copy.deepcopy(row)
  revised.update({'status':'proved','kind':'independently_reviewed_prospective31_entire_literal_mathematics','statement_in_prose':descriptions[f['id']],
   'lean_declarations':f['public_theorem_names'],'remaining_gaps':[],
   'hypotheses':'Exact current Source81 full literal domains and all explicitly stated theorem hypotheses, including the dimension/radius/index conditions assessed by the full mathematical peer.',
   'correspondence':'Exact full-source and whole-literal independent semantic approval; Source80 actual correction supplies421 identity. This is a prospective candidate row, with actual canonical pairing and final mapping still required.',
   'independent_full_scope_peer':peerref})
  change(candidate['material_claims'],i,revised,['material_claims',i])
 family=copy.deepcopy(f)
 family.update({'requested_current81_whole_keys':wholekeys,'actual_Source80_qualifier_applied':f['id']=='spectral_induction11',
   'canonical_installation_and_true_standalone_named_pairs_pending':True,'independent_final_mapping_pending':True})
 families.append(family)
assert candidate['proof_files']==old['proof_files'] and candidate['proof_sha256']==old['proof_sha256']
assert candidate['exercises']==old['exercises'] or all(
 {k:v for k,v in a.items() if k!='source_sha256'}=={k:v for k,v in b.items() if k!='source_sha256'}
 for a,b in zip(candidate['exercises'],old['exercises']))
counts={s:sum(r['status']==s for r in candidate['material_claims']) for s in ['not_a_formal_claim','proved','pending']}
change(candidate['counts'],'material_claim_statuses',counts,['counts','material_claim_statuses'])
metadata={'status':'draft_actual_Source81_identity_and_four_TMP_families_pending_canonical_pairs_and_final_mapping',
 'original_whole_owner30':ref(BASE),'actual_source81_inventory':ref(INV),'original_four_family_supply':ref(SUPPLY),
 'actual_source80_81_transaction':ref('reports/full-coverage/source80-81-corrections-application-v3.json'),
 'families':families,'direct_new_source_count':4,'direct_new_public_theorems':41,'direct_new_definitions':4,
 'candidate_whole_keys':approved,'pending_full_review_keys':['primer-basics.html::node-1271'],
 'all_old289_selected_foundation_sources_retained':True,'all119_exercises_and_old_proved_rows_retained_except_exact_source_identity':True,
 'new_proof_files_deliberately_not_added_before_true_canonical_pairs':True,'canonical_pairs_pending':True,
 'current_owner_or_new_selected_aggregate_or_publication_installation_claimed':False,'coverage_complete':False}
candidate['current31_source81_four_family_draft']=metadata
inverse=copy.deepcopy(candidate);del inverse['current31_source81_four_family_draft']
for patch in reversed(patches):
 parent=inverse
 for item in patch['pointer'][:-1]:parent=parent[item]
 assert parent[patch['pointer'][-1]]==patch['after']
 parent[patch['pointer'][-1]]=patch['before']
assert inverse==old
DEST.mkdir()
out=DEST/'foundations31-current81-identity-four-family-provisional-candidate-v1.json';put(out,candidate)
interface=DEST/'foundations31-current81-identity-four-family-exact-inverse-v1.json';put(interface,{'status':'exact_static_candidate_forward_inverse_preserving_original_owner30_semantics','original':ref(BASE),'candidate':ref(out),'patches':patches,'appended_field':'current31_source81_four_family_draft','original_body_sha256':BASE_SHA,'whole_candidate_current_installation_claimed':False,'canonical_pairs_pending':True})
offer=DEST/'foundations31-current81-four-family-provisional-offer-v1.json';put(offer,{'status':'prepared_provisional_only_not_ready_for_owner_installation','candidate':ref(out),'exact_inverse':ref(interface),'metadata':metadata,'whole_review_pending':['primer-basics.html::node-1271'],'no_current_writes':True,'coverage_complete':False})
print(json.dumps({'candidate':ref(out),'interface':ref(interface),'offer':ref(offer),'candidate_material_statuses':counts}))
