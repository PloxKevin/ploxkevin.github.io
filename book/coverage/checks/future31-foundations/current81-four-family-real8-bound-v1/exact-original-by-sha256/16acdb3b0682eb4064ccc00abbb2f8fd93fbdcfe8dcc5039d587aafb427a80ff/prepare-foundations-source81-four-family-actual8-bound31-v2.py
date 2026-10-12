"""Unexecuted candidate author: no live/canonical/owner/publication writes.

The eventual fresh-context wrapper must guard actual Source81 inputs. This
output binds the actual canonical pairs and requests a final mapping review.
"""
from pathlib import Path
import copy, hashlib, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
DEST=Path('/tmp/foundations-source81-four-family-actual8-bound31-v2')
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
approved=['primer-linalg.html::node-421','primer-basics.html::node-1306','primer-basics.html::node-1271','primer-basics.html::node-1437','primer-basics.html::node-1452']
descriptions={
 'spectral_induction11':'Entire corrected proof sketch: real unit eigenvector, invariant orthogonal complement and restricted symmetric map, one-lower finrank, actual finite-dimensional dimension induction, and arbitrary full eigenspace orthonormal-basis extension. Nonunique orthogonal eigenvector matrix is correctly scoped to n>=1; dimension0 uniqueness retained.',
 'logcube_crossover13':'Entire1306: actual little-o limits, unique strict24M-to24.5M upper crossing with the every-real-point finite interval comparison and no later recross, plus finite-budget modifications preserving little-o. Numerical range is proved separately from asymptotic behavior.',
 'growth_examples_logdet10':'Entire1271: exact natural3n^2+10n+5 Theta bounds with threshold10; genuine all-positive-power logarithm and all-real-power exponential little-o; analytic matrix determinant/logarithm second-order Taylor remainder on the actual linked positive-definite domain; and positive-step O(eta) means a constant independent of eta. No whole linked algorithm guarantee inferred.',
 'explorer_captions7':'Both complete1437/1452 captions: true shifted invariant-domain Banach posterior bound, exact geometric fractions and first1percent horizon including gamma0, actual source widget/JS colors and off-plot marker scope, with independent exact checks of all200 admitted slider horizons.',
}
families=[]
for original_family in supply['families']:
 f=copy.deepcopy(original_family)
 if f['id']=='growth_examples_logdet10':
  f['independent_full_math_scope_peer']=ref('book/coverage/checks/future31-applied/growth10-whole-independent-v1/growth10-entire-current1271-independent-applied31-peer-v1.json')
  assert f['independent_full_math_scope_peer']['sha256']=='e3f153e9cb87a1f326c0a7c9bc2cce6de1a7f3b8458e1d6dc1a87644c6ecb9d4'
  f['approved_current_whole_keys']=['primer-basics.html::node-1271'];f['pending_current_whole_keys']=[];f['full_review_pending']=False
 checked(f['final_actual_passed_TMP_source'])
 peerref=f.get('independent_full_math_scope_peer')
 peer=json.loads(checked(peerref).read_bytes()) if peerref else None
 if peer:assert peer['status'].startswith('passed') and peer.get('errors',[])==[]
 wholekeys=(['primer-linalg.html::node-421'] if f['id']=='spectral_induction11' else f['approved_current_whole_keys'])
 if f['id']=='growth_examples_logdet10':
  assert peer['entire_node_decision']['entire_exact_literal_approved'] is True
  assert peer['entire_node_decision']['remaining_mathematical_gaps']==[]
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
   'canonical_installation_and_true_standalone_named_pairs_pending':False,'canonical_installation_performed':True,'independent_final_mapping_pending':True})
 families.append(family)
assert candidate['proof_files']==old['proof_files'] and candidate['proof_sha256']==old['proof_sha256']
# Bind the four actual per-file pairs only after the whole12-command Root batch closed.
READINESS=ROOT/'book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
assert sha(READINESS)=='c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
ready=json.loads(READINESS.read_bytes());assert ready['status']=='passed_actual_reviewed31_canonical_standalone_and_named_pairs_unselected' and ready['errors']==[]
assert ready['source_count']==6 and ready['actual_compiler_command_count']==12
import re
proofmeta={}
for f in families:
 target=f['prospective_canonical_target'];source=checked(f['final_actual_passed_TMP_source'])
 assert sha(ROOT/target)==sha(source)
 rootrow=next(r for r in ready['sources'] if r['canonical_source']==target)
 assert rootrow['public_theorem_count']==f['direct_public_theorem_count']
 theorem_names=[d['name'] for d in rootrow['public_declarations'] if d['kind'] in ['theorem','lemma']]
 public_names=[d['name'] for d in rootrow['public_declarations']]
 assert theorem_names==f['public_theorem_names'] and len(public_names)==f['direct_public_theorem_count']+f['direct_public_definition_count']
 pairs={}; evidence={}
 for kind in ['standalone','named']:
  pair=copy.deepcopy(next(p for p in ready['actual_paired_records'] if p['source']['file']==target and p['kind']==kind))
  assert pair['actual_exit_code']==0 and pair['source']['sha256']==sha(source)
  record=json.loads(checked(pair['actual_record']).read_bytes());raw=checked(pair['raw_log']);snap=checked(pair['source_snapshot'])
  assert type(record['exit_code']) is int and record['exit_code']==0 and record['source_unchanged'] is True
  assert record['source']==target and record['source_sha256_before']==record['source_sha256_after']==sha(source)
  assert snap.read_bytes()==source.read_bytes() and record['log_sha256']==sha(raw)
  base=Path(target).stem
  expected=['lake','env','lean','SafeLearning/'+base+'.lean'] if kind=='standalone' else ['lake','build','SafeLearning.'+base]
  assert record['command']==expected and record['actual_workdir']==str(ROOT/'verification/lean')
  assert record['elapsed_seconds']>0 and record['checked_at_utc']
  pair['original_checked_at_utc']=record['checked_at_utc'];pair['original_elapsed_seconds']=record['elapsed_seconds']
  pair['new_compiler_started_by_this_binding']=False
  for field in ['actual_record','raw_log','source_snapshot']:
   pair[field]=ref(checked(pair[field]));evidence[pair[field]['file']]=pair[field]['sha256']
  invocation=ref(READINESS.parent/(base+'-'+kind+'-helper-invocation.log'));pair['actual_helper_invocation_log']=invocation
  evidence[invocation['file']]=invocation['sha256'];pairs[kind]=pair
 proofmeta[target]={'sha256':sha(source),'theorem_count':len(theorem_names),'public_theorem_names':theorem_names,'mapped_named_declarations':public_names,'actual_pair':pairs,'evidence_sha256':evidence}
 oldfiles=copy.deepcopy(candidate['proof_files']);oldshas=copy.deepcopy(candidate['proof_sha256'])
 assert target not in oldfiles and target not in oldshas
 change(candidate,'proof_files',oldfiles+[target],['proof_files'])
 change(candidate,'proof_sha256',{**oldshas,target:sha(source)},['proof_sha256'])
assert len(proofmeta)==4 and sum(m['theorem_count'] for m in proofmeta.values())==41
assert sum(len(m['mapped_named_declarations']) for m in proofmeta.values())==45
assert candidate['proof_files'][:len(old['proof_files'])]==old['proof_files']
assert all(candidate['proof_sha256'][n]==h for n,h in old['proof_sha256'].items())
assert candidate['exercises']==old['exercises'] or all(
 {k:v for k,v in a.items() if k!='source_sha256'}=={k:v for k,v in b.items() if k!='source_sha256'}
 for a,b in zip(candidate['exercises'],old['exercises']))
counts={s:sum(r['status']==s for r in candidate['material_claims']) for s in ['not_a_formal_claim','proved','pending']}
change(candidate['counts'],'material_claim_statuses',counts,['counts','material_claim_statuses'])
metadata={'status':'actual_Source81_identity_four_canonical_source_eight_true_pair_bound_final_mapping_review_pending',
 'original_whole_owner30':ref(BASE),'original_provisional_pending_offer':ref('/tmp/foundations-source81-four-family-provisional31-v1/foundations31-current81-four-family-provisional-offer-v1.json'),'original_provisional_preparation_native':ref('/tmp/foundations-source81-four-family-provisional31-preparation-actual-v1.json'),'actual_source81_inventory':ref(INV),'original_four_family_supply':ref(SUPPLY),
 'actual_source80_81_transaction':ref('reports/full-coverage/source80-81-corrections-application-v3.json'),
 'families':families,'direct_new_source_count':4,'direct_new_public_theorems':41,'direct_new_definitions':4,
 'candidate_whole_keys':approved,'pending_full_review_keys':[],
 'all_old289_selected_foundation_sources_retained':True,'all119_exercises_and_old_proved_rows_retained_except_exact_source_identity':True,
 'new_proof_files_added_only_after_true_canonical_pairs':True,'canonical_pairs_pending':False,'proof_files':proofmeta,'actual_common12_readiness':ref(READINESS),
 'current_owner_or_new_selected_aggregate_or_publication_installation_claimed':False,'coverage_complete':False}
candidate['current31_source81_four_family_draft']=metadata
inverse=copy.deepcopy(candidate);del inverse['current31_source81_four_family_draft']
for patch in reversed(patches):
 parent=inverse
 for item in patch['pointer'][:-1]:parent=parent[item]
 assert parent[patch['pointer'][-1]]==patch['after']
 parent[patch['pointer'][-1]]=patch['before']
assert inverse==old
assert (json.dumps(inverse,indent=2)+'\n').encode()==BASE.read_bytes()
DEST.mkdir()
out=DEST/'foundations31-current81-real8-pair-bound-candidate-v2.json';put(out,candidate)
interface=DEST/'foundations31-current81-real8-pair-bound-exact-inverse-v2.json';put(interface,{'status':'exact_static_candidate_forward_inverse_preserving_original_owner30_semantics','original':ref(BASE),'candidate':ref(out),'patches':patches,'appended_field':'current31_source81_four_family_draft','original_body_sha256':BASE_SHA,'whole_candidate_current_installation_claimed':False,'canonical_pairs_pending':False})
offer=DEST/'foundations31-current81-real8-pair-bound-final-offer-v2.json';put(offer,{'status':'actual_four_source_eight_pair_bound_current81_final_mapping_review_pending','candidate':ref(out),'exact_inverse':ref(interface),'metadata':metadata,'whole_review_pending':[],'no_current_writes':True,'coverage_complete':False})
print(json.dumps({'candidate':ref(out),'interface':ref(interface),'offer':ref(offer),'candidate_material_statuses':counts}))
