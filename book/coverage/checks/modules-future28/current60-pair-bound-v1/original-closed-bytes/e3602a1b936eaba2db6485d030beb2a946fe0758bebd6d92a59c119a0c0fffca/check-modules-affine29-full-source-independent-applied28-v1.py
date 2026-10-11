from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/modules-affine-ibp28-full-literal-review-request-v2.json');OUT=Path('/tmp/modules-affine29-independent-applied-findings28-v1.json');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(REQUEST)=='61abb0451986b52e8c19fce4e40fc32fe082a78021a8158d94c7aa3a866aafad'
d=json.loads(REQUEST.read_bytes());closed={str(REQUEST):sha(REQUEST)}
def refs(x):
 if isinstance(x,dict):
  if type(x.get('file'))is str and type(x.get('sha256'))is str:
   p=Path(x['file']);assert p.is_file() and sha(p)==x['sha256'],str(p)
   if 'bytes' in x:assert p.stat().st_size==x['bytes'],str(p)
   if str(p) in closed:assert closed[str(p)]==x['sha256']
   closed[str(p)]=x['sha256']
  for v in x.values():refs(v)
 elif isinstance(x,list):
  for v in x:refs(v)
refs(d)
source=Path(d['source']['file']).read_text();names=['SafeLearning.CompleteModulesAffineIBP28.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
assert names==d['public_theorem_names'] and len(names)==d['public_theorem_count']==29
oldsource=Path('/tmp/CompleteModulesAffineIBP28-draft-v3.lean').read_text();a=source.index('def standardUpperWitness');b=source.index('abbrev V :=',a);assert source[:a]+source[b:]==oldsource
assert not any(re.search(r'\b(sorry|axiom|admit)\b',l) for l in source.splitlines() if not l.lstrip().startswith('--'))
trials=[]
for k,code in [(1,1),(2,1),(3,0),(4,0)]:
 p=Path('/tmp/modules-affine-ibp28-trial'+str(k)+'.json');x=json.loads(p.read_bytes());assert type(x['actual_exit_code'])is int and x['actual_exit_code']==code and type(x['actual_runner_exit_code'])is int and x['actual_runner_exit_code']==code
 assert x['protection_errors']==[] and x['source_unchanged']is True
 assert x['protected_selected27_proof_sources']==1175 and x['unchanged_current55_book_assets']==31 and x['unchanged_installed27_live_owners']==5
 log=Path(x['raw_log']);snap=Path(x['source_snapshot']);assert sha(log)==x['raw_log_sha256'] and sha(snap)==x['source_snapshot_sha256']==x['source_sha256_after']==x['source_sha256_before']
 assert x['actual_command']==['lake','env','lean',x['source']] and x['actual_workdir']==str(ROOT/'verification/lean')
 if code==0:assert log.read_bytes()==b''
 for q in [p,log,snap,Path(x['source'])]:closed[str(q)]=sha(q)
 trials.append({'actual_record':{'file':str(p),'sha256':sha(p)},'actual_exit_code':code,'original_started_at_utc':x['started_at_utc'],'original_finished_at_utc':x['finished_at_utc'],'raw_log':{'file':str(log),'sha256':sha(log)},'source_snapshot':{'file':str(snap),'sha256':sha(snap)}})
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes());assert sha(ROOT/'book/coverage/inventory.json')==d['inventory']['sha256']
exercises={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']};key='verification.html::exercise-15';assert exercises[key]==d['full_exercise_inventory_literal']
old_ex=next(x for x in owner['exercises'] if x['inventory_key']==key);assert old_ex==d['full_original_owner_exercise']
for x in d['full_material_inventory_literals']:assert units[x['key']]==x
raw=(ROOT/'SafeLearning/verification.html').read_text();context='\n'.join(raw.splitlines()[114:134])+'\n';exercise_context='\n'.join(raw.splitlines()[795:811])+'\n'
primary=[ROOT/'verification/lean/SafeLearning/CompleteFoundationsBalancedSensorReconstruction27.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Basic/Sign/Defs.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Basic/Sign/Basic.lean']
for p in primary:closed[str(p)]=sha(p)
parser_peer=Path('/tmp/modules-zero-sign-source58-independent-foundations-parser28-v2.json');assert sha(parser_peer)=='11eaf14376112e862a9d6a91af03e6fe68be81ee05d25615fdee726750f7984e';pp=json.loads(parser_peer.read_bytes());assert pp['status']=='passed_independent_source58_zero_sign_wording_and_isolated_full29_parser' and pp['errors']==[]
assert pp['both_parser_ROOT_and_OUT_isolated']is True and pp['exact_forward_and_inverse_whole_source_passed']is True
assert pp['fresh_parser_literal_changes']=={'exercises':[],'material_source_units':['verification.html::node-193']}
closed[str(parser_peer)]=sha(parser_peer)
for n,h in pp['closed_evidence_sha256'].items():assert sha(Path(n))==h;closed[n]=h
proposal=Path('/tmp/modules-ibp-zero-sign-source58-proposal28-v1/modules-ibp-zero-sign-source58-proposal28-v1.json');pr=json.loads(proposal.read_bytes());refs(pr);assert raw.count(pr['before_raw_fragment'])==1
proposed=Path(pr['proposed_source']['file']).read_text();assert proposed==raw.replace(pr['before_raw_fragment'],pr['after_raw_fragment'],1) and proposed.replace(pr['after_raw_fragment'],pr['before_raw_fragment'],1)==raw
# This exact analytical one-variable counterexample retains the current193 issue, rather than changing sign(0).
assert 0*(-1)==0*0==0*1==0 and 0 not in [-1,1]
core='SafeLearning.CompleteModulesAffineIBP28.'
groups=[
 {'id':'finite_original_matrix_center_radius_and_triangle_chain','approved':True,'hypotheses':['Finite real input coordinates; coordinatewise ordered finite endpoints lo<=hi; genuine affine action W.mulVec+b.'],'lean_declarations':[n for n in names[:4]],'correspondence':'Exact box iff absolute center-radius deviation, derived nonnegative radii, the internal actual finite-sum affine decomposition and triangle/weighted radius inequalities, and both output interval formulas. No independent-coordinate reachability for multiple output rows is inferred.','missing_clauses':[]},
 {'id':'genuine_coordinate_extrema_standard_sign_zero_and_endpoint_corners','approved':True,'hypotheses':['The ordered rectangular input box includes each endpoint; the attaining witness is row-dependent. Standard SignType.sign(0) is0.'],'lean_declarations':names[4:15],'correspondence':'True IsGreatest/IsLeast coordinate extrema, feasible endpoint witnesses and explicit every-coordinate endpoint equalities. Separate standard-sign(0)=0 feasible witnesses attain exact upper/lower values through self_mul_sign; zero weights contribute0. Current193 falsely calls the centered zero-weight witness a corner when radius>0; the prospective58 wording distinguishes it from endpoint choices.','missing_clauses':[]},
 {'id':'true_matrix_diamond_joint_unreachability_and_next_layer','approved':True,'hypotheses':['Exact matrix [[1,1],[1,-1]], zero bias, input[-1,1]^2.'],'lean_declarations':names[15:22],'correspondence':'Actual matrix action, exact center/radius/IBP box, both directions of image iff |z0|+|z1|<=2 via explicit inverse, four source corner images, unreachable IBP(2,2), and genuine attained greatest next-row maxima2 versus4. The diamond characterization and four explicit vertices give the source rotated square; no broader independence or depth-growth claim is inferred.','missing_clauses':[]},
 {'id':'genuine_determinant_lebesgue_and_euclidean_areas','approved':True,'hypotheses':['Two-dimensional real Lebesgue volume and the canonical volume-preserving Euclidean coordinate equivalence; exact determinant-2 is nonzero.'],'lean_declarations':names[21:],'correspondence':'Actual Icc product volumes4/16, measurable diamond and invertible-matrix preimage identity, Mathlib determinant change of volume giving image8, true ratio2, and actual Euclidean volumes16/8. Neither area appears as a supplied hypothesis.','missing_clauses':[]}
]
material=[]
for n in [191,192,195,1157,1161,1162]:
 k='verification.html::node-'+str(n);old=[x for x in owner['material_claims'] if k in x.get('source_unit_keys',[])];material.append({'inventory_key':k,'entire_inventory_record':units[k],'entire_original_owner_claims':old,'whole_unit_approved':True,'missing_clauses':[],'hypotheses':groups[0]['hypotheses']+(['Exact source two-dimensional matrix/box for worked part(b), genuine Lebesgue area.'] if n in [1157,1162] else []),'lean_declarations':names,'correspondence':'Whole literal read in the full page/exercise context. The actual declared center/radius, finite-matrix, standard-sign, diamond, extremum and volume routes cover every clause in the relevant literal, as grouped above.'})
virtual=pr['entire_changed_records']['verification.html::node-193']['entire_proposed_inventory_record']
result={'status':'passed_independent_full_affine_ibp29_body_literal_review28','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Applied independent full-source reviewer','request':{'file':str(REQUEST),'sha256':sha(REQUEST)},'source':d['source'],'all29_full_bodies_and_definitions_read':True,'whole_exercise_records':[{'inventory_key':key,'entire_inventory_record':exercises[key],'entire_original_owner_exercise':old_ex,'whole_exercise_approved':True,'missing_clauses':[],'components':groups,'lean_declarations':names,'hypotheses':['Finite genuine real affine layer and coordinatewise ordered closed input box; exact two-dimensional example matrix/zero bias/[-1,1]^2; row-specific standard-sign witnesses; genuine product and Euclidean Lebesgue areas.']}],'material_units':material,'current193_disposition':{'inventory_key':'verification.html::node-193','entire_inventory_record':units['verification.html::node-193'],'whole_unit_approved':False,'remaining_gaps':['The standard sign(0)=0 attaining point need not be a box corner; current55 exact literal must be corrected before whole193 promotion.'],'analytical_counterexample':pr['analytical_counterexample'],'mathematical_extremum_and_sign_components_approved':True},'prospective_source58_unit193':{'entire_proposed_inventory_record':virtual,'whole_unit_approved_under_proposed_literal':True,'missing_clauses':[],'conditional_on_root_later_actual_source58':True,'correspondence':'Corrected full literal uses standard sign0 centered feasible attaining point, then independently replaces zero-weight coordinates by endpoints to form a true corner without changing any row term. The actual endpoint and standard-sign source bodies, finite-sum proof, and primitive zero-weight multiplication verify this qualification.','isolated_parser_peer':{'file':str(parser_peer),'sha256':sha(parser_peer)}},'node196_whole_approved':False,'node196_remaining_scope':['General monotone activation, exact zonotope/independence, citation and broad depth assertions are outside this full source packet.'],'full_source_context':context,'full_exercise_context':exercise_context,'prior_v3_23_body_bytes_preserved_exact':True,'actual_original_trial_histories':trials,'primary_api_scope_read':['Complete selected BalancedSensorReconstruction27 source142lines; the exact invertible matrix determinant measure-map declaration/body and PiLp Euclidean volume-preserving declaration/body; complete used sign definition/coercions/zero and self_mul_sign theorem bodies.'],'closed_evidence_sha256':closed,'canonical_pair_or_new_owner_mapping_or_publication_claimed':False,'scope':'Independent full29 semantic reading and mechanical exact current-source/body/native binding. Whole current Ex15.1 plus6 requested whole physical units approved; current193 remains pending and prospective58 exact corrected193 approved only as a virtual clause. Genuine standalone TMP trials are retained; no canonical named/current owner/source/selected proof writes.'}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'findings':str(OUT),'sha256':sha(OUT),'public_names':len(names),'whole_units':len(material),'whole_exercise':key,'closed_refs':len(closed)}))
