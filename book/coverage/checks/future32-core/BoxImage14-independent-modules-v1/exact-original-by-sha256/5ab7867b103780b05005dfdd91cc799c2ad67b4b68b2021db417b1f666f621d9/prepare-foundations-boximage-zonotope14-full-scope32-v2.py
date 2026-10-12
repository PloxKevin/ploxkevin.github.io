from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future32-foundations/boximage-zonotope14-full-scope-v2';assert not B.exists()
S=Path('/tmp/CompleteFoundationsBoxImageZonotope32-draft-v3.lean');V=R/'book/coverage/inventory-after-correction81.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def retain(n):
 p=path(n);r=ref(p)
 if p.is_relative_to(R) and '.lake' not in p.parts and str(p.relative_to(R))!='SafeLearning/primer-linalg.html':refs[str(p)]=r;return r
 t=B/'exact-original-by-sha256'/r['sha256']/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:t.write_bytes(p.read_bytes())
 a=ref(t);refs[str(p)]=a;return a
assert sha(S)=='1280575640190071c5e2233e35bbc6d340408f4b11066d90a91b38ad09e5abdb'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
assert path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes()
inv=json.loads(V.read_bytes());key='primer-linalg.html::node-332';unit=next(r for r in inv['material_source_units'] if r['key']==key)
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if key in r.get('source_unit_keys',[])];assert len(rows)==1 and rows[0]['status']=='pending'
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
s=S.read_text();names=declarations(s);ts=[r['name'] for r in names if r['kind']=='theorem'];assert len(names)==18 and len(ts)==14 and sum(r['kind']=='def' for r in names)==4
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
hist=[]
for kind,p in [('source_trial1','/tmp/foundations-box-image-zonotope13-installed31-trial1.json'),('source_trial2','/tmp/foundations-box-image-zonotope14-installed31-trial2.json'),('source_trial3','/tmp/foundations-box-image-zonotope14-installed31-trial3.json'),('all14_standard_axiom_inspection','/tmp/foundations-box-image-zonotope14-all-public-axioms-installed31-actual-v1.json')]:
 n=json.loads(path(p).read_bytes());assert n['actual_exit_code']==n['actual_runner_exit_code'] and n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after'] and sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'history_role':kind,'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),'original_body_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [h['actual_exit_code'] for h in hist]==[1,1,0,0] and hist[2]['source']['sha256']==sha(S)
axraw=path('/tmp/foundations-box-image-zonotope14-all-public-axioms-installed31-actual-v1.log').read_text();ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axraw,re.S)
assert [name for name,_ in ax]==ts and all(set(x.strip() for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'} for _,v in ax)
selected={n:retain('verification/lean/SafeLearning/'+n) for n in ['CompleteModulesAffineIBP28.lean','CompleteFoundationsBalancedSensorReconstruction27.lean']}
assert selected['CompleteModulesAffineIBP28.lean']['sha256']=='cc40073489615ede8e9c52668137da6b718d19cedfb41d6b1a865465788c064d'
oldpeer=retain('book/coverage/checks/future28-core/current60-canonical-pairs-v1/original-closed-bytes/1b9ec81925c50f35874fd97df12c0de552b46a4dd03ad4c7ba0501f7b9da3e7c/modules-affine29-independent-applied-full-source-review28-v2.json')
old=json.loads(path(oldpeer['file']).read_bytes());assert old['errors']==[] and old['node196_remaining_scope']
meta=owner if 'verification/lean/SafeLearning/CompleteModulesAffineIBP28.lean' in owner.get('proof_sha256',{}) else json.loads(path('book/coverage/modules.json').read_bytes())
# Close only the exact existing proof metadata and immutable historical records, not another whole owner snapshot.
proof=meta['proof_files']['verification/lean/SafeLearning/CompleteModulesAffineIBP28.lean'];assert proof['sha256']==selected['CompleteModulesAffineIBP28.lean']['sha256']
pairrefs=[]
for p in proof['actual_pair']:
 for k in ['actual_record','raw_log','source_snapshot']:
  r=p[k];assert sha(r['file'])==r['sha256'];pairrefs.append(retain(r['file']))
providers={n:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n) for n in [
 'Analysis/Normed/Group/Constructions.lean','Analysis/Normed/Lp/PiLp.lean','Analysis/InnerProductSpace/PiL2.lean',
 'Algebra/Group/Pointwise/Set/BigOperators.lean','Analysis/Convex/Segment.lean','LinearAlgebra/Span/Basic.lean',
 'LinearAlgebra/Matrix/Determinant/Basic.lean','Data/Matrix/Mul.lean','LinearAlgebra/Matrix/ToLin.lean',
 'MeasureTheory/Measure/Lebesgue/Basic.lean','MeasureTheory/Measure/Haar/InnerProductSpace.lean','MeasureTheory/Measure/Map.lean']}
full=path('SafeLearning/primer-linalg.html');assert sha(full)==unit['source_sha256']=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
lines=full.read_text().splitlines(keepends=True);before='$W$ maps';after=r'For $\varepsilon>0$, $W$ maps';assert full.read_text().count(before)==1
new=full.read_text().replace(before,after,1);assert new.replace(after,before,1).encode()==full.read_bytes()
P=B/'primer-linalg-zonotope-positive-radius-prospective-unnumbered32.html';P.parent.mkdir(parents=True,exist_ok=True);P.write_text(new)
prop={**unit,'source_text':unit['source_text'].replace(before,after,1),'source_sha256':sha(P)};assert prop['source_text']!=unit['source_text'];prop['text_sha256']=hashlib.sha256(prop['source_text'].encode()).hexdigest()
body=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1] if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsBoxImageZonotope32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
q={'status':'prepared_full_BoxImageZonotope14_source_entire_current332_component_prospective_positive_radius_whole_review_request','errors':[],
 'final_genuine_passed_source':retain(S),'public_theorem_count':14,'public_name_count':18,'definition_count':4,'all_public_declarations':names,'public_theorem_names':ts,'all14_complete_body_signatures':body,
 'entire_current_literal':unit,'exact_planned_prospective_positive_radius_literal':prop,'prospective_full_Source81_page':ref(P),'unnumbered_exact_planned_replacements':[{'before':before,'after':after}],
 'actual_installed_owner31_pending_rows':rows,'immutable_actual_installed_owner31':retain(OWN),'current_inventory81':retain(V),'full_current_Source81_linalg':retain(full),
 'full_previous_radius_and_metric_context_lines172_219':''.join(lines[171:219]),'full_matrix_norm_and_box_image_context_lines309_362':''.join(lines[308:362]),
 'entire_two_selected_dependencies':selected,'old_AffineIBP29_full_mathematical_peer_unchanged':oldpeer,
 'exact_old_AffineIBP29_canonical_proof_metadata_and_pairs':proof,'bounded_existing_canonical_pair_leaf_refs':pairrefs,
 'old_peer_generic_zonotope_scope_gap_preserved':old['node196_remaining_scope'],
 'full_actual_used_Mathlib_primary_source_copies':providers,'all_genuine_native_histories':hist,'actual_standard_axioms_per_public_theorem':{name:[x.strip() for x in v.replace('\n',' ').split(',')] for name,v in ax},
 'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),
 'requested_full_mathematical_scope':'Read all14 proofs/four definitions, both entire selected dependencies and all actual used primary bodies, the exact full current332 and planned prospective332. New proofs close generic image/column-segment/Minkowski/positive-parallelogram/tightest-box correspondence; the old selected source supplies exact full running W image and actual Lebesgue8/16 areas unchanged. Current literal remains pending its radius and nondegeneracy qualification; full prospective whole is requested only after the separate exact positive-radius full29 parser proposal is independently verified. No neighboring verification196 whole decision is requested.',
 'actual_generic_zonotope_scope':'The actual finite matrix action equals its coefficient-scaled column sum. Both directions of the full uniform-box image equality choose independent genuine scalar coefficients. The resulting existential sum is explicitly identified with Mathlib finite Set Minkowski sum. Nonnegative-radius coefficient segments equal epsilon times unit segments and actual geometric closed segments between their endpoints. No desired-image equality is a hypothesis.',
 'actual_tight_box_scope':'Specializing the actual selected arbitrary ordered-box endpoint-attainment theorem derives exact upper/lower row-coordinate extrema epsilon*sum|Wij|. These actual endpoint witnesses prove the iff for containment in every possible axis-aligned enclosing box, so smallest half-widths are proved, not merely a sound bound. The width is the actual row one-norm times epsilon.',
 'actual_parallelogram_scope':'Nonzero actual determinant implies linear independence of both true matrix columns. A positive radius yields independent scaled generators via actual determinant scalar law. The box image is exactly the two-coefficient closed parallelogram. At epsilon0 it degenerates to a point; the proposed epsilon>0 scopes the printed nondegenerate word.',
 'actual_running_example_scope':'The unchanged selected W=[[1,1],[1,-1]] has full image equal to the entire diamond |z0|+|z1|<=2 with an explicit inverse for every point, all four printed corner images, exact input4/image8/boundingbox16 Lebesgue volumes and Euclidean copies. The new all-input Euclidean norm-square identity2*norm(x)^2 additionally proves the map is a scaled isometry, so the rotated image is a square, not just an arbitrary quadrilateral.',
 'actual_radius_domain_countercomparison':'The generic norm-ball/box identity and scaled unit-segment association require epsilon>=0 and correctly include zero and empty index cases. A genuine negative-radius example has an empty norm ball but nonempty negatively scaled unit segment; hence the printed formula is not approved for arbitrary real epsilon. The one planned epsilon>0 prefix resolves this and nondegenerate parallelogram together.',
 'current_or_prospective_whole332_approved_by_author':False,'no_Source_ordinal_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
q['original_genuine_author1_metadata_schema_failure_preserved']={
 'helper':retain('/tmp/prepare-foundations-boximage-zonotope14-full-scope32-v1.py'),
 'wrapper':retain('/tmp/run-prepare-foundations-boximage-zonotope14-full-scope32-v1.py'),
 'native':retain('/tmp/foundations-boximage-zonotope14-full-scope-author-preparation32-actual-v1.json'),
 'raw_log':retain('/tmp/foundations-boximage-zonotope14-full-scope-author-preparation32-actual-v1.log'),
 'diagnosis':'Author expected Module proof metadata under proof_sha256; actual authoritative Module owner31 has proof_files dictionary. NEW2 corrects only metadata lookup/output namespace. All proof/source/current/prospective bytes and original failure times unchanged.'}
retain(Path(__file__));q['physical_original_leaf_refs']=refs;q['required_evidence_artifacts_sha256']={r['file']:r['sha256'] for r in refs.values()}
O=B/'foundations-boximage-zonotope14-entire-source-current332-component-prospective332-whole-independent-review-request32-v2.json';O.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':ref(O),'public_theorems':14,'public_names':18,'source_codes':[h['actual_exit_code'] for h in hist[:3]],'physical_refs':len(refs)}))
