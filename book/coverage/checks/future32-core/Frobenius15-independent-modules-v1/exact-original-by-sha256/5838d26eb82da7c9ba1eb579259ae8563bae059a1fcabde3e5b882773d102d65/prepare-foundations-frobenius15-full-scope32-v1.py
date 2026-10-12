from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future32-foundations/frobenius15-full-scope-v1';assert not B.exists()
S=Path('/tmp/CompleteFoundationsFrobeniusTraceRankComparison32-draft-v5.lean');V=R/'book/coverage/inventory-after-correction81.json';OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def retain(n):
 p=path(n);r=ref(p)
 if p.is_relative_to(R)and '.lake'not in p.parts and str(p.relative_to(R))not in ['SafeLearning/primer-linalg.html']:
  refs[str(p)]=r;return r
 t=B/'exact-original-by-sha256'/r['sha256']/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:t.write_bytes(p.read_bytes())
 a=ref(t);refs[str(p)]=a;return a
assert sha(S)=='4ffcc890b368ae7b7c95cb68f974d7f3579425fec2e45ebfc9915d0c53081870';assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
assert path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes();inv=json.loads(V.read_bytes());keys=['primer-linalg.html::node-315','primer-linalg.html::node-317'];units={x['key']:x for x in inv['material_source_units']};owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims']if set(keys)&set(r.get('source_unit_keys',[]))]
assert len(rows)==2 and all(r['status']=='pending'for r in rows)
s=S.read_text();sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
names=declarations(s);theorems=[x['name']for x in names if x['kind']=='theorem'];assert len(theorems)==15 and len(names)==16
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
hist=[]
for i in range(1,4):
 p=Path(f'/tmp/foundations-frobenius15-installed-owner31-trial{i}.json');n=json.loads(p.read_bytes());assert n['protection_errors']==[]and n['source_unchanged']is True
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after']and sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'trial':i,'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [h['actual_exit_code']for h in hist]==[1,1,0]and hist[-1]['source']['sha256']==sha(S)
AX=Path('/tmp/foundations-frobenius15-all-public-axiom-installed31-actual-v1.json');an=json.loads(AX.read_bytes());assert an['actual_exit_code']==0 and an['protection_errors']==[]
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",path(an['raw_log']).read_text(),re.S);assert [name for name,_ in ax]==theorems
assert all(set(x.strip()for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'}for _,v in ax)
primaries=['Analysis/Matrix/Normed.lean','Analysis/Matrix/Spectrum.lean','LinearAlgebra/Matrix/Rank.lean','Analysis/Normed/Lp/Matrix.lean','Analysis/Normed/Lp/PiLp.lean','Analysis/Normed/Operator/Basic.lean']
support={name:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/name)for name in primaries}
selected=retain('verification/lean/SafeLearning/CompleteFoundationsInducedNormProductCertificates30.lean')
oldpeer=retain('book/coverage/checks/future30-core/foundations-inducednorm19-independent-modules-v1/foundations-inducednorm19-full-source-five-component-independent-modules30-closed-peer-v3.json')
for i in [1,2]:retain(f'/tmp/CompleteFoundationsFrobeniusTraceRankComparison32-draft-v{i}.lean')
fullsource=path('SafeLearning/primer-linalg.html');assert sha(fullsource)==units[keys[0]]['source_sha256']=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
blocks=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);body=tail[:stop.start()+1]if stop else tail
 blocks.append({'declaration':'SafeLearning.CompleteFoundationsFrobeniusTraceRankComparison32.'+m.group(1),'complete_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'actual_signature':body.split(':=',1)[0].strip()})
q={'status':'prepared_bounded_full_Frobenius15_source_two_entire_current_literals_independent_review_request','errors':[],'final_genuine_passed_source':retain(S),'public_theorem_count':15,'definitions_count':1,'private_actual_Gram_hermitian_proof_present':True,'all_public_declarations':names,'public_theorem_names':theorems,'all15_entire_body_signatures':blocks,'complete_current_literals':{k:units[k]for k in keys},'actual_installed_owner31_pending_rows':rows,'immutable_installed_owner31':retain(OWN),'current_inventory81':retain(V),'full_current_Source81_linalg':retain(fullsource),'full_source_context_lines300_345':''.join(fullsource.read_text().splitlines(keepends=True)[299:345]),'full_selected_literal_matrix_CLM_bridge_source':selected,'original_induced19_component_peer_body_time_unchanged':oldpeer,'complete_used_primary_source_copies':support,'genuine_original_three_Lean_histories':hist,'actual_separate_all15_axiom_native':{'native':retain(AX),'source':retain(an['source']),'source_snapshot':retain(an['source_snapshot']),'raw_log':retain(an['raw_log']),'actual_exit_code':an['actual_exit_code'],'original_body_times':{k:an[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(an['raw_log']).read_text(),re.M))},'actual_standard_axioms_per_public_theorem':{name:[x.strip()for x in v.replace('\n',' ').split(',')]for name,v in ax},'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),'requested_full_mathematical_scope':'Independently read all15 complete proofs/actual Frob definition/private Gram proof, complete selected matrix-map source and actual primary proof bodies, and both entire315/317 with full matrix/norm/context. Decide each whole only after formula/trace-Hilbert/flattened vector/identity/rank comparison/family not-induced/running fixture clauses. The current whole scopes remain pending this independent decision.','mathematical_assessment':'The lower operator bound is derived from genuine Frobenius submultiplicativity on actual replicated column vectors. The upper bound uses actual Gram unit-eigenvector images and operator norm, genuine trace-sum and nonzero-eigenvalue rank cardinality, and rank(A-transpose*A)=rankA, then takes the nonnegative square root. No eigenvalue-bound, desired rank comparison or singular-value bound is assumed. All finite empty-dimension cases are included where stated. The trace pairing is exactly the Euclidean inner product of flattened matrices.','family_not_induced_domain_observation':'The norm family is not induced: the actual2x2 identity has Frob sqrt2>1 while every nontrivial induced identity norm is1. In one dimension Frobenius can coincide with an induced norm; no contrary one-dimensional statement is asserted by the proof. Please assess the complete source family wording explicitly.','exact_running_fixture_and_rounding':'Actual matrix[[2,2],[-1,1]] has Frob sqrt10, strictly within.005 of3.16. This is numerical approximation, not finite-decimal equality.','current_whole315_317_approved_by_author':False,'any_other_linalg_unit_source_ordinal_owner_canonical_selected_or_publication_mutated':False,'uncompiled_drafts1_2_preserved_not_claimed_native_passes':True,'physical_original_leaf_refs':refs,'coverage_complete':False}
retain(Path(__file__));q['physical_original_leaf_refs']=refs;q['required_evidence_artifacts_sha256']={r['file']:r['sha256']for r in refs.values()}
out=B/'foundations-frobenius15-entire-source-two-full-current-literals-independent-review-request32-v1.json';out.write_text(json.dumps(q,indent=2)+'\n');print(json.dumps({'request':ref(out),'public_theorems':15,'original_codes':[h['actual_exit_code']for h in hist],'physical_refs':len(refs)}))
