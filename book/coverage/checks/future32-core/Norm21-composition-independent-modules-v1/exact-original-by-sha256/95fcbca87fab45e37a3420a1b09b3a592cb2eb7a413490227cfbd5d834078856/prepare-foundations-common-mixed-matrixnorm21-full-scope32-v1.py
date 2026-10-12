from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/future32-foundations/common-mixed-matrixnorm21-full-scope-v1'
assert not B.exists()
S=Path('/tmp/CompleteFoundationsCommonMixedInducedNormFormulas32-draft-v7.lean')
V=R/'book/coverage/inventory-after-correction81.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
def path(n): return Path(n) if Path(n).is_absolute() else R/n
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n)
 return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def retain(n):
 p=path(n);r=ref(p)
 if p.is_relative_to(R) and '.lake' not in p.parts and str(p.relative_to(R))!='SafeLearning/primer-linalg.html':
  refs[str(p)]=r;return r
 t=B/'exact-original-by-sha256'/r['sha256']/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists(): assert t.read_bytes()==p.read_bytes()
 else: t.write_bytes(p.read_bytes())
 a=ref(t);refs[str(p)]=a;return a
assert sha(S)=='74682eee88d589f2f6107fdb0560f12074e5e13e9b28f65e59936ee35a51ee45'
assert sha(V)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
assert path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes()
inv=json.loads(V.read_bytes());keys=['primer-linalg.html::node-305','primer-linalg.html::node-307','primer-linalg.html::node-311']
units={k:next(r for r in inv['material_source_units'] if r['key']==k) for k in keys}
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if any(k in r.get('source_unit_keys',[]) for k in keys)]
assert {k for r in rows for k in r.get('source_unit_keys',[]) if k in keys}==set(keys)
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
s=S.read_text();names=declarations(s);theorems=[r['name'] for r in names if r['kind']=='theorem']
assert len(names)==25 and len(theorems)==21 and sum(r['kind']=='def' for r in names)==4
assert len(re.findall(r'^private theorem ',s,re.M))==6
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
old19=Path('/tmp/CompleteFoundationsCommonMixedInducedNormFormulas32-draft-v5.lean')
old10=Path('/tmp/CompleteFoundationsCommonMixedInducedNormFormulas32-draft-v2.lean')
assert S.read_bytes().startswith(old19.read_bytes()) and S.read_bytes().startswith(old10.read_bytes())
native_names=[
 '/tmp/foundations-common-mixed-matrixnorm10-installed31-trial1.json',
 '/tmp/foundations-common-mixed-matrixnorm10-installed31-trial2.json',
 '/tmp/foundations-common-mixed-matrixnorm18-installed31-trial3.json',
 '/tmp/foundations-common-mixed-matrixnorm19-installed31-trial4.json',
 '/tmp/foundations-common-mixed-matrixnorm19-installed31-trial5.json',
 '/tmp/foundations-common-mixed-matrixnorm21-installed31-trial6.json',
 '/tmp/foundations-common-mixed-matrixnorm21-installed31-trial7.json',
 '/tmp/foundations-common-mixed-matrixnorm19-all-public-axioms-installed31-actual-v1.json',
 '/tmp/foundations-common-mixed-matrixnorm21-all-public-axioms-installed31-actual-v1.json']
hist=[]
for i,p in enumerate(native_names):
 n=json.loads(path(p).read_bytes())
 assert n['actual_exit_code']==n['actual_runner_exit_code'] and n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after']
 assert sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'history_role':('source_trial_'+str(i+1)) if i<7 else ('all19_axiom_inspection' if i==7 else 'all21_axiom_inspection'),
  'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),
  'actual_exit_code':n['actual_exit_code'],'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),
  'original_body_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [h['actual_exit_code'] for h in hist]==[1,0,1,1,0,1,0,0,0]
assert hist[6]['source']['sha256']==sha(S)
axraw=path(native_names[-1]).with_suffix('.log').read_text()
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axraw,re.S)
assert [name for name,_ in ax]==theorems
assert all(set(x.strip() for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'} for _,v in ax)
selected={n:retain('verification/lean/SafeLearning/'+n) for n in [
 'CompleteFoundationsHolderDualNormWholeUnits30.lean',
 'CompleteFoundationsInducedNormProductCertificates30.lean',
 'CompleteFoundationsRayleighQuotientWhole30.lean']}
providers={n:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n) for n in [
 'Analysis/Normed/Lp/PiLp.lean','Analysis/Normed/Lp/Matrix.lean',
 'Analysis/InnerProductSpace/PiL2.lean','Analysis/InnerProductSpace/Adjoint.lean',
 'Analysis/InnerProductSpace/SingularValues.lean','Analysis/InnerProductSpace/Spectrum.lean',
 'Analysis/Matrix/Spectrum.lean','Analysis/Matrix/Normed.lean','Analysis/Real/Sqrt.lean',
 'LinearAlgebra/Matrix/Hermitian.lean','LinearAlgebra/Matrix/DotProduct.lean',
 'LinearAlgebra/Matrix/ToLin.lean','LinearAlgebra/Matrix/PosDef.lean',
 'Algebra/Order/BigOperators/Group/Finset.lean','Analysis/Normed/Operator/Basic.lean']}
peers={n:retain(n) for n in [
 'book/coverage/checks/future30-core/foundations-holder23-full-independent-modules-v1/foundations-holder23-full-source-two-whole-independent-modules30-closed-peer-v3.json',
 'book/coverage/checks/future30-core/foundations-inducednorm19-independent-modules-v1/foundations-inducednorm19-full-source-five-component-independent-modules30-closed-peer-v3.json',
 'book/coverage/checks/future30-core/rayleigh18-independent-applied30b-v1/foundations-rayleigh18-full-components-prospective427429430-with-current422-rotation-gap-independent-applied30b-closed-peer-v1.json']}
full=path('SafeLearning/primer-linalg.html');assert sha(full)=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
assert all(r['source_sha256']==sha(full) for r in units.values())
lines=full.read_text().splitlines(keepends=True)
body=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1] if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsCommonMixedInducedNormFormulas32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
q={'status':'prepared_full_CommonMixedInducedNorm21_source_three_entire_current_literals_mathematical_review_request',
 'errors':[],'final_genuine_passed_source':retain(S),'public_theorem_count':21,'public_name_count':25,'definition_count':4,'private_proof_count':6,
 'all_public_declarations':names,'public_theorem_names':theorems,'all21_complete_body_signatures':body,
 'entire_three_current_literals':units,'actual_installed_owner31_affected_rows':rows,'immutable_actual_installed_owner31':retain(OWN),
 'current_inventory81':retain(V),'full_current_Source81_linalg':retain(full),
 'full_p_norm_domain_and_dual_norm_context_lines139_309':''.join(lines[138:309]),
 'full_induced_norm_definition_table_proofs_and_running_fixture_context_lines309_350':''.join(lines[308:350]),
 'entire_three_selected_dependencies':selected,'full_actual_used_Mathlib_primary_source_copies':providers,
 'old_dependency_independent_peer_refs_no_body_or_time_redecision':peers,
 'genuine_literal_byte_prefixes':{'old_passed10':retain(old10),'old_passed19':retain(old19),'entire10_and19_bytes_prefix_final21':True},
 'all_genuine_native_histories':hist,'actual_standard_axioms_per_public_theorem':{name:[x.strip() for x in v.replace('\n',' ').split(',')] for name,v in ax},
 'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),
 'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),
 'requested_entire_literal_mathematical_scope':'Read every21 full proof/four definitions/six private proofs, all three complete selected sources and actual used primary proof chains, all complete current305/307/311 and context. Decide current/prospective tables individually, keeping the missing common positive-dimension qualification explicit. The separate unnumbered narrow proposal will qualify305/307 with m,n>=1 and leave311 unchanged. No neighboring source-unit promotion.',
 'actual_mixed_formula_scope':'Actual sourceMatrixMap p q is the selected genuine finite-dimensional continuous linear map. Column decomposition plus triangle inequality bounds1->p, attained by an actual coordinate unit vector. All conjugate p->infinity are bounded by actual Holder and attained by genuine norm<=1 dual-ball vectors. Exponents cover1 and infinity endpoints with Fact1<=p,q and ENNReal.HolderConjugate, not just finite interior exponents.',
 'actual_spectral_formula_scope':'The true squared image norm equals x dot (A transpose*A)x. Actual Hermitian eigenbasis Rayleigh extrema give upper bound and unit eigenvector attainment. All actual Gram eigenvalues are nonnegative image norm squares. The final two new proofs identify the finite Gram maximum with descending eigenvalue0 and the Gram linear map with actual adjoint composition, yielding opNorm=LinearMap.singularValues0 and IsGreatest of the complete actual singularValues range. This is named singularValues correspondence, not merely a definition of sigma by the desired norm.',
 'actual_running_fixture_scope':'For [[2,2],[-1,1]], actual1=3,infinity=4 at(1,1),1->infinity=2,2->infinity=sqrt8,2->2=2sqrt2. Exact energy gap3(x0-x1)^2 bounds every input and the actual unit input attains it; strict error<.005 certifies the printed2.83. Both directions of the entire unit-circle image ellipse are proved with semiaxes2sqrt2,sqrt2, not just an axis witness.',
 'dimension_conventions':'Column maximum requires nonempty n, row maximum nonempty m, entry maximum both; spectral Gram maximum nonempty n. Other dimension may be empty and the respective formulas genuinely give0. The printed simultaneous table is proposed on m,n>=1 so every displayed maximum and nonzero-input unit-sphere convention exists. No unrestricted empty-dimensional maximum is approved.',
 'zero_matrix_sign_attainment_convention':'The selected Holder dual attainer has norm<=1. Zero weights may give sign0=0, which correctly attains the zero bound without division. A nonzero maximal row forces a unit attainer; the zero operator still has the genuine norm0 and coordinate-unit attainment where input is nonempty. Do not claim the zero sign vector is nonzero or has norm1.',
 'current_or_prospective_whole_approval_by_author':False,
 'no_Source_ordinal_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
retain(Path(__file__));q['physical_original_leaf_refs']=refs
q['required_evidence_artifacts_sha256']={r['file']:r['sha256'] for r in refs.values()}
out=B/'foundations-common-mixed-inducednorm21-entire-source-three-literals-full-mathematical-independent-review-request32-v1.json'
out.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':ref(out),'public_theorems':21,'public_names':25,'source_codes':[h['actual_exit_code'] for h in hist[:7]],'physical_refs':len(refs)}))
