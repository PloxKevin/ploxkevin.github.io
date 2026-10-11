from pathlib import Path
import json,hashlib,re,shutil
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/foundations-literal-gradient15-full-review28-v1');OUT.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):
    p=Path(p)
    if not p.is_absolute():p=ROOT/p
    return {'file':str(p),'sha256':sha(p)}
inv=json.loads((ROOT/'book/coverage/inventory.json').read_text())
owner=json.loads((ROOT/'book/coverage/foundations.json').read_text())
assert sha(ROOT/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
source=Path('/tmp/CompleteFoundationsLiteralGradientHessian28-draft-v3.lean')
assert sha(source)=='729945670fd81ad7183192b8c6b028ef7b95035d484c31717de748e6faa50555'
names=re.findall(r'^theorem (\w+)',source.read_text(),re.M);assert len(names)==15
ns='SafeLearning.CompleteFoundationsLiteralGradientHessian28.'
keys=['primer-optimization.html::node-'+str(n) for n in [178,208,210]]
units=[u for u in inv['material_source_units'] if u['key'] in keys];assert len(units)==3
groups=[
 {'key':keys[0],'lean_declarations':[ns+names[n] for n in [0,1,3,4,5,6,7]],'complete_literal_correspondence':[
  'literalObjective is exactly f=x1 squared+3x1x2; the existing CalculusModels uses another polynomial and is reused only for the actual Euclidean coordinate continuous linear map. The actual gradient is proved as HasGradientAt and becomes the actual vector(2x1+3x2,3x1); at the printed point(1,2) it is(8,3).',
  'The actual directional line t↦f((1,2)+t v) has a genuine HasDerivAt at0 for every Euclidean vector v, with slope inner((8,3),v). The printed v=(1,1)/sqrt2 has actual norm1 and its actual slope is11/sqrt2.',
  'The true gradient norm is sqrt73. For every actual Euclidean unit v, real Cauchy–Schwarz bounds its slope by sqrt73. The actual normalized vector(8/sqrt73,3/sqrt73) has norm1 and attains sqrt73. Since norm((8,3))=sqrt73>0, this vector is exactly the printed gradient divided by its norm; no zero-gradient normalization is used.',
  'Exact strict rational enclosures7.775<11/sqrt2<7.785 and8.535<sqrt73<8.545 support the printed two-decimal roundings7.78 and8.54. They are proved using actual real square-root identities and positivity, not floating-point measurements.'
 ]},
 {'key':keys[1],'lean_declarations':[ns+names[n] for n in [0,1,2,8,9,10,11,12,13,14]],'complete_literal_correspondence':[
  'For an arbitrary finite Euclidean coordinate index I and f genuinely C2 at x, jacobianGradientHessian takes entries of the true Frechet derivative of the actual gradient against the jth coordinate basis vector, evaluated in coordinate i. secondPartialHessian is the true second Frechet derivative against the two coordinate basis vectors. The proof differentiates the actual inverse real Riesz map and derives equality of these matrices; it does not posit the displayed Hessian correspondence.',
  'ContDiffAt R2 implies symmetry of the second derivative by the primary Mathlib ContDiffAt.isSymmSndFDerivAt theorem. Applied to actual basis vectors, it proves transpose equality of the actual gradient Jacobian matrix. C2 is retained as a real local differentiability/continuity assumption, not replaced by the intended symmetry conclusion.',
  'The literal polynomial is actually C2. Its true gradient derivative is the actual operator from matrix[[2,3],[3,0]], which is symmetric and has nonnegative diagonal. Explicit real eigenvectors(1+sqrt10,3) and(1-sqrt10,3) are nonzero, have the stated eigenvalues, and every nonzero real eigenvector has one of those two eigenvalues.',
  'The positive eigenvalue1+sqrt10 and negative eigenvalue1-sqrt10 are proved with exact2-decimal rounding enclosures4.155<lambdaPlus<4.165 and-2.165<lambdaMinus<-2.155. Actual Hessian quadratic forms are8 along(1,1) and-4 along(1,-1), establishing the up/down curvature of this polynomial despite nonnegative diagonal entries.'
 ]},
 {'key':keys[2],'same_complete_mathematical_body_as_parent_key':keys[1],'lean_declarations':[ns+names[n] for n in [0,1,2,8,9,10,11,12,13,14]],'complete_literal_correspondence':'This separately inventoried full body is read and bound independently to its own text hash. Every generic C2 gradient-Jacobian/second-partial/symmetry clause and all literal polynomial Hessian/spectrum/sign/rounding/curvature clauses have exactly the same complete correspondence as the containing definition unit208. It is not classified as a label or promoted from only the numerical example.'}
]
records=[];files=[source,ROOT/'SafeLearning/primer-optimization.html']
for n in [1,2,3]:
    p=Path('/tmp/foundations-literal-gradient-hessian28-trial'+str(n)+'.json');a=json.loads(p.read_text());expected=0 if n==3 else 1
    assert type(a['actual_exit_code']) is int and a['actual_exit_code']==expected
    assert a['actual_runner_exit_code']==expected and a['protection_errors']==[] and a['source_unchanged'] is True
    assert sha(Path(a['raw_log']))==a['raw_log_sha256'] and sha(Path(a['source_snapshot']))==a['source_snapshot_sha256']
    log=Path(a['raw_log']).read_text()
    records.append({'record':ref(p),'entire_original_record_and_time':a,'raw_log':ref(Path(a['raw_log'])),'entire_raw_log':log,'source_snapshot':ref(Path(a['source_snapshot'])),'entire_original_source':Path(a['source_snapshot']).read_text(),'actual_emitted_warning_diagnostics':len(re.findall(r'^.+\.lean:\d+:\d+: warning:',log,re.M))})
    files += [p,Path(a['raw_log']),Path(a['source_snapshot']),Path(a['source']),Path(a['original_actual_runner']['file'])]
dependencies=[ROOT/'verification/lean/SafeLearning/CompleteFoundationsCalculusModels.lean',ROOT/'verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean']
files+=dependencies
aliases={}
for p in dict.fromkeys(files):
    h=sha(p);q=OUT/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
    if q.exists():assert q.read_bytes()==p.read_bytes()
    else:shutil.copyfile(p,q)
    aliases[str(p)]={'file':str(q),'sha256':h}
context=(ROOT/'SafeLearning/primer-optimization.html').read_text().splitlines()
j={'status':'prepared_tmp_actual15_body_three_full_literal_source_semantic_review_request','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/foundations_recovery28','current_inventory':ref(ROOT/'book/coverage/inventory.json'),'current_foundations_owner':ref(ROOT/'book/coverage/foundations.json'),'proof_source':ref(source),'entire_source':source.read_text(),'public_theorem_count':15,'full_source_units':units,'full_source_context_lines129_to218':'\n'.join(context[128:218]),'current_pending_claims_unchanged':[c for c in owner['material_claims'] if any(k in keys for k in c['source_unit_keys'])],'complete_literal_clause_correspondences':groups,'actual_trials_original_bodies_and_times':records,'actual_successful_trial':records[2]['record'],'actual_successful_emitted_warning_diagnostics':records[2]['actual_emitted_warning_diagnostics'],'all_reused_dependency_sources':[{'source':ref(p),'entire_source':p.read_text()} for p in dependencies],'original_closed_byte_aliases':aliases,'independent_whole_unit_approval':False,'canonical_installation_or_aggregate_verification_claimed':False,'review_request':'Read every full15 body/definition, all3 complete current literals including the generic C2 Hessian parent/body and exact example source, true operator/Riesz/basis/second-partial bridge and reused primary declarations. Check native successful3 and true failed1/2 with original full source/raw/body/times; decide all printed clauses independently. Compilation/integrity alone is not source correspondence. No generic function f may be replaced by a different fixed quadratic and no target symmetry or derivative is a premise.','scope':'TMP-only protected actual Lean and independent full-source semantic request; no installed owners/proofs/current55 changes.'}
p=OUT/'foundations-literal-gradient15-full-review28-v1.json';assert not p.exists();p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'packet':ref(p),'public_theorems':15,'full_literal_units':3,'byte_aliases':len(aliases),'actual_warning_diagnostics':j['actual_successful_emitted_warning_diagnostics']}))
