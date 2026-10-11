from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':str(p),'sha256':sha(p)}
invpath=ROOT/'book/coverage/inventory-after-correction49.json';inv=read(invpath)
assert sha(invpath)=='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
oldinv=read(ROOT/'book/coverage/inventory-after-correction48.json')
ledgerpath=ROOT/'book/coverage/foundations.json';ledger=read(ledgerpath)
assert sha(ledgerpath)=='305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88'
source=TMP/'foundations-linalg-refresher23-trial2.lean'
assert sha(source)=='1918ab182f7fe20385966020197f3195abca4d61068ebeb1f21bfc9bd2061f0e'
names=['SafeLearning.CompleteFoundationsLinalgRefresher23.'+n for n in re.findall(r'^theorem\s+(\w+)',source.read_text(),re.M)]
assert len(names)==23
groups={98:([0,3,4],['Genuine arbitrary rectangular matrix output equals its row coordinate sum; actual printed A times (1,2).']),100:([3,4],['All coordinate actions and the exact printed Ax display.']),101:([1,2,5],['Arbitrary compatible rectangular composition, every product column, and the actual A/B example.']),103:([5],['Both displayed products calculated exactly over real entries.']),104:([6,7,8,9],['Actual noncommuting counterexample; arbitrary transpose entries/product reversal; printed transpose and power2.']),108:([3,10],['Every real candidate vector solves the displayed triangular system iff it equals (1,2); actual backward substitution.']),110:([11,12,13],['Printed two-sided inverse and generic finite real square inverse iff nonzero determinant; full arbitrary 2x2 determinant formula.','Only the final advice about usually preferring a solve to explicit inversion is algorithmic guidance, without an unconditional performance theorem.']),112:([14,15,16,17,18],['Actual rank definition equals1, arbitrary full nullspace/range/solvability, printed row dependency and no inverse.']),117:([19],['Both vectors proved nonzero with their actual eigenvector scaling equations and exact eigenvalues3/1; eigenvector term denotes precisely this property.']),119:([20,21],['Arbitrary nonzero homogeneous solution requires zero determinant; actual characteristic factorization and iff two real roots; solving the homogeneous system afterward is proof guidance.']),123:([19,22],['Exact two printed readiness computations, all possible solutions, and previous eigenvector checks; final learning advice is narrowly pedagogical.'])}
units={r['key']:r for r in inv['material_source_units']};oldunits={r['key']:r for r in oldinv['material_source_units']}
rows=[]
for n,(idx,why) in groups.items():
 key=f'primer-linalg.html::node-{n}';u=units[key];pending=[r for r in ledger['material_claims'] if key in r['source_unit_keys'] and r['status']=='pending']
 assert u==oldunits[key] and pending and sha(ROOT/u['source'])==u['source_sha256']
 rows.append({'source_unit_key':key,'entire_inventory_record':u,'entire_original_pending_claim_rows':pending,'whole_unit_requested':True,'proposed_lean_declarations':[names[i] for i in idx],'proposed_clause_scope':why,'candidate_missing_clauses':[]})
hist=[]
for n,exitcode in [(1,1),(2,0)]:
 p=TMP/f'foundations-linalg-refresher23-trial{n}.json';r=read(p)
 assert r['actual_exit_code']==exitcode and sha(Path(r['source']))==r['source_sha256_before']==r['source_sha256_after']
 assert sha(Path(r['raw_log']))==r['raw_log_sha256'] and sha(Path(r['actual_runner']))==r['actual_runner_sha256']
 hist.append({'record':ref(p),'entire_original_actual_record':r,'source_snapshot':ref(Path(r['source'])),'raw_log':ref(Path(r['raw_log']))})
manifestpath=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';manifest=read(manifestpath)
for name,row in manifest['proof_files'].items():assert sha(ROOT/name)==row['sha256']
assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
for name,digest in assets.items():assert sha(ROOT/'reports/full-coverage/checkpoint-22'/name)==digest
held={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}}
for name,digest in held.items():assert sha(ROOT/name)==digest
html=(ROOT/'SafeLearning/primer-linalg.html').read_text().splitlines(keepends=True)
primary=[]
for name,scope in [('Mathlib/Data/Matrix/Mul.lean','Directly read true rectangular mulVec composition889–896 and transpose product reversal1174–1178.'),('Mathlib/LinearAlgebra/Matrix/Rank.lean','Directly read genuine vecMulVec rank≤1 and rank-submatrix monotonicity198–203/287–310; rank identity proves the nonzero1x1 lower bound.'),('Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean','Directly read real unit determinant/invertibility127–132 and true two-sided nonsingular inverse211–224.'),('Mathlib/LinearAlgebra/Matrix/Nondegenerate.lean','Directly read actual kernel-triviality theorem for nonzero determinant180–182.'),('Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean','Directly read full arbitrary 2x2 determinant calculation806–815.')]:
 p=ROOT/'verification/lean/.lake/packages/mathlib'/name;primary.append({'file':str(p.relative_to(ROOT)),'sha256':sha(p),'direct_read_scope':scope})
result={'status':'actual_TMP_standalone_zero_23_full_bodies_11_current49_linalg_literals_peer_requested_future23','created_at_utc':datetime.now(timezone.utc).isoformat(),'review_request':'Independently full-read every source clause and all23 complete theorem bodies/private definitions; approve each whole unit only if every mathematical clause holds under the actual hypotheses. Retain exact source49 identity and old48 unchanged literal equality. Node121 orthonormality/spectral-basis material is deliberately not included or promoted.','inventory':ref(invpath),'original48_inventory':ref(ROOT/'book/coverage/inventory-after-correction48.json'),'held_foundations22_ledger':ref(ledgerpath),'material_units':rows,'full_source_HTML_context':{'file':'SafeLearning/primer-linalg.html','sha256':sha(ROOT/'SafeLearning/primer-linalg.html'),'first_line':65,'last_line':132,'exact_lines':''.join(html[64:132])},'new_proof_source':{**ref(source),'entire_source':source.read_text()},'public_theorem_names':names,'public_theorem_count':23,'actual_original_standalone':hist[1],'all_actual_unique_trial_history':hist,'trial1_failure_description':'Two genuine arithmetic proof errors in the final characteristic-root disjunction: trial2 explicitly selects left/right before linarith. No theorem statement or other body was weakened; four actual unnecessarySeqFocus warnings remain.','precompile_old48_guard_observed_failure':ref(TMP/'foundations-linalg-refresher23-initial-old48-guard-observed-failure-v1.json'),'all_original_trial_runners':[ref(TMP/'run-foundations-linalg-refresher23-trial-v1.py'),ref(TMP/'run-foundations-linalg-refresher23-trial-v2.py')],'local_primary_Mathlib_semantics':primary,'protected_selected22_manifest':ref(manifestpath),'protected_selected22_source_count':len(manifest['proof_files']),'protected_frozen22_source48_asset_sha256':assets,'protected_four_working22_ledger_sha256':held,'unchanged_48_to_49_entire_linalg_literal_records_verified':True,'canonical_source_or_named_execution_claimed':False,'whole_parent_exercise_approved':False,'coverage_complete':False,'limits':['The dimensions are represented by arbitrary types with precisely the finite-index hypotheses required for sums and real finite square determinants.','All printed matrices, actual Matrix.rank and complete nullspace/range/equation iff statements are proved; no desired conclusion is assumed.','Narrow learning/algorithmic guidance is identified per clause rather than used to dismiss any mathematical guarantee.','The root source49 correction concerns two Monitoring clauses only. This request uses the actual archived49 identity and full unchanged Foundation literals; it does not overwrite48 reviews or any22 selected asset.','Only TMP request/helper files written. Canonical paired execution and isolated candidate mapping require separate actual records and peer approval.']}
out=TMP/'foundations-linalg-refresher23-eleven-literals-full-source-review-request-v1.json'
with out.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'request':ref(out),'public_theorems':23,'whole_units_requested':11}))
