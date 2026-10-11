from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re,copy
R=Path('/home/oxrexkevin/SafetyBased')
REQ=Path('/tmp/foundations-linalg-refresher23-eleven-literals-full-source-review-request-v1.json')
OUT=Path('/tmp/foundations-linalg-refresher-eleven-literals-independent-modules-source-review23-v1.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
REF=lambda p:{'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':H(p)}
assert not OUT.exists()
assert H(REQ)=='67835ed0ee903e73565c80453bc08a5d55bdc8bcad6f30c41c9a560576739a2a'
r=J(REQ)
oldinv=R/'book/coverage/inventory-after-correction49.json'
assert H(oldinv)=='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
old=J(oldinv);current_path=R/'book/coverage/inventory.json';current=J(current_path)
oldunits={u['key']:u for u in old['material_source_units']};currentunits={u['key']:u for u in current['material_source_units']}
source=Path(r['new_proof_source']['file'])
assert H(source)==r['new_proof_source']['sha256']=='1918ab182f7fe20385966020197f3195abca4d61068ebeb1f21bfc9bd2061f0e'
body=source.read_text();assert body==r['new_proof_source']['entire_source']
prefix='SafeLearning.CompleteFoundationsLinalgRefresher23.'
names=[prefix+n for n in re.findall(r'^theorem\s+(\w+)',body,re.M)]
assert names==r['public_theorem_names'] and len(names)==r['public_theorem_count']==23
assert not re.search(r'\bsorry\b|\badmit\b|^axiom\s',body,re.M)
assert 'def A : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;0,1]' in body
assert 'def B : Matrix (Fin 2) (Fin 2) ℝ := !![2,0;1,3]' in body
assert 'def R : Matrix (Fin 2) (Fin 2) ℝ := !![1,2;2,4]' in body
assert 'def M : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;1,2]' in body
for t in r['all_actual_unique_trial_history']:
    for k in ['record','raw_log','source_snapshot']:
        p=t[k];assert H(p['file'])==p['sha256']
    a=J(t['record']['file']);assert a==t['entire_original_actual_record']
    assert a['source_sha256_before']==a['source_sha256_after']==t['source_snapshot']['sha256']
    assert a['command']==['lake','env','lean',t['source_snapshot']['file']]
    assert a['raw_log_sha256']==t['raw_log']['sha256']
assert J(r['all_actual_unique_trial_history'][0]['record']['file'])['actual_exit_code']==1
passed=J(r['actual_original_standalone']['record']['file']);assert passed['actual_exit_code']==0
warnings=Path(r['actual_original_standalone']['raw_log']['file']).read_text()
assert warnings.count('warning:')==4 and 'error:' not in warnings
g=r['precompile_old48_guard_observed_failure'];assert H(g['file'])==g['sha256']
guardfailure=J(g['file']);assert guardfailure['absent_Lean_record'] and guardfailure['absent_Lean_log']
assert guardfailure['observed_process_exit_code']==1
for p in r['all_original_trial_runners']+r['local_primary_Mathlib_semantics']:
    q=Path(p['file']);q=q if q.is_absolute() else R/q;assert H(q)==p['sha256']
html=R/'SafeLearning/primer-linalg.html';assert H(html)==r['full_source_HTML_context']['sha256']
ctx=r['full_source_HTML_context'];lines=html.read_text().splitlines(keepends=True)
assert ''.join(lines[ctx['first_line']-1:ctx['last_line']])==ctx['exact_lines']
manifest_path=R/r['protected_selected22_manifest']['file'];assert H(manifest_path)==r['protected_selected22_manifest']['sha256']
manifest=J(manifest_path);snapshot=R/manifest['snapshot'];assert len(manifest['proof_files'])==1113
for p,row in manifest['proof_files'].items():assert H(R/p)==row['sha256']
for p,d in r['protected_frozen22_source48_asset_sha256'].items():assert H(snapshot/p)==d
for p,d in r['protected_four_working22_ledger_sha256'].items():assert H(R/p)==d
reasons={
98:'The arbitrary rectangular matrix is typed with output rows m and input coordinates n. Its actual mulVec coordinate is exactly the row sum. The printed A action and actual (1,2) evaluation use the exact displayed matrix, with no relabeling of another fixture.',
100:'The actual printed A action is calculated coordinate by coordinate, and A times (1,2) equals (5,2). These exact real integer entries directly match both rows of the display.',
101:'The genuine arbitrary compatible rectangular matrix product acts by applying the right matrix first. Its every column equals the left matrix applied to that actual right column. The supplied B has columns (2,1) and (0,3), and the exact A/B product identities bind this example.',
103:'Both full displayed products are computed for the exact definitions A=[1,2;0,1] and B=[2,0;1,3]: AB=[4,6;1,3], BA=[2,4;1,5].',
104:'The actual A/B counterexample proves products cannot generally be reordered. Arbitrary transpose entries and rectangular product reversal are exported; the exact A transpose and A squared equals A*A are separately proved. The superscript explanation is notation tied to these actual operations.',
108:'For every real vector x, the actual triangular system A*x=(5,2) holds iff x=(1,2). The proof reads the second coordinate and uses it in the first coordinate, directly exposing the printed backward-substitution route.',
110:'The printed inverse [1,-2;0,1] is verified on both sides. For every real finite square matrix, nonzero determinant is equivalent to an actual two-sided inverse, with no invertibility conclusion assumed. The generic 2x2 determinant and printed detA=1 are derived. The last sentence is implementation advice to solve a system directly, not a universal numerical-performance or conditioning theorem.',
112:'The actual R action has second coordinate twice the first. Rank exactly one is derived from its outer-product upper bound and the genuine nonzero 1x1 submatrix lower bound. For every real x, Rx=0 iff x=t*(-2,1); for every real b, Rx=b is solvable iff b=t*(1,2). The exact determinant zero and two-sided-inverse criterion prove R has no inverse.',
117:'Both actual eigenvectors (1,1) and (1,-1) are proved nonzero, with exact matrix actions 3*(1,1) and (1,-1). They meet the literal nonzero-eigenvector definition and exhibit the eigenvalues 3 and1.',
119:'A genuine nonzero homogeneous solution of any finite real square matrix requires zero determinant, proved by actual kernel triviality for nonzero determinant. The exact printed determinant equals (2-lambda)^2-1=(1-lambda)*(3-lambda), and its zeros are precisely1 or3. The instruction to solve homogeneous equations is consistent with the explicit nonzero eigenvectors already exported; no unproved general spectral theorem is inferred.',
123:'The exact readiness multiplication A*(2,-1)=(0,-1) and all-vector unique solve A*x=(4,1) iff x=(2,1), together with both eigenvector equations, discharge each requested check. Continuing to the inner product and fluency advice are scoped instructional guidance.'}
hyp={
98:'Arbitrary real rectangular matrices with finite input index; actual A=[1,2;0,1] and vector(1,2).',
100:'Actual real Fin2 matrix A=[1,2;0,1] and vector(1,2).',
101:'Compatible finite real index types for rectangular products and vector composition; actual A,B as printed.',
103:'Actual real Fin2 matrices A=[1,2;0,1], B=[2,0;1,3].',
104:'Compatible real rectangular product types with finite inner index; actual A/B, ordinary transpose and square power.',
108:'Every real Fin2 candidate vector for the exact A and right side(5,2).',
110:'Finite real square matrices, with decidable finite index equality; actual printed A and its candidate inverse. Both directions retain their exact determinant assumptions.',
112:'Actual real Fin2 R=[1,2;2,4]; every candidate x and b, arbitrary real parameter t.',
117:'Actual real Fin2 M=[2,1;1,2] and both specified nonzero vectors.',
119:'Arbitrary finite real square C and nonzero v with actual C*v=0; the printed characteristic roots use actual M and every real lambda.',
123:'Actual A/M definitions and every candidate vector for the second readiness solve.'}
units=[]
for u in r['material_units']:
    rec=u['entire_inventory_record'];key=rec['key'];num=int(key.rsplit('-',1)[1])
    assert num in reasons and key!='primer-linalg.html::node-121'
    assert rec==oldunits[key]==currentunits[key]
    assert hashlib.sha256(rec['source_text'].encode()).hexdigest()==rec['text_sha256']
    assert all(n in names for n in u['proposed_lean_declarations'])
    units.append({'source_unit_key':key,'source':rec['source'],'source_sha256':rec['source_sha256'],
        'line':rec['line'],'locator':rec['locator'],'source_text':rec['source_text'],
        'unit_text_sha256':rec['text_sha256'],'entire_inventory_record':rec,
        'status':'approved_complete_source','material_status':'proved','whole_unit_approved':True,
        'lean_declarations':copy.deepcopy(u['proposed_lean_declarations']),
        'hypotheses':[hyp[num]],'per_unit_reason':reasons[num],'missing_clauses':[],
        'original_pending_rows_preserved_as_history':u['entire_original_pending_claim_rows']})
assert len(units)==11 and set(reasons)=={int(u['source_unit_key'].rsplit('-',1)[1]) for u in units}
report={
 'status':'independent_complete_literal_source_review_passed','reviewer':'/root/modules_resume',
 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'inventory':str(oldinv.relative_to(R)),'inventory_sha256':H(oldinv),
 'source':'SafeLearning/primer-linalg.html','source_sha256':H(html),
 'original_review_request':REF(REQ),'material_units':units,
 'full_source_HTML_context_read':ctx,'entire_new_TMP_source_body_read':body,
 'all23_public_theorem_names_read':names,
 'actual_new_proof_evidence':r['actual_original_standalone'],
 'actual_original_trial_history':r['all_actual_unique_trial_history'],
 'original_precompile_old48_guard_failure':g,
 'warning_scope':'Four original unnecessarySeqFocus warnings retained with genuine standalone trial2 exit0; original trial1 compiler failure and separate precompile guard failure remain exact.',
 'local_primary_Mathlib_semantics':r['local_primary_Mathlib_semantics'],
 'protected_selected22':{'manifest':r['protected_selected22_manifest'],'all1113_source_hashes_exact':True,
     'frozen31_source48_asset_sha256':r['protected_frozen22_source48_asset_sha256'],
     'four_held22_working_ledger_sha256':r['protected_four_working22_ledger_sha256']},
 'current_unchanged_Linalg_identity_observation':{'inventory':REF(current_path),'all11_entire_unit_records_equal_original49':True},
 'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),'errors':[],
 'limits':['Eleven exact physical units only are whole-approved. Node121 and every other neighboring literal/exercise remain outside this decision.',
           'Real finite matrix and index hypotheses are explicit; notation and implementation/study instructions are individually scoped. No numerical software-performance, generic spectral-basis or conditioning claim is inferred.',
           'The genuine new proof is TMP standalone only; no canonical source, named execution, live owner mapping or aggregate23 is claimed.',
           'All original trial/request/review/pending scopes and actual times remain immutable. Historical source49 inventory is explicit, and the current unchanged entire Linalg records are separately checked despite Root serial corrections to other pages.'],
 'coverage_complete':False}
OUT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':str(OUT),'sha256':H(OUT),'whole_units':11,'theorem_count':23}))
