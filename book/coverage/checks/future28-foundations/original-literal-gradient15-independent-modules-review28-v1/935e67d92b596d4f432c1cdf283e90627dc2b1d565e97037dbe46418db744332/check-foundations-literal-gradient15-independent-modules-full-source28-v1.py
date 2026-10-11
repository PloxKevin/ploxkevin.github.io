from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, re

ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/foundations-literal-gradient15-full-review28-v1/foundations-literal-gradient15-full-review28-v1.json')
OUT=Path('/tmp/foundations-literal-gradient15-independent-modules-full-source28-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
def checked(r):
    assert type(r)is dict and set(r)=={'file','sha256'}
    p=Path(r['file']);p=p if p.is_absolute()else ROOT/p
    assert p.is_file()and not p.is_symlink()and sha(p)==r['sha256'],str(p)
    return p
def code(d,want):
    v=[d[k]for k in ('actual_exit_code','exit_code','actual_runner_exit_code')if k in d]
    assert v and all(type(x)is int and x==want for x in v)
started=datetime.now(timezone.utc).isoformat()
assert sha(REQUEST)=='0be78755dd642eebc9fc9ae9ef2c9a19c365da23fdcd95cd28e4f5ea19e6664b'
j=read(REQUEST);source=checked(j['proof_source']);s=source.read_text()
assert s==j['entire_source']and sha(source)=='729945670fd81ad7183192b8c6b028ef7b95035d484c31717de748e6faa50555'
matches=list(re.finditer(r'^theorem\s+(\w+)\b',s,re.M))
decls={m.group(1):s[m.start():(matches[i+1].start()if i+1<len(matches)else len(s))]for i,m in enumerate(matches)}
assert len(decls)==j['public_theorem_count']==15 and not re.search(r'\b(sorry|admit|axiom)\b',s)
selected=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
assert len(selected['proof_files'])==1175
bindings=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')
assets=bindings['exact_current55_safelearning_assets_sha256'];assert len(assets)==31
integration=read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json');assert integration['applied']is True
owners={r['destination']:r['candidate']['sha256']for r in integration['exact_replacements']};assert len(owners)==5
held={n:r['sha256']for n,r in selected['proof_files'].items()};held.update(assets);held.update(owners)
for k in ('current_inventory','current_foundations_owner'):held[str(checked(j[k]).relative_to(ROOT))]=j[k]['sha256']
held['reports/full-coverage/checkpoint-27-selection.json']='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
def guard():
    for n,h in held.items():assert sha(ROOT/n)==h,n
guard()
inv=read(checked(j['current_inventory']));units={r['key']:r for r in inv['material_source_units']}
keys={'primer-optimization.html::node-178','primer-optimization.html::node-208','primer-optimization.html::node-210'}
assert {r['key']for r in j['full_source_units']}==keys
for u in j['full_source_units']:
    assert u==units[u['key']]and sha(ROOT/u['source'])==u['source_sha256']
    assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
page=ROOT/'SafeLearning/primer-optimization.html'
context='\n'.join(page.read_text().splitlines()[128:218]);assert context==j['full_source_context_lines129_to218']
ledger=read(checked(j['current_foundations_owner']))
rows=[r for r in ledger['material_claims']if keys.intersection(r.get('source_unit_keys',[]))]
assert rows==j['current_pending_claims_unchanged']
assert len(j['all_reused_dependency_sources'])==4
for r in j['all_reused_dependency_sources']:
    p=checked(r['source']);assert p.read_text()==r['entire_source']
    if '/SafeLearning/'in str(p):
        n=str(p.relative_to(ROOT));assert selected['proof_files'][n]['sha256']==r['source']['sha256']
for original,r in j['original_closed_byte_aliases'].items():assert Path(original).read_bytes()==checked(r).read_bytes()and sha(original)==r['sha256']
assert len(j['original_closed_byte_aliases'])==18
assert len(j['actual_trials_original_bodies_and_times'])==3
for i,row in enumerate(j['actual_trials_original_bodies_and_times']):
    a=read(checked(row['record']));assert a==row['entire_original_record_and_time'];code(a,0 if i==2 else 1)
    assert a['actual_command']==['lake','env','lean',a['source']]and a['actual_workdir']==str(ROOT/'verification/lean')
    assert a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==sha(checked(row['source_snapshot']))
    assert checked(row['source_snapshot']).read_text()==row['entire_original_source']
    assert sha(a['raw_log'])==a['raw_log_sha256']==row['raw_log']['sha256']and checked(row['raw_log']).read_text()==row['entire_raw_log']
    assert a['protection_errors']==[]and a['protected_proof_sources']==1175
    assert a['installed27_owner_sha256']==owners
    assert a['original_actual_runner']=={'file':'/tmp/root_tmp_lean28_runner_v4.py','sha256':'8fe26e9954800b4e104db5a079eb2e9295e3680064fe7ebaaa74b496e60ec49b'}
    checked(a['original_actual_runner'])
    assert row['actual_emitted_warning_diagnostics']==row['entire_raw_log'].count('warning:')
success=j['actual_trials_original_bodies_and_times'][2]
assert j['actual_successful_trial']==success['record']and success['entire_original_source']==s
assert j['actual_successful_emitted_warning_diagnostics']==success['actual_emitted_warning_diagnostics']==1
ns='SafeLearning.CompleteFoundationsLiteralGradientHessian28.'
names={ns+n for n in decls};cs={r['key']:r for r in j['complete_literal_clause_correspondences']}
assert set(cs)==keys and set().union(*(set(r['lean_declarations'])for r in cs.values()))==names
reason178='The exact polynomial x1^2+3*x1*x2 is genuinely C2 and its actual HasGradientAt is (2*x1+3*x2,3*x1). At the printed point (1,2), the gradient is (8,3), every actual line direction has the inner-product derivative, and (1,1)/sqrt2 is a unit direction with slope11/sqrt2. The true Euclidean gradient norm is sqrt73; every unit direction has slope at most sqrt73 and the exact normalized gradient attains it. This complete example has nonzero gradient, so division by its norm is legitimate. Strict rational enclosures prove the printed two-decimal approximations7.78 and8.54.'
reasonH='For arbitrary finite real Euclidean coordinates and an actual local C2 function, the derivative of the true gradient is differentiated through the inverse real Riesz map; its coordinate matrix equals the genuine second Frechet derivative against basis vectors. The primary C2 symmetry theorem proves mixed-partial commutation and transpose equality. The exact polynomial has actual Hessian operator[[2,3],[3,0]], not a different selected quadratic. Its symmetric matrix has nonnegative diagonal; nonzero eigenvectors realize1±sqrt10 and the full nonzero-vector eigenvalue iff excludes other real eigenvalues. Exact sign and decimal bounds support4.16/-2.16. Genuine Hessian quadratic forms8 and-4 along(1,1)/(1,-1) establish both curvature directions for this quadratic.'
decisions=[]
for u in j['full_source_units']:
    h=['Real finite Euclidean coordinate spaces, the literal polynomial x1^2+3*x1*x2, and the printed evaluation point(1,2).','The printed directional/maximal-slope example uses actual Euclidean unit vectors and a nonzero gradient of normsqrt73.']if u['key'].endswith('178')else ['Arbitrary finite real Euclidean coordinates and ContDiffAt real2 at the point for the generic gradient-Jacobian/second-partial/symmetry clauses.','For numerical spectrum and curvature, the actual literal polynomial with constant matrix[[2,3],[3,0]]; real nonzero eigenvectors and genuine Euclidean quadratic forms.']
    decisions.append({'source_unit_key':u['key'],'entire_inventory_record':copy.deepcopy(u),'status':'proved','decision':'approved_complete_literal_under_explicit_hypotheses','whole_unit_approved':True,'whole_literal_approved':True,'lean_declarations':cs[u['key']]['lean_declarations'],'hypotheses':h,'reason':reason178 if u['key'].endswith('178')else reasonH,'per_clause_correspondence':cs[u['key']]['complete_literal_correspondence'],'missing_clauses':[],'remaining_gaps':[]})
guard()
closure={str(REQUEST):sha(REQUEST),str(source):sha(source),str(page):sha(page)}
for r in j['all_reused_dependency_sources']:closure[str(checked(r['source']))]=r['source']['sha256']
for original,r in j['original_closed_byte_aliases'].items():closure[original]=r['sha256'];closure[r['file']]=r['sha256']
closure.update({str(ROOT/n):h for n,h in held.items()})
out={'status':'passed_independent_full_three_literal_gradient_hessian_source_review28','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'proof_source':j['proof_source'],'public_theorem_count':15,'all_public_declarations':sorted(names),'all_fifteen_complete_bodies_definitions_and_three_complete_literals_read':True,'all_four_full_dependency_and_primary_sources_read':True,'entire_source':s,'all_complete_theorem_bodies':decls,'full_reused_dependency_and_primary_sources':j['all_reused_dependency_sources'],'full_local_teaching_context':context,'material_units':decisions,'entire_original_existing_claims_and_times':rows,'entire_actual_trial_records_sources_logs_and_times':j['actual_trials_original_bodies_and_times'],'actual_successful_trial':j['actual_successful_trial'],'actual_warning_count':1,'current1175_sources31_assets5_owners_rehashed_before_after':True,'scope':'TMP-only full literal and mathematical correspondence review, with actual prior standalone0 and all real failures/warnings preserved. Parent208 and body210 are each approved from their complete generic C2 and literal-example content. No compiler rerun, new canonical pairing, owner/candidate installation, adjacent unit or parent-section promotion, or aggregate verification is claimed.','closed_evidence_sha256':closure,'actual_checker':ref(Path(__file__))}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'public_theorem_count':15,'whole_units':sorted(keys)}))
