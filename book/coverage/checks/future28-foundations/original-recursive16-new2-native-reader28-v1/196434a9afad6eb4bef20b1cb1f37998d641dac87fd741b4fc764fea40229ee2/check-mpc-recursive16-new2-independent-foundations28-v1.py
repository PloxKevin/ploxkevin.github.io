from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/mpc-recursive-finite-shift16-full-review28-v1/mpc-recursive-finite-shift16-full-review28-v1.json')
OUT=Path('/tmp/mpc-recursive16-new2-independent-foundations28-findings-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
def checked(r):
    p=Path(r['file']);p=p if p.is_absolute()else ROOT/p
    assert not p.is_symlink() and p.is_file() and sha(p)==r['sha256'],str(p)
    return p
def codes(d,w):
    keys=[k for k in ('exit_code','actual_exit_code','actual_runner_exit_code')if k in d]
    assert keys and all(type(d[k])is int and d[k]==w for k in keys)
def bodies(s):
    ms=list(re.finditer(r'^theorem\s+(\w+)\b',s,re.M))
    return {m.group(1):s[m.start():ms[i+1].start()if i+1<len(ms)else len(s)]for i,m in enumerate(ms)}
assert sha(REQUEST)=='bd5678123631d523b4f686382741de585c34619311599b4fd01c5f5d222f1a95'
j=read(REQUEST);assert j['errors']==[]
assert all(j[k]is False for k in ('whole_exercise18_approved','whole_material_units_approved','canonical_or_named_execution_claimed','current27_cutoff_changed'))
selection=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']
owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']}
held={n:r['sha256']for n,r in selection['proof_files'].items()};held.update(assets);held.update(owners)
held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94','reports/full-coverage/checkpoint-27-selection.json':'ff2cf797d5171fbd9d7ed94683e779cdb442e476dde6f2ccc76470d81186bcd'})
# Preserve the authoritative selection SHA literal without deriving source semantics from it.
held['reports/full-coverage/checkpoint-27-selection.json']='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
assert len(selection['proof_files'])==1175 and len(assets)==31 and len(owners)==5
def guard():
    for n,h in held.items():assert sha(ROOT/n)==h,n
started=datetime.now(timezone.utc).isoformat();guard()
source=checked(j['source']);s=source.read_text();assert s==j['entire_source']
assert sha(source)=='69886d315ac97759a5c0eb3a2299eeae83031014c2faddebf17236a0b598eadf'
assert len(bodies(s))==j['public_theorem_count']==16
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
old=checked(j['exact_old10_entire_source']).read_text()
scalar=checked(j['exact_scalar4_entire_body']).read_text()
prefix='import Mathlib.Algebra.Field.GeomSum\n\n'+old+'\n'+scalar[scalar.index('set_option autoImplicit false'):]
assert s.startswith(prefix)
new=bodies(s[len(prefix):]);assert len(new)==2
assert ['SafeLearning.CompleteCoreMPCTypedDomainShift28.'+n for n in new]==j['new_public_theorem_names']
prior_refs=[('/tmp/mpc-old-plan-reference4-full-review28-v1/mpc-old-plan-reference4-full-review28-v1.json','entire_old_reference4_request_body_and_time'),('/tmp/mpc-exact-tightening4-full-review28-v1/mpc-exact-tightening4-full-review28-v1.json','entire_scalar4_request_body_and_time'),('/tmp/mpc-old-reference4-and-tightening4-independent-foundations28-v1.json','entire_old8_independent_peer_body_and_time')]
for p,k in prior_refs:assert read(p)==j[k],k
assert sha(prior_refs[2][0])=='b470edba6661ba2e92a993fa835024dd5cc2991a448677187a31f719f4cc9823'
domain=read('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-review-v2.json')
assert sha('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-review-v2.json')=='37ff22c2f37201bdef612feb6ce3b1fc47748b1db94305c9df36ba1888ff2dcc'
assert j['entire_old8_independent_peer_body_and_time']['entire_original_domain_interpretation_peer_body_and_time']==domain
inv=read(ROOT/'book/coverage/inventory.json')
assert next(u for u in inv['exercises']if u['key']=='lyapunov-mpc.html::exercise-18')==j['current_source55_entire_exercise18']
units={u['key']:u for u in inv['material_source_units']}
for u in j['current_source55_whole_physical_context_units']:
    assert units[u['key']]==u
    assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
    assert sha(ROOT/u['source'])==u['source_sha256']
closure={str(REQUEST):sha(REQUEST)}
for original,alias in j['original_closed_byte_aliases'].items():
    p=checked(alias);assert Path(original).read_bytes()==p.read_bytes(),original
    closure[original]=alias['sha256'];closure[str(p)]=alias['sha256']
assert len(j['original_closed_byte_aliases'])==1267
for idx,t in enumerate(j['actual_trials_full_original_bodies_times_and_raw']):
    actual=read(checked(t['record']));assert actual==t['entire_original_body_and_time'];codes(actual,1 if idx==0 else 0)
    assert actual['actual_command']==['lake','env','lean',actual['source']] and actual['actual_workdir']==str(ROOT/'verification/lean')
    assert actual['protection_errors']==[] and actual['source_unchanged']is True
    assert sha(actual['source'])==actual['source_sha256_before']==actual['source_sha256_after']==actual['source_snapshot_sha256']==sha(actual['source_snapshot'])
    assert checked(t['snapshot']).read_text()==t['entire_original_source']==Path(actual['source']).read_text()
    assert checked(t['raw_log']).read_text()==t['entire_raw_log'] and sha(actual['raw_log'])==actual['raw_log_sha256']
    assert len(re.findall(r'^.*:\d+:\d+: warning:',t['entire_raw_log'],re.M))==t['actual_warning_count']==13
    assert actual['protected_selected27_proof_sources']==1175 and actual['unchanged_current55_book_assets']==31 and actual['unchanged_installed27_live_owners']==5
    assert actual['installed27_owner_sha256']==owners
    assert checked(actual['original_actual_runner'])==Path('/tmp/root_tmp_lean28_runner_v4.py')
    for n,h in actual['pinned_installed27_provenance_sha256'].items():assert sha(ROOT/n)==h,n
dependency=ROOT/'verification/lean/SafeLearning/CompleteCoreMPCFirstSuccessor27.lean'
decisions=[
 {'theorem':'actual_old_feasible_plan_and_source_budgets_construct_a_true_shifted_prediction','approved_component':True,'missing_component_clauses':[],'reason':'The old plan is a genuine FiniteFeasiblePrediction with the exact source epsilon formula. The original terminal row condition and nonnegative exact tightening imply all old shifted-reference domains/rows; robust terminal invariance at w=0 yields its nominal invariance, with radius nonnegative proved from the exact formula. The already reviewed exact radius identity supplies every tracking value/radius budget and max(H,L*k) supplies both increments. The actual tracking constructor then derives all new state/input/terminal constraints; no shifted feasible prediction or its tightened rows are premises. The initial next membership and V bound remain explicit conditional bootstrap interfaces. This is a valid composition component under the qualified typed-domain reading, not a derivation of those interfaces, physical norm correspondence, optimizer existence or whole18.'},
 {'theorem':'actual_geometric_tracking_radius_is_the_printed_terminal_ball_radius','approved_component':True,'missing_component_clauses':[],'reason':'For rho>=0,cL>0,cU>=0 the nonnegative factor q^N*sqrt(cU/cL), q=sqrt(rho), has square rho^N*cU/cL. Equality of the nonnegative square roots derives the exact printed factor, and multiplication gives the radius equality for arbitrary real lambda and eta. In the physical source their positivity is stronger, so zero rho/eta/lambda remain covered. No terminal membership, constraint or feasibility conclusion is an algebraic premise.'}
]
assert set(new)=={d['theorem']for d in decisions}
guard();closure.update({str(ROOT/n):h for n,h in held.items()});closure[str(dependency)]=sha(dependency)
d={'status':'passed_independent_full_recursive16_two_new_component_review28','errors':[],'reviewer':'/root/foundations_recovery28, independent of Applied author','reviewed_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'component_count':2,'request':ref(REQUEST),'entire_original_request_body_and_time':j,'source':j['source'],'entire_source':s,'all16_complete_bodies_and_definitions_manually_read':True,'entire_new2_reviewed_bodies':new,'component_decisions':decisions,'reused_primary_dependency':{'source':ref(dependency),'entire_source':dependency.read_text()},'entire_original_old8_review_body_and_time':j['entire_old8_independent_peer_body_and_time'],'entire_original_domain_interpretation_review_body_and_time':domain,'adopted_partial_domain_reading_qualified_current55_unchanged':True,'whole_exercise18_approved':False,'whole_material_units_approved':False,'remaining_whole_source_obligations':j['remaining_full_source_obligations'],'actual_successful_trial':j['actual_trials_full_original_bodies_times_and_raw'][1]['record'],'actual_emitted_warning_count':13,'current_selected1175_sources31_assets5_owners_rehashed_before_after':True,'closed_evidence_sha256':closure,'actual_checker':ref(Path(__file__)),'scope':'Full manual mathematical read of all16 cumulative bodies/definitions, full literal physical context and exercise18, plus measured native evidence identity/guard reader. Reader runtime is not claimed as duration of the preceding manual semantic read. Two component decisions only; explicit first-successor interfaces, physical norm/scaled-set instantiation, actual optimizer/positive-horizon/controller safety/convergence and validation composition remain open. Current55 has not installed the adopted stronger typed-domain clarification. No compiler rerun or canonical source/proof/owner/mapping change.'}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'component_count':2,'actual_emitted_warning_count':13,'whole_exercise18_approved':False}))
