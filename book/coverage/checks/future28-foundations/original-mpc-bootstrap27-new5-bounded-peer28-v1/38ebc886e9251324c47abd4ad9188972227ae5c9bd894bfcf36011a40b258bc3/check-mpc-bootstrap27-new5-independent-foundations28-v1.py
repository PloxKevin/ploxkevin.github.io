from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQ=Path('/tmp/mpc-bootstrap-recursive27-bounded-review28-v2/mpc-bootstrap-recursive27-bounded-review28-v2.json')
OUT=Path('/tmp/mpc-bootstrap27-new5-independent-foundations28-findings-v1.json');assert not OUT.exists()
def sha(p):
    digest=hashlib.sha256()
    with Path(p).open('rb')as f:
        while block:=f.read(1024*1024):digest.update(block)
    return digest.hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
def checked(r):
    p=Path(r['file']);p=p if p.is_absolute()else ROOT/p
    assert p.is_file()and not p.is_symlink()and sha(p)==r['sha256'],str(p)
    return p
def samebytes(p,q):
    with Path(p).open('rb')as a,Path(q).open('rb')as b:
        while True:
            x=a.read(1024*1024);y=b.read(1024*1024)
            assert x==y,(str(p),str(q))
            if not x:break
def codes(d,w):
    keys=[k for k in ('exit_code','actual_exit_code','actual_runner_exit_code')if k in d]
    assert keys and all(type(d[k])is int and d[k]==w for k in keys)
def bodies(s):
    ms=list(re.finditer(r'^theorem\s+(\w+)\b',s,re.M))
    return {m.group(1):s[m.start():ms[n+1].start()if n+1<len(ms)else len(s)]for n,m in enumerate(ms)}
assert sha(REQ)=='c99ad0415be564e7a9d75e6ce4ec34657a5e02b2d27b9d6ae94617414022d3d8'
j=read(REQ);assert j['errors']==[]
assert all(j[k]is False for k in ('whole_exercise18_approved','whole_material_units_approved','canonical_or_named_execution_claimed','current27_cutoff_changed'))
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']
owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']}
held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners)
held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94','reports/full-coverage/checkpoint-27-selection.json':'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'})
assert len(sel['proof_files'])==1175 and len(assets)==31 and len(owners)==5
def guard():
    for n,h in held.items():assert sha(ROOT/n)==h,n
started=datetime.now(timezone.utc).isoformat();guard()
source=checked(j['source']);s=source.read_text();decls=bodies(s)
assert s==j['entire_source']and sha(source)=='4823f064d2ba822bd76e90701282d94b6234e95e00b8f79edd3d3ee03061af35'
assert len(decls)==j['public_theorem_count']==27
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
old=checked(j['exact_recursive16_entire_source']).read_text()
assert s.startswith('import Mathlib.Analysis.Normed.Module.RCLike.Real\n\n'+old)
for row in j['exact_old_geometry4_ordered2_and_rows4_namespace_bodies']:
    text=checked(row['source']).read_text();assert text==row['entire_original_source']
    assert text[text.index('namespace '):]in s
prior=[]
for r in j['retained_original_prior_full_review_bytes_and_times']:
    p=checked(r['ref']);body=read(p)
    assert body['reviewed_at_utc']==r['original_reviewed_at_utc']and body['status']==r['original_status']and body['errors']==r['original_errors']==[]
    assert r['entire_original_body_and_time_preserved_offline']is True and r['semantic_decision_relabelled']is False
    prior.append(r)
large=j['retained_original_unmodified_large_request'];p=checked(large)
assert p.stat().st_size==large['bytes']and large['offline_tmp_only']is True
original=read(p)
assert original['prepared_at_utc']==large['original_prepared_at_utc']
for k in ('source','entire_source','public_theorem_count','new_public_theorem_names','component_scopes','actual_trials_full_original_bodies_times_and_raw','remaining_full_source_obligations','original_closed_byte_aliases'):assert original[k]==j[k],k
del original
inv=read(ROOT/'book/coverage/inventory.json');units={u['key']:u for u in inv['material_source_units']}
assert next(u for u in inv['exercises']if u['key']=='lyapunov-mpc.html::exercise-18')==j['current_source55_entire_exercise18']
for u in j['current_source55_whole_physical_context_units']:
    assert units[u['key']]==u and hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']and sha(ROOT/u['source'])==u['source_sha256']
closure={str(REQ):sha(REQ)}
for original,alias in j['original_closed_byte_aliases'].items():
    p=checked(alias);assert sha(original)==alias['sha256'];samebytes(original,p)
    closure[original]=alias['sha256'];closure[str(p)]=alias['sha256']
assert len(j['original_closed_byte_aliases'])==2542
for idx,t in enumerate(j['actual_trials_full_original_bodies_times_and_raw']):
    a=read(checked(t['record']));assert a==t['entire_original_body_and_time'];codes(a,[0,1,0][idx])
    assert a['actual_command']==['lake','env','lean',a['source']]and a['actual_workdir']==str(ROOT/'verification/lean')
    assert a['protection_errors']==[]and a['source_unchanged']is True
    assert sha(a['source'])==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==sha(a['source_snapshot'])
    assert Path(a['source_snapshot']).read_text()==t['entire_source_snapshot']
    assert checked(t['raw_log']).read_text()==t['entire_raw_log']and sha(a['raw_log'])==a['raw_log_sha256']
    assert len(re.findall(r'^.*:\d+:\d+: warning:',t['entire_raw_log'],re.M))==t['actual_emitted_warning_count']==[0,15,15][idx]
    assert a['protected_selected27_proof_sources']==1175 and a['unchanged_current55_book_assets']==31 and a['unchanged_installed27_live_owners']==5
    assert a['installed27_owner_sha256']==owners
    assert checked(a['original_actual_runner'])==Path('/tmp/root_tmp_lean28_runner_v4.py')
    for n,h in a['pinned_installed27_provenance_sha256'].items():assert sha(ROOT/n)==h,n
newnames=[n.rsplit('.',1)[1]for n in j['new_public_theorem_names']];assert len(newnames)==5
decisions=[
 {'theorem':newnames[0],'approved_component':True,'missing_component_clauses':[],'reason':'The real H matrix row is a continuous linear map on the Euclidean state coordinates. Its evaluation is literally H*x, and its operator bound is derived from the actual matrix infinity row-sum inequality combined with coordinate infinity norm <= Euclidean norm. No operator bound is a premise. Empty state/row indices remain permitted.'},
 {'theorem':newnames[1],'approved_component':True,'missing_component_clauses':[],'reason':'The real Lt row is a continuous linear map on Pi infinity-norm input coordinates. Its evaluation is literally Lt*u, and norm_le_pi_norm with the actual infinity matrix operator inequality derives its operator bound. This preserves the input infinity norm used for disturbances.'},
 {'theorem':newnames[2],'approved_component':True,'missing_component_clauses':[],'reason':'For every real epsilon, the constructor state-row inequalities are exactly the literal matrix inequalities H*x<=1-epsilon. Scalar multiplication of the set (1-epsilon)X is not inferred, especially at zero or negative scale.'},
 {'theorem':newnames[3],'approved_component':True,'missing_component_clauses':[],'reason':'For every real epsilon, the constructor input-row inequalities are exactly Lt*u<=1-epsilon with actual Pi input coordinates. Scalar-multiple set equivalence remains a separate open obligation.'},
 {'theorem':newnames[4],'approved_component':True,'missing_component_clauses':[],'reason':'For a genuinely positive horizon, old stage0 rows prove initial X membership and actual u0 in the eroded input set. The erosion yields both u0 and u0+d in U. Old dynamics plus terminal rows/invariance derive the entire shifted nominal/reference interface. In a subsingleton state space the perturbed successor equals the nominal successor, yielding original X membership and V=0 directly. In a nontrivial state space the actual H polytope contains a positive origin ball; continuity and the genuine local lower/upper bounds produce a distinct local pair and derive cL<=cU. The exact epsilon formula then supplies the first state margin; original Assumptions2/3 plus continuity and conditional upper bound derive successor X membership before the local V bootstrap. Exact actual H/Lt row operator bounds and terminal radius conversion feed the previously reviewed constructor, deriving all new constraints and terminal membership. No hnextX/hnextV, cL<=cU, shifted constraints or new feasible prediction are premises. The typed contraction certificate remains conditional on the adopted partial-domain reading; its Pi feedback clause must still be explicitly obtained from the printed Euclidean feedback bound before whole-source coverage.'}
]
guard();closure.update({str(ROOT/n):h for n,h in held.items()})
compactprior=ROOT/'book/coverage/checks/future28-foundations/mpc-recursive16-new2-independent-foundations28-byte-binding-v2.json'
closure[str(compactprior)]=sha(compactprior)
d={'status':'passed_independent_full_bootstrap27_five_new_component_review28','errors':[],'reviewer':'/root/foundations_recovery28, independent of Applied authorship','reviewed_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'source':j['source'],'entire_source':s,'all27_complete_bodies_and_definitions_manually_read':True,'complete_reviewed_new5_bodies':{n:decls[n]for n in newnames},'component_count':5,'component_decisions':decisions,'full_current_source55_exercise18':j['current_source55_entire_exercise18'],'full_current_source55_physical_context_units':j['current_source55_whole_physical_context_units'],'original_native_trial_records_and_times':j['actual_trials_full_original_bodies_times_and_raw'],'actual_successful_trial':j['actual_trials_full_original_bodies_times_and_raw'][2]['record'],'actual_emitted_warning_count':15,'prior_full_review_exact_refs_and_original_times_unchanged':prior,'prior_recursive16_compact_original_decision_binding':ref(compactprior),'original_unmodified_large_request_preserved_offline':large,'adopted_partial_domain_reading_qualified_current55_unchanged':True,'whole_exercise18_approved':False,'whole_material_units_approved':False,'remaining_whole_source_obligations':j['remaining_full_source_obligations'],'current_selected1175_sources31_assets5_owners_rehashed_before_after':True,'closed_evidence_sha256':closure,'actual_checker':ref(Path(__file__)),'scope':'Full manual mathematical component review with measured native evidence reader. All original prior full bodies/times are preserved offline and bound by exact SHA rather than recursively embedded. Runtime is only the native reader runtime, not the duration of preceding manual source review. Five conditional component approvals; positive horizon, Euclidean-feedback conversion, scalar-multiple sets, actual attained MPC optimizer/controller, all-time safety/convergence and finite-entry fixed-batch validation composition remain separate. Source55/1175/31/five unchanged; no compiler, canonical proof/source/owner/mapping installation or whole18 approval.'}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'component_count':5,'whole_exercise18_approved':False,'actual_emitted_warning_count':15}))
