from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re

ROOT=Path('/home/oxrexkevin/SafetyBased')
OUTPUT=Path('/tmp/mpc-old-reference4-and-tightening4-independent-foundations28-findings-v1.json')
assert not OUTPUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
def checked(r):
    p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
    assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'],str(p)
    return p
def codes(d,w):
    keys=[k for k in ('exit_code','actual_exit_code','actual_runner_exit_code') if k in d]
    assert keys and all(type(d[k]) is int and d[k]==w for k in keys)
def bodies(s):
    matches=list(re.finditer(r'^theorem\s+(\w+)\b',s,re.M))
    return {m.group(1):s[m.start():matches[i+1].start() if i+1<len(matches) else len(s)] for i,m in enumerate(matches)}
selection=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
assert len(selection['proof_files'])==selection['proof_file_count']==1175
assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];assert len(assets)==31
owners={r['destination']:r['candidate']['sha256'] for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']};assert len(owners)==5
held={n:r['sha256'] for n,r in selection['proof_files'].items()};held.update(assets);held.update(owners)
held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94','reports/full-coverage/checkpoint-27-selection.json':'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'})
def guard():
    for n,h in held.items():assert sha(ROOT/n)==h,n
started=datetime.now(timezone.utc).isoformat();guard()
requests=[Path('/tmp/mpc-old-plan-reference4-full-review28-v1/mpc-old-plan-reference4-full-review28-v1.json'),Path('/tmp/mpc-exact-tightening4-full-review28-v1/mpc-exact-tightening4-full-review28-v1.json')]
expected=['c888f3b607005ab82b193fadaf54d2c033817c913702491490c00450097b2142','9f725128bbc5a5e8476e356439a2d3df57554acdd67f5ca2d1e9d45308ebf655']
prior_packet=read('/tmp/mpc-shift15-components-full-review28-v1/mpc-shift15-components-full-review28-v1.json')
prior_peer=read('/tmp/mpc-shift15-components-independent-foundations28-v1.json')
domain_peer=read('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-review-v2.json')
assert sha('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-review-v2.json')=='37ff22c2f37201bdef612feb6ce3b1fc47748b1db94305c9df36ba1888ff2dcc'
closure={str(p):sha(p) for p in requests}
components=[]
for i,path in enumerate(requests):
    assert sha(path)==expected[i]
    j=read(path);source=checked(j['source']);s=source.read_text();decls=bodies(s)
    assert s==j['full_source_text' if i==0 else 'entire_source_body']
    assert not re.search(r'\b(sorry|admit|axiom)\b',s)
    assert j['errors']==[] and all(j[k] is False for k in ('whole_exercise18_approved','whole_material_units_approved','canonical_or_named_execution_claimed','current27_cutoff_changed'))
    assert j['entire_original15_packet_body_and_time']==prior_packet
    assert j['entire_original15_'+('independent_peer' if i==0 else 'peer')+'_body_and_time']==prior_peer
    for original,alias in j['original_closed_byte_aliases'].items():
        assert Path(original).read_bytes()==checked(alias).read_bytes()
        closure[original]=alias['sha256'];closure[alias['file']]=alias['sha256']
    trialref=j['actual_standalone_evidence' if i==0 else 'actual_standalone_ref'];trial=read(checked(trialref));codes(trial,0)
    assert trial==j['actual_standalone_record']
    assert trial['actual_command']==['lake','env','lean',str(source)] and trial['actual_workdir']==str(ROOT/'verification/lean')
    assert trial['source_sha256_before']==trial['source_sha256_after']==trial['source_snapshot_sha256']==sha(source)
    assert Path(trial['source_snapshot']).read_bytes()==source.read_bytes()
    assert trial['protection_errors']==[] and trial['protected_proof_sources']==1175
    assert trial['unchanged_current55_book_assets']==31 and trial['unchanged_installed27_live_owners']==5
    assert trial['installed27_owner_sha256']==owners
    assert checked(trial['original_actual_runner'])==Path('/tmp/root_tmp_lean28_runner_v4.py')
    assert trial['original_actual_runner']['sha256']=='8fe26e9954800b4e104db5a079eb2e9295e3680064fe7ebaaa74b496e60ec49b'
    for n,h in trial['pinned_installed27_provenance_sha256'].items():assert sha(ROOT/n)==h,n
    raw=Path(trial['raw_log']).read_text();assert sha(trial['raw_log'])==trial['raw_log_sha256']
    warnings=re.findall(r'^.*:\d+:\d+: warning:.*$',raw,re.M)
    assert len(warnings)==(9 if i==0 else 4)==j['actual_emitted_warning_count' if i==0 else 'actual_warning_count']
    if i==0:
        prefix=checked(j['exact_prior_finite6_byte_prefix']).read_text();assert s.startswith(prefix)
        assert s[len(prefix):]==j['new_full_source_suffix']
        new=bodies(s[len(prefix):]);assert len(new)==4
        assert [f'SafeLearning.CompleteCoreMPCTypedDomainShift28.{n}' for n in new]==j['new_public_theorem_names']
        assert checked(j['raw_warning_log']).read_text()==raw
        decisions=[
          {'theorem':'actual_old_feasible_plan_extends_by_the_terminal_plant_step','approved_component':True,'reason':'For j<N the extension is literally the old state/input and old dynamics; at j=N it is literally f(z_N,k_f(z_N)). No recurrence after N is claimed. The constant definition outside this interval supplies only the one extended point.'},
          {'theorem':'actual_old_shifted_reference_has_its_true_later_tightened_rows','approved_component':True,'reason':'At j+1<N both rows come from the old feasible prediction at index j+1; at j+1=N both come from the original terminal stage row condition. The source later level epsilon(j+1) is preserved. New tracking rows are not premises.'},
          {'theorem':'actual_old_reference_extension_stays_in_the_original_domains','approved_component':True,'reason':'Old and terminal tightened rows plus epsilon>=0 imply the actual untightened X rows and Ut subset U. At N+1 the genuine nominal terminal-invariance assumption gives another terminal point, and the terminal stage rows then give X and k_f of that point in U. This is the nominal extension, not new actual successor membership. N=0 is handled by the terminal branches.'},
          {'theorem':'actual_old_feasible_plan_supplies_every_shifted_reference_assumption','approved_component':True,'reason':'The shifted nominal/reference are the actual old extension at j+1. The theorem derives all domains through j=N, dynamics through j<N, old later state/input row bounds and nominal_N=f(z_N,k_f(z_N)). It supplies the prior tracking constructor reference interface from a genuine old feasible plan, with no shifted feasible plan as a premise.'}
        ]
    else:
        new=decls;assert len(new)==4
        failed=j['true_original_failed_trial'];codes(failed,1)
        original_failed=read('/tmp/applied-mpc-exact-tightening28-trial1.json');assert failed==original_failed
        assert failed['protection_errors']==[]
        assert sha(failed['source_snapshot'])==failed['source_snapshot_sha256']==failed['source_sha256_before']==failed['source_sha256_after']
        assert sha(failed['raw_log'])==failed['raw_log_sha256']
        decisions=[
          {'theorem':'actual_original_radius_has_the_exact_geometric_value_budget','approved_component':True,'reason':'The actual radius is q^j lambda eta sqrt(cU/cL), q=sqrt(rho). Nonnegative rho,cU,lambda,eta and positive cL imply nonnegative radius; the proof squares q and the ratio and cancels cL to derive rho^j[cU(lambda eta)^2]=cL radius_j^2. The desired scalar identity is derived, including eta=0 or cU=0.'},
          {'theorem':'actual_original_tightening_has_exact_increments_and_is_monotone','approved_component':True,'reason':'The actual source tightening is epsilon times sum_{i<j} q^i. The finite-sum successor identity derives the exact epsilon q^j increment, and epsilon>=0 with q>=0 derives nonnegative levels and monotonicity. No rho interval is needed for this finite algebra.'},
          {'theorem':'actual_original_max_norm_tightening_covers_both_tracking_rows','approved_component':True,'reason':'For R=lambda eta sqrt(cU/cL), epsilon=R max(H,Lk) is nonnegative. The true scalar radius is q^j R and the exact increment is epsilon q^j. max(H,Lk) dominates each bound, deriving both H radius_j and L(k radius_j) budgets. No state or input membership conclusion is inserted as a hypothesis.'},
          {'theorem':'actual_original_tightening_is_the_printed_geometric_quotient','approved_component':True,'reason':'For 0<=rho<1, sqrt(rho)<1 and 1-sqrt(rho)>0. The actual finite-sum formula is transformed by the geometric-sum identity to epsilon(1-q^j)/(1-q), with the nonzero denominator explicitly justified, including rho=0.'}
        ]
    assert set(new)=={d['theorem'] for d in decisions}
    components.append({'request':ref(path),'entire_original_request_body_and_time':j,'source':j['source'],'entire_source':s,'entire_reviewed_component_bodies':new,'all_definitions_and_complete_source_bodies_read':True,'component_decisions':decisions,'actual_original_standalone_record_and_time':trial,'entire_original_raw_log':raw,'actual_emitted_warning_count':len(warnings),'remaining_original_source_obligations':j['remaining_full_source_obligations' if i==0 else 'required_continuing_instantiations']})
guard()
closure.update({str(ROOT/n):h for n,h in held.items()})
d={'status':'passed_independent_full_old_reference4_and_exact_tightening4_component_review28','errors':[],'reviewer':'/root/foundations_recovery28, independent of Applied author','reviewed_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'component_count':8,'components':components,'entire_original15_peer_body_and_time':prior_peer,'entire_original_domain_interpretation_peer_body_and_time':domain_peer,'adopted_partial_domain_reading_qualified_current55_unchanged':True,'whole_exercise18_approved':False,'whole_material_units_approved':False,'remaining_composition_obligations':['Compose the actual old-plan reference, exact tightening/radius, original disturbance bootstrap and derived tracking constructor into one feasible prediction theorem.','Show exact original infinity matrix/row norms and input infinity disturbance law correspond to the typed spaces and row bounds.','Derive the printed terminal radius sqrt(rho^N*cU/cL)*lambda*eta from the radius definition and instantiate robust terminal invariance at that exact bound.','Handle zero-dimensional state branch and positivity/zero-scale bounded-recession issue if scaled polytopes rather than actual row inequalities are used.','Supply actual feasible optimizer/control selection (including positive horizon when a first input is used), then the derived one-step certificate and probability/validation composition.','The approved explicit typed-domain reading is an adopted interpretation; current55 has not installed that clarification and the weaker total ambient reading retains its counterexample.'],'current_selected1175_sources31_assets5_owners_rehashed_before_after':True,'closed_evidence_sha256':closure,'actual_checker':ref(Path(__file__)),'scope':'Full manual mathematical component review plus measured native evidence reader; the reader checks evidence identities and guards, not an automated source semantics proof. No compiler rerun, owner/proof/source installation or whole18 approval.'}
with OUTPUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'errors':[],'component_count':8,'findings':ref(OUTPUT)}))
