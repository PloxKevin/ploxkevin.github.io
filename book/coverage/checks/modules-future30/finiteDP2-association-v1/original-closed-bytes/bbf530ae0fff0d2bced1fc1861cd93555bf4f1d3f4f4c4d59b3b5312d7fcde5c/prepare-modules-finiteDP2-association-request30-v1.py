from pathlib import Path
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/finiteDP2-association-v1';assert not B.exists();B.mkdir(parents=True)
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={};refs={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb')as f:f.write(p.read_bytes())
 assert sha(q)==h;r={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;refs[r['file']]=h;return r
P=R/'book/coverage/checks/modules-future30/duality55-components-v1/modules-duality55-full-source-current-literal-component-review-request30-v2.json';p=json.loads(P.read_bytes());refs.update(p['required_evidence_artifacts_sha256']);aliases.update(p['original_closed_byte_aliases']);prior=copy(P)
S=Path('/tmp/CompleteModulesViabilityFiniteDPCommonOptimizer30-draft-v1.lean');t=S.read_text();assert sha(S)=='47ef3461cf9fc98060d3fdc16f4f0c2aa98fe5c4f22a5a69b81945ebc651f2cf';names=[d['name']for d in lean_names.declarations(t)if d['kind']in ['theorem','lemma']];assert len(names)==2
N=Path('/tmp/modules-viability-finiteDP-common2-owner29-trial1.json');n=json.loads(N.read_bytes());assert n['actual_exit_code']==n['actual_runner_exit_code']==0 and n['protection_errors']==[] and n['source_unchanged']
assert n['actual_command']==['lake','env','lean',str(S)]and n['actual_workdir']==str(R/'verification/lean')
assert sha(S)==n['source_sha256_before']==n['source_sha256_after']==sha(n['source_snapshot'])==n['source_snapshot_sha256'];assert sha(n['raw_log'])==n['raw_log_sha256'];assert Path(n['raw_log']).read_bytes()==b''
assert [n[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
selected=[]
for name in ['CompleteAppliedBellman','CompleteAppliedBellmanReturns','CompleteFiniteHistoryPathLinearProgram','CompleteFiniteControlledPathMeasure','CompleteFiniteControlledPathMeasureLaws','CompleteFiniteMarkovPathCorrespondence','CompleteFiniteCMDPDeterministicVertices','CompleteFiniteCMDPOccupancy','CompleteFiniteCMDPFlow']:
 selected.append(copy(R/'verification/lean/SafeLearning'/(name+'.lean')))
primary=copy(R/'verification/lean/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean')
for f in [__file__,'/tmp/run-modules-finiteDP2-association-request30-preparation-v1.py','/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py']:copy(f)
d={'status':'prepared_actual_kernel0_finiteDP2_common_stationary_optimizer_association_independent_review_pending','source':copy(S),'full_source_body':t,'public_theorem_count':2,'public_theorem_names':names,'actual_native':copy(N),'actual_source_snapshot':copy(n['source_snapshot']),'actual_raw_log':copy(n['raw_log']),'true_first_trial0_empty_raw_zero_warnings':True,'original_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'original_body_and_times_untouched':True,'selected_complete_dependency_sources':selected,'complete_primary_fixedpoint_source':primary,'original55_full_current_literal_and_component_request':prior,'current_full_context':p['current_full_context'],
 'requested_semantic_scope':'The printed finite deterministic dynamic-programming common stationary attainment parenthetical in Exercise7.5(a). Genuine Bellman contraction yields a real fixed point, finite action maxima choose one stationary policy before initial distribution. Actual all-history path upper bound and actual greedy path equality establish its global optimality for every initial PMF simultaneously. Deterministic pure transitions and reward-minus-penalty-cost are actual specializations, not optimizer existence premises.',
 'actual_process_semantics':'The selected pathReturn is the actual path-measure expected infinite discounted return and its occupancy linear identity, not a supplied desired value. Full selected path/flow/Markov/greedy proofs are retained for independent used-chain read.',
 'remaining_scope':'This closes only the common stationary finite-DP association if independently approved. It does not prove general finite-CMDP dual-multiplier existence, arbitrary-clock-penalty common attainment, actual Chain delta2 profile or the oscillation wording qualifier; whole Exercise7.5 and its current rows remain pending.',
 'whole_exercise_review_requested':False,'whole_exercise_approved':False,'source_applied':False,'canonical_pairs_executed':False,'coverage_complete':False,'supplementary_after_frozen29_manifest':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':refs}
assert all((R/f).resolve().is_relative_to(R.resolve())and sha(R/f)==h for f,h in refs.items())
O=B/'modules-finiteDP2-common-stationary-optimizer-association-review-request30-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'refs':len(refs),'aliases':len(aliases)}))
