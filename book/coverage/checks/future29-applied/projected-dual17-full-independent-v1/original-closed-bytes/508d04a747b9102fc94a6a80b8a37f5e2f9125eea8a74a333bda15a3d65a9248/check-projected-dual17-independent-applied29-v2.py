from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');REQ=R/'book/coverage/checks/future29-core/projected-dual-drift17-v1/core-projected-dual-drift17-full-semantic-review-request29-v1.json';C=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):p=Path(q['file']);return p if p.is_absolute() else R/p
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
ctx=json.loads(C.read_bytes());pins={**ctx['pins_sha256'],**ctx['held_current_source_sha256']}
def guard():
 for n,h in pins.items():assert sha(R/n)==h,n
guard();before={n:sha(R/n) for n in pins};assert sha(REQ)=='6b3364e35dada2299eebfe1b791a6026ac0e10342257592620c4a01b7b8907b5';d=json.loads(REQ.read_bytes());closed={str(REQ):sha(REQ),str(C):sha(C),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q) if isinstance(q,dict) else Path(q)
 if isinstance(q,dict):assert sha(p)==q['sha256'],str(p)
 closed[str(p)]=sha(p);return p
for original,q in d['exact_original_tmp_receipts_sources_logs_and_helpers'].items():
 p=add(q);assert p.resolve().is_relative_to(R)
 o=Path(original)
 if o.exists():assert sha(o)==sha(p),original
for original,q in d['current_root_references'].items():assert sha(Path(original))==sha(add(q))
src=add(d['final_actual_source']);s=src.read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
ns='SafeLearning.CompleteCoreProjectedDualDrift29.';parsed=[{'name':ns+n,'kind':k} for k,n in re.findall(r'^(def|theorem)\s+(\w+)',s,re.M)]
assert parsed==d['source_level_public_names'] and len(parsed)==17 and sum(q['kind']=='theorem' for q in parsed)==12
natives=[];warnings=[]
for i,expected in zip(range(1,6),[1,0,0,1,0]):
 q=d['exact_original_tmp_receipts_sources_logs_and_helpers'][f'/tmp/root-core-projected-dual-drift29-trial{i}.json'];p=add(q);n=json.loads(p.read_bytes())
 assert type(n['actual_exit_code']) is int and n['actual_exit_code']==expected and n['protection_errors']==[]
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 raw=add(d['exact_original_tmp_receipts_sources_logs_and_helpers'][n['raw_log']]);snapshot=add(d['exact_original_tmp_receipts_sources_logs_and_helpers'][n['source_snapshot']])
 assert n['raw_log_sha256']==sha(raw) and n['source_snapshot_sha256']==n['source_sha256_before']==n['source_sha256_after']==sha(snapshot)
 assert n['source_unchanged'] is True and n['finished_at_utc']>=n['started_at_utc']
 natives.append(q);warnings.append(len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M)))
assert warnings==[0,5,5,5,5] and sha(snapshot)==sha(src)
base=json.loads((R/'book/coverage/inventory.json').read_bytes());units={r['key']:r for r in base['material_source_units']};owner=json.loads((R/'book/coverage/core.json').read_bytes())
for row in d['literal_units']:
 key=row['source_unit_keys'][0];literal=units[key]
 assert row['source_text']==row['statement_in_prose']==literal['source_text'] and row['source_sha256']==literal['source_sha256'] and row['text_sha256']==literal['text_sha256']
 assert any(c==row for c in owner['material_claims']),key
assert d['whole_unit_request_only']=='cmdp.html::node-749' and d['whole_generic_theorem_750_752_or_exercise21_claimed'] is False
apis=[R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean',R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean']
for p in apis:add(p)
for p in ['/tmp/check-projected-dual17-independent-applied29-v1.py','/tmp/run-projected-dual17-independent-applied29-v1.py','/tmp/projected-dual17-independent-applied-actual29-v1.json','/tmp/projected-dual17-independent-applied-actual29-v1.log']:add(p)
assert 'theorem EuclideanSpace.real_norm_sq_eq' in apis[0].read_text() and 'theorem norm_sum_le' in apis[1].read_text()
components=[]
reasons={'actual-entrywise-epoch-update':'The recursive multiplier applies the true max-positive projection to each coordinate. Substituting epochViolation and its coordinate formula gives the printed eta/T epoch sum, indexed by k*T+t for t=0..T-1. This enumerates exactly the source epoch k*T..(k+1)*T-1. The update is pathwise for an arbitrary reward sequence; no sampling or optimality premise is used. Operational T is positive, while total inverse keeps T=0 algebraically harmless.', 'actual-violation-norm-dimension-factor':'Energy is explicitly sum of squared coordinates, identified with the actual Euclidean norm squared. Coordinatewise B bounds derive m*B^2, including m=0. For positive epoch duration the triangle inequality derives the Euclidean bound on the actual average from all individual reward-vector bounds; no unbiasedness is inferred.', 'actual-finite-horizon-energy-complementarity':'Projection reduces squared magnitude. Expanding and summing gives the exact one-step energy estimate and its true induction telescope. Nonnegative final energy plus positive eta and positive N derives the finite-N pairing bound. Nonnegative initialization gives all nonnegative multiplier coordinates. This is finite deterministic algebra, not an expectation or almost-sure theorem.', 'actual-slater-maximizer-drift-algebra':'The actual chosen Lagrangian comparison to the supplied Slater value and a primitive reward upper bound, combined with nonnegative multipliers and coordinate margin, derives the pairing drift. In a stochastic execution, chosen long-run values must still be connected to actual epoch observations by a genuine conditional-unbiasedness hypothesis.'}
for q in d['components_requested']:components.append({**q,'approved':True,'missing_clauses':[],'independent_reason':reasons[q['id']]})
guard();assert before=={n:sha(R/n) for n in pins}
out=Path('/tmp/projected-dual17-independent-applied-findings29-v2.json');assert not out.exists()
out.write_text(json.dumps({'status':'passed_independent_full_projected_dual17_components_and_whole749_semantic_review','reviewer':'/root/applied_next','review_completed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'proof_source':d['final_actual_source'],'all17_public_declarations_12_theorems_and_full_definitions_read':True,'components':components,'whole_material_units':[{'key':'cmdp.html::node-749','entire_current_record':units['cmdp.html::node-749'],'whole_unit_approved':True,'missing_clauses':[],'operational_hypotheses':['positive finite epoch length','actual reward sequence; positive-part coordinate projection'],'correspondence':'step + multiplier recursion, with epochViolation and the exact coordinate formula, is the full displayed update with the ordinary offset enumeration of the epoch.'}],'whole750_752_or_exercise21_approved':False,'remaining_generic_theorem_gaps':['Genuine stochastic sampling and conditional-expectation association to actual Lagrangian maximizers','Tail/moment control and almost-sure trajectory feasibility','Expected long-run near-optimality and legitimate limit or liminf passage','Actual fixed-price selector realization in the monitoring source context'],'primary_direct_read':{'url':'https://arxiv.org/pdf/2102.11941','observed_version':'arXiv2102.11941v2,21Sep2023','locators':'Eq6,Theorem1; AppendixI eq22–30 and Slater comparison37–39','own_bounded_observation':'The primary uses projected epoch updates, cumulative deficits, squared Euclidean energy and Slater comparisons. Its scalar reward bound requires the dimension factor when converted to vector energy. The requested finite pathwise algebra is verified independently; stochastic passages remain pending.'},'used_primary_API_refs':list(map(ref,apis)),'full_current_section7_and_entire749_750_752_read':True,'original_five_actual_trials_bodies_times_and_warnings_retained':natives,'own_reader1_failure_preserved':{'actual':ref('/tmp/projected-dual17-independent-applied-actual29-v1.json'),'reason':'Independent mechanical reader used generic claims key instead of actual Core material_claims; no mathematical decision or compiler failure.'},'actual_lean_exit_codes':[1,0,0,1,0],'actual_warning_header_counts':warnings,'no_Lean_rerun_or_source_owner_canonical_publication_mutation':True,'closed_evidence_sha256':closed,'errors':[]},indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'findings':ref(out),'all_guards_passed':True,'four_components_approved':True,'whole749_only':True}))
