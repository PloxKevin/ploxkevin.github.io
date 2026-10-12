import hashlib,json,re
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/mpc-primary9-independent-foundations29-v1');OUT.mkdir(exist_ok=True)
REQUEST=Path('/tmp/mpc-primary-composition9-full-source-review-request28-v1.json');CTX=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def actualpath(n):return Path(n) if n.startswith('/') else ROOT/n
def pinned(r):p=actualpath(r['file']);assert sha(p)==r['sha256'],r['file'];return p

def guard():
 c=json.loads(CTX.read_text());assert sha(CTX)=='35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
 for fam in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in c[fam].items():assert sha(ROOT/n)==h,n
 return {'context':ref(CTX),'protected_selected_sources':1186,'current_assets':31,'owners':5,'inventory_sha256':sha(ROOT/'book/coverage/inventory.json'),'corrections_sha256':sha(ROOT/'book/coverage/material-corrections.json')}
start=datetime.now(timezone.utc).isoformat();before=guard();assert sha(REQUEST)=='7a948fce3a381368b032459b8f92ea7ba3f70f1a7885421f1730710ae06211dc';r=json.loads(REQUEST.read_text())
for n,h in r['closed_evidence_sha256'].items():assert sha(actualpath(n))==h,n
source=pinned(r['proof_source']);primary=pinned(r['passed_primary_composition_source']);s=source.read_text();q=primary.read_text();old=Path('/tmp/CompleteCoreMPCGlobalOptimizerRecursiveCertificate28-draft-v4.lean').read_text()
assert q.startswith(old)
assert s.startswith(r['exact_prior_primary_composition_after_one_added_import']['added_import_literal']+q)
assert len(r['new_public_names'])==len(set(r['new_public_names']))==r['new_public_theorem_count']==9
for n in r['new_public_names']:assert len(re.findall(r'^theorem '+re.escape(n)+r'\b',s,re.M))==1,n
for body,key in [(r['entire_new_primary_composition_scope'],'namespace SafeLearning.CompleteCoreMPCPrimaryComposition28'),(r['entire_new_validation_scope'],'namespace SafeLearning.CompleteCoreMPCPrimaryValidation28')]:assert body in s
assert 'structure PrimaryMPCIngredients' in s
inventory=json.loads((ROOT/'book/coverage/inventory.json').read_text());materials={x['key']:x for x in inventory['material_source_units']};exercises={x['key']:x for x in inventory['exercises']}
assert exercises['lyapunov-mpc.html::exercise-18']==r['current60_entire_exercise18']
for row in r['current60_entire_material_units']:assert materials[row['key']]==row
original=json.loads(pinned(r['entire_original_installed_exercise18_record']).read_text());owner=json.loads((ROOT/'book/coverage/core.json').read_text());assert next(x for x in owner['exercises'] if x['inventory_key']=='lyapunov-mpc.html::exercise-18')==original
prior=json.loads(pinned(r['exact_prior_full18_peer']).read_text());assert sha(r['exact_prior_full18_peer']['file'])=='f48c65f9c095b6dde4a444743775b21712a3061ada0afa2fa1a9eb82fed40068'
trials=[]
for row in r['actual_trials_including_all_five_genuine_failures']:
 a=json.loads(pinned(row['actual']).read_text());raw=pinned(row['raw']);snap=pinned(row['source_snapshot'])
 assert type(a['actual_exit_code']) is int and a['actual_exit_code']==row['actual_exit_code']
 assert type(a['actual_runner_exit_code']) is int and a['actual_runner_exit_code']==row['actual_exit_code']
 assert a['actual_command']==row['actual_command']==['lake','env','lean',a['source']]
 assert a['actual_workdir']==str(ROOT/'verification/lean') and a['protection_errors']==row['protection_errors']==[]
 assert a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==row['source_snapshot']['sha256']
 assert a['raw_log_sha256']==row['raw']['sha256'] and a['started_at_utc']==row['started_at_utc'] and a['finished_at_utc']==row['finished_at_utc']
 count=len(re.findall(r'^.*\.lean:\d+:\d+: warning:',raw.read_text(),re.M));assert count==row['actual_emitted_warning_diagnostic_count']
 trials.append({'actual':row['actual'],'raw':row['raw'],'source_snapshot':row['source_snapshot'],'actual_exit_code':a['actual_exit_code'],'warning_diagnostic_count':count,'started_at_utc':a['started_at_utc'],'finished_at_utc':a['finished_at_utc'],'elapsed_seconds':a['elapsed_seconds']})
assert sum(t['actual_exit_code']==1 for t in trials)==5
assert trials[-1]['actual_exit_code']==0 and trials[-1]['source_snapshot']['sha256']==r['proof_source']['sha256']
for fam in ['full_selected_dependencies_to_read','full_primary_sources','complete_additional_primary_APIs']:
 for row in r[fam]:pinned(row)
for n,startline,endline,k in [('SafeLearning/lyapunov-mpc.html',484,536,'full_current_page_context_lines484_to536'),('SafeLearning/lyapunov-mpc.html',928,951,'full_current_exercise_context_lines928_to951')]:
 assert r[k]=='\n'.join((ROOT/n).read_text().splitlines()[startline-1:endline])
# Full semantic decisions arise from the independent literal/premise/body read;
# these integrity checks preserve the exact source and actual histories only.
whole=[{'inventory_key':'lyapunov-mpc.html::exercise-18','whole_unit_approved':True,'missing_clauses':[],
 'a':'The complete selected log enclosures, exact thresholds and integer iff proofs derive41394(two-sided) and35978(one-sided) from0.008; the printed decimal approximations are enclosed.',
 'b':'The selected radius enclosure and integer iff proof give at most45 failures/34935 successes for34980, and strictly distinguish rounded0.9987 from the exact cutoff.',
 'c':'The full selected history-dependent fresh-product-IID proof supplies each attempt conditional confidence and the genuine five-attempt union bound. Exact delta.002 and threshold53967 with30–31percent sample increase are proved.',
 'd':'The new primitive source MPC record supplies only Ass1–4, actual rows/erosion, compact X/U, continuous f, positive P/Q/R and a positive finite horizon. Terminal domains, globally attained optimizer, bootstrap successor X/locality, shifted finite feasibility and original robustOneStepCertificate are derived. Actual first-entry paths match the switched path through entry; terminal positive quadratic dissipation derives all-time X/U safety and convergence, including zero-dimensional state. The final literal IID route derives the measurable good event from the fixed implemented measurable MPC/approximation, derives its actual Bernoulli failure law from true same-law IID initial states, and combines acceptance confidence with AE feasible-law safe convergent paths. It never tests the approximation after entry and never transfers to a different initial law.'},
 {'inventory_key':'lyapunov-mpc.html::node-1387','whole_unit_approved':True,'missing_clauses':[],'correspondence':'Exactly clause(d) above: confidence is the probability of the acceptance-implies-good-event guarantee over the independent validation data. Good finite-entry/error-before-entry event has probability at least critical under the same physical initial law, and its AE feasible points have safe convergent switched paths. Approximation is not validated inside the terminal set.'}]
limits=['The currentSource60 adopted typed-domain reading is used explicitly; no claim that the original paper printed a separate successor-domain clause.','The positive finite horizon is the physical source MPC convention. State dimension zero is covered separately rather than silently imposing nontrivial state dimension.','The primary paper uses positive definite P/Q/R. The recovered thesis permits semidefinite R; this peer does not promote that more general thesis variant.','A classical global argmin is derived without a measurability claim. The statistical literal requires measurable implemented MPC/approximation, as needed to define the actual observations; measurable classical selection existence is not derived.','The literal route needs no terminal-feedback measurability because it measures the good finite-entry event and derives AE outcomes. The optional theorem measuring the complete safety/convergence event states a separate measurable-terminal-feedback hypothesis explicitly.','The two-sided bound is used for the full actual good-event composition; selected one-sided bound separately closes(a).','No whole735/737/739 Assumption boxes, general robust-positive-invariant/practical-convergence Theorem5, or other exercises are approved.','All actual0 old component peers retain their original intentional whole-pending status and original times; this is a new composition approval, not retiming or relabeling them.']
after=guard();assert before==after
f={'status':'passed_independent_full9_body_original_source_mpc_and_whole_exercise18_node1387_review','reader_started_at_utc':start,'reader_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'proof_source':r['proof_source'],'new_public_names':r['new_public_names'],'new_public_theorem_count':9,'full_new9_definitions_bodies_and_primitive_record_read':True,'full_current_exercise18_and_material1387_and_all_source60_premise_contexts_read':True,'full_selected_numerical_statistical_adaptive_trajectory_hybrid_matrix_sources_read':r['full_selected_dependencies_to_read'],'full_primary_paper_and_thesis_relevant_model_assumption_terminal_and_validation_contexts_read':r['full_primary_sources'],'complete_new_primary_measurability_and_measure_mono_proof_bodies_read':r['complete_additional_primary_APIs'],'exact_prior_full18_peer_unchanged':r['exact_prior_full18_peer'],'prior_original_body_time_preserved':r['prior_full18_original_times'],'prior_source_review_reuse_scope':'The entire exact old global4/connection/bootstrap/optimizer prefix and prior component findings are retained with their actual whole-pending status. The new full semantic read checks every new primitive field, all9 new bodies, complete current literal/primary-premise correspondence and full selected numerical/adaptive/hybrid/statistical dependencies. Integrity alone is not treated as source correspondence.','whole_decisions':whole,'component_groups':r['requested_component_groups'],'actual_all_five_failures_and_two_success_histories':trials,'scope_limits':limits,'before':before,'after':after,'errors':[],'protection_errors':[],'new_Lean_execution_by_reviewer':False,'canonical_owner_or_coverage_promotion':False,'coverage_complete':False}
(OUT/'findings-v1.json').write_text(json.dumps(f,indent=2)+'\n');print(json.dumps({'status':f['status'],'whole_decisions':[(x['inventory_key'],x['whole_unit_approved']) for x in whole],'new_bodies':9,'genuine_prior_failed_trials':5,'guards':True}))
