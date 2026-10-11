#!/usr/bin/env python3
"""Read-only byte/literal/evidence checker for a completed independent full-source read."""
from pathlib import Path
import datetime,hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/applied-double-integrator-wall53-full-source-review-request27-v2.json')
REQUEST_SHA='dea2da70b4a801d40c95dfa7875dc8d76b12664290202df058654fe9759f8374'
OUT=Path('/tmp/wall53-full-source-independent-foundations-check-result27-v1.json')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):
 p=Path(n); return p if p.is_absolute() else ROOT/p
def check(ref):
 p=path(ref['file']); assert p.is_file() and sha(p)==ref['sha256'],ref
 return p
def ref(p): return {'file':str(p),'sha256':sha(p)}
def strictzero(d):
 keys=[k for k in ('actual_exit_code','exit_code') if k in d]
 assert keys and all(type(d[k]) is int and d[k]==0 for k in keys)
assert not OUT.exists()
assert sha(REQUEST)==REQUEST_SHA
q=json.loads(REQUEST.read_text())
src=check(q['proof_source']); text=src.read_text(); assert text==q['entire_source']
names=re.findall(r'^theorem\s+(\w+)',text,re.M)
ns='SafeLearning.CompleteAppliedDoubleIntegratorWall27.'
assert len(names)==53 and [ns+n for n in names]==q['public_theorem_names']
assert q['public_theorem_count']==53
assert not re.search(r'\bsorry\b|\badmit\b|^axiom\s',text,re.M)
act=json.loads(check(q['actual_standalone']).read_text());strictzero(act)
assert act==q['entire_original_actual_standalone_record_and_time']
assert act['actual_command']==['lake','env','lean',str(src)]
assert act['actual_workdir']==str(ROOT/'verification/lean')
assert act['source_sha256_before']==act['source_sha256_after']==sha(src)
assert sha(path(act['source_snapshot']))==sha(src)
assert sha(path(act['raw_log']))==act['raw_log_sha256']
assert act['protection_errors']==[]
assert len(q['actual_warning_lines'])==58
raw=path(act['raw_log']).read_text()
assert all(w in raw for w in q['actual_warning_lines'])
# Exact old owner aliases are selected by the actual copy-only Root installation,
# rather than treating the changed current raw owner files as the original bytes.
integration_path=ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json'
execution_path=ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-execution-v1.json'
integration=json.loads(integration_path.read_text()); execution=json.loads(execution_path.read_text())
strictzero(execution)
assert execution['actual_command']==['python3','book/coverage/checks/root_integrate_owner27_candidates_v2.py','book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json','--apply']
assert execution['actual_workdir']==str(ROOT)
assert integration['applied'] is True and integration['coverage_complete'] is False
assert len(integration['exact_replacements'])==5
rows={v['destination']:v for v in integration['exact_replacements']}
aliases={}; checked={}
for n,digest in q['closed_evidence_sha256'].items():
 p=path(n)
 if n in rows:
  row=rows[n]; assert row['before_sha256']==digest
  alias=ROOT/row['original26_byte_copy']
  assert alias.is_file() and sha(alias)==digest
  aliases[n]={'file':str(alias.relative_to(ROOT)),'sha256':digest}
  checked[str(alias.relative_to(ROOT))]=digest
 else:
  assert p.is_file() and sha(p)==digest,n
  checked[n]=digest
assert len(aliases)==5
checked[str(integration_path.relative_to(ROOT))]=sha(integration_path)
checked[str(execution_path.relative_to(ROOT))]=sha(execution_path)
# Entire current physical records and the original pending rows are checked directly.
inv=json.loads(check(q['current_inventory']).read_text())
unis={u['key']:u for u in inv['material_source_units']}; exs={u['key']:u for u in inv['exercises']}
old=json.loads((ROOT/aliases['book/coverage/modules.json']['file']).read_text())
for u in q['material_units']:
 assert unis[u['source_unit_key']]==u['entire_inventory_record']
 original=[v for v in old['material_claims'] if u['source_unit_key'] in v.get('source_unit_keys',[])]
 assert original==u['entire_original_current26_rows']
 assert set(u['proposed_lean_declarations']) <= set(q['public_theorem_names'])
for e in q['exercise_records']:
 assert exs[e['key']]==e['entire_inventory_record']
 assert next(v for v in old['exercises'] if v['inventory_key']==e['key'])==e['entire_original_current26_exercise_record']
for c in q['full_current_page_contexts']:
 p=ROOT/c['source']; assert sha(p)==c['source_sha256']
 assert ''.join(p.read_text().splitlines(keepends=True)[c['first_line']-1:c['last_line']]).rstrip('\n')==c['entire_text'].rstrip('\n')
sel=json.loads((ROOT/'reports/full-coverage/checkpoint-26-selection.json').read_text())
for d in q['full_selected_dependency_sources_and_original_rows']:
 p=check(d['source']); assert p.read_text()==d['entire_source']
 assert sel['proof_files'][str(p.relative_to(ROOT))]==d['entire_selected_proof_row']
 for n,h in d['entire_selected_proof_row']['evidence_sha256'].items(): assert sha(ROOT/n)==h
primary=check(q['primary_source']['text']);check(q['primary_source']['pdf'])
for c in q['complete_primary_assumption_theorem_appendix_contexts']:
 assert ''.join(primary.read_text().splitlines(keepends=True)[c['first_line']-1:c['last_line']]).rstrip('\n')==c['entire_text'].rstrip('\n')
for n,t in q['original_trial_history'].items():
 d=json.loads(check(t).read_text());assert d==t['entire_original_record_and_time']
 assert sha(path(d['raw_log']))==d['raw_log_sha256']
 assert sha(path(d['source_snapshot']))==d['source_snapshot_sha256']
assert len(q['original_trial_history'])==12
original_gap=json.loads(check(q['original_gap_peer']).read_text())
assert original_gap==q['entire_original_gap_peer_body_and_time']
# These are the reviewer’s completed semantic decisions, not a compiler inference.
reasons={
 '1095':'The exact a>0 closed-wall double-integrator question is covered by the actual measurable bounded-control/locally absolutely-continuous ODE model, both attained kernel branches and exact complement, all-controller finite/root/uniform/nonuniform horizons, true measurable held-input volumes and both distinct boundary limits. The later source sentence specifies that the velocity bound concerns initial states; a separate hard velocity constraint requires extra boundary semantics.',
 '1099':'FTC derives the velocity and position lower bounds for every actual admissible control. The strict-clearance braking-until-rest/zero continuation and the nonpositive-velocity zero-input path attain both safe branches. The exact iff and complement exports give the printed unions; touching the closed wall is failure, including equality at the stopping parabola.',
 '1101':'The smaller root is proved as the attained first wall hit of maximal braking, with equality of the root bound precisely at the boundary. The all-controller comparison plus continuity/IVT gives actual wall touch by this deadline. The initial-velocity bound gives v_max/a; a concrete unbounded-velocity sequence has exact first hits tending to infinity, while every individual unviable state has finite all-controller failure. Theorem2 is read as a sufficient theorem whose uniform-horizon hypothesis fails, so it supplies no finite threshold by that theorem. The phrase about reward duration means an unbounded available pre-failure time interval, witnessed by those first hits, and does not claim an unbounded discounted reward return or universal nonexistence of a reward-specific finite exact penalty. AppendixB’s pendulum/bee statements are checked source attributions, with their model/empirical caveats intact.',
 '1103':'The actual boundary sequence v_n=a*(n+1), x_n=L-v_n^2/(2a) has attained first wall hits t_n=n+1 tending to infinity. This proves absence of a common bound without relying merely on a supremum of upper bounds. The exact initial-velocity versus independently specified hard-state-constraint qualification is preserved.',
 '1104':'The continuous stopping barrier yields the actual kernel closure and the printed two-piece frontier. The measurable held-action set is exactly prefix safety plus successor membership; every accepted hold has a constant -a or0 continuation on all later half-open sampling intervals. At fixed positive v the strict O(epsilon) input restriction, attained full braking and volume squeeze give the zero-measure/selector-to-full-braking limit. At wall/rest the actual positive-input iff is the printed quadratic inequality, and the nonpositive interval gives volume limit a. The a=1,Delta=1/2,v=-3/10 example and sufficiently far-rest case attain all inputs and volume2a. The graded-margin explanation is scoped to these actual alternatives, rather than an arbitrary global boundary limit.',
 '1109':'The genuine held polynomial state differentiates the stopping point to v(t)*(1+u/a). With t0=min(Delta,v/(2a))>0 the true velocity lower bound gives v(t)>=v/2, and strict actual safe continuation yields u+a<2a*epsilon/(v*t0). This is precisely the displayed necessary O(epsilon) inequality, with fixed a,v,Delta and positive epsilon.'
}
units=[]
for u in q['material_units']:
 num=u['source_unit_key'].rsplit('-',1)[1]
 units.append({'source_unit_key':u['source_unit_key'],'entire_inventory_record':u['entire_inventory_record'],'entire_original_current26_rows':u['entire_original_current26_rows'],'whole_source_unit_approved':True,'status':'independently_approved_full_literal_under_explicit_model_and_context_scope','lean_declarations':u['proposed_lean_declarations'],'hypotheses':q['qualification_limits'],'per_unit_reason':reasons[num],'missing_clauses':[]})
starts=list(re.finditer(r'^theorem\s+(\w+)',text,re.M));bodies=[]
for i,m in enumerate(starts):
 bodies.append({'lean_declaration':ns+m.group(1),'full_theorem_and_following_definitions_until_next_public_theorem':text[m.start():starts[i+1].start() if i+1<len(starts) else len(text)]})
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
result={'status':'passed_independent_full_wall53_source_and_six_literal_semantic_review','errors':[],'reviewed_at_utc':now,'reviewer':'/root/config21_next','request':ref(REQUEST),'proof_source':q['proof_source'],'actual_standalone':q['actual_standalone'],'entire_original_actual_standalone_record_and_time':act,'public_theorem_count':53,'public_theorem_names':q['public_theorem_names'],'all_full_public_bodies_and_private_definitions_read':True,'full_source':text,'full_body_records':bodies,'actual_warning_lines':q['actual_warning_lines'],'original_trial_history':q['original_trial_history'],'material_units':units,'exercise_records':[{'key':e['key'],'entire_inventory_record':e['entire_inventory_record'],'entire_original_current26_exercise_record':e['entire_original_current26_exercise_record'],'whole_exercise_approved':True,'reviewed_claim_ids':[c['id'] for c in e['entire_original_current26_exercise_record']['claims']],'lean_declarations':q['public_theorem_names'],'hypotheses':q['qualification_limits'],'per_exercise_reason':reasons['1095'],'missing_clauses':[]} for e in q['exercise_records']],'full_current_page_contexts':q['full_current_page_contexts'],'full_selected_dependency_sources_and_original_rows':q['full_selected_dependency_sources_and_original_rows'],'primary_source':q['primary_source'],'complete_primary_assumption_theorem_appendix_contexts':q['complete_primary_assumption_theorem_appendix_contexts'],'entire_original_gap_peer_body_and_time':original_gap,'original_gap_peer':q['original_gap_peer'],'source_scope_limits':q['qualification_limits'],'direct_historical_owner_byte_aliases':aliases,'historical_alias_authorization':{'integration_result':ref(integration_path),'actual_execution':ref(execution_path),'original_rows_and_times_reinterpreted':False},'closed_evidence_sha256':checked,'new_lean_compiler_or_canonical_execution_claimed':False,'fixed_checkpoint27_cutoff_amendment':False,'live_owner_source_or_selection_mutation':False,'scope':'Fresh TMP-only independent full semantic/literal review; six exact units and whole Exercise15 approved only under the explicit actual model and directly read explanatory/source-attribution scope. No reward-specific impossibility theorem, separate hard-velocity model, new primary bee/pendulum dynamics, current aggregate or deployment is inferred.'}
OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':'passed','errors':[],'public_bodies':53,'whole_material_units':6,'whole_exercises':1,'original_trials':12,'warnings':58,'historical_owner_aliases':5,'closed_evidence':len(checked),'result':ref(OUT)}))
