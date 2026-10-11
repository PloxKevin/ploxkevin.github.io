from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');REQ=Path('/tmp/foundations-chain-lie11-four-full-units28-v1/foundations-chain-lie11-four-full-units28-v1.json');OUT=Path('/tmp/foundations-chain-lie11-independent-applied-findings28-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ref=lambda p:{'file':str(p),'sha256':sha(p)}
assert sha(REQ)=='7e8016f981e350c3a6e1bbd5ab2ec764ec0adcfbbb3c38ac163c108853a439f2'
d=json.loads(REQ.read_bytes());closed={str(REQ):sha(REQ)}
def refs(x):
 if isinstance(x,dict):
  if type(x.get('file'))is str and type(x.get('sha256'))is str:
   p=Path(x['file']);assert p.is_file() and sha(p)==x['sha256'],str(p);closed[str(p)]=sha(p)
  for v in x.values():refs(v)
 elif isinstance(x,list):
  for v in x:refs(v)
refs(d)
src=Path(d['source']['file']);s=src.read_text();assert s==d['entire_source']
assert not any(re.search(r'\b(sorry|axiom|admit)\b',l) for l in s.splitlines() if not l.lstrip().startswith('--'))
names=[];ns=None
for l in s.splitlines():
 if l.startswith('namespace '):ns=l.split()[1]
 if l.startswith('theorem '):names.append(ns+'.'+l.split()[1])
assert names==d['public_theorem_names'] and len(names)==d['public_theorem_count']==11
for x in d['reused_selected_sources_full_bodies'] if 'reused_selected_sources_full_bodies' in d else d['reused_selected_full_source_bodies']:
 p=Path(x['source']['file']);assert p.read_text()==x['entire_source'];closed[str(p)]=sha(p)
notation=(R/'verification/lean/SafeLearning/CompleteFoundationsNotation.lean').read_text()
a=s[s.index('def coordinatePartial'):s.index('\nend SafeLearning.CompleteFoundationsLiteralChainLie28Notation')]
b=notation[notation.index('def coordinatePartial'):notation.index('\nend SafeLearning.CompleteFoundationsNotation')]
assert a==b,'entire four selected Notation bodies must be preserved exactly'
inv=json.loads((R/'book/coverage/inventory-after-correction55.json').read_bytes());owner=json.loads((R/'book/coverage/foundations.json').read_bytes());units={x['key']:x for x in inv['material_source_units']}
html=(R/'SafeLearning/primer-optimization.html').read_text();assert d['full_current_teaching_context147_to190']==''.join(html.splitlines(keepends=True)[146:190])
old=[]
for u in d['current_source55_full_literal_records']:
 assert units[u['key']]==u and sha(R/u['source'])==u['source_sha256']
 old.extend(c for c in owner['material_claims'] if u['key'] in c.get('source_unit_keys',[]))
assert old==d['entire_original_pending_claim_bodies_and_times']
trials=[]
for row,code,nwarn in zip(d['actual_trials_full_original_bodies_times_and_raw'],[1,0],[3,0]):
 p=Path(row['record']['file']);x=json.loads(p.read_bytes());assert x==row['entire_original_body_and_time']
 assert type(x['actual_exit_code'])is int and x['actual_exit_code']==code and type(x['actual_runner_exit_code'])is int and x['actual_runner_exit_code']==code
 assert x['actual_command']==['lake','env','lean',x['source']] and x['actual_workdir']==str(R/'verification/lean') and x['source_unchanged']is True and x['protection_errors']==[]
 log=Path(x['raw_log']);snapshot=Path(x['source_snapshot']);assert sha(log)==x['raw_log_sha256'] and sha(snapshot)==x['source_sha256_before']==x['source_sha256_after']==x['source_snapshot_sha256']
 assert log.read_text()==row['entire_raw_log'] and snapshot.read_text()==row['entire_source_snapshot']
 assert len(re.findall(r'^.*?:\d+:\d+: warning:',log.read_text(),re.M))==nwarn
 assert x['protected_proof_sources']==1175 and x['unchanged_current55_book_assets']==31 and x['unchanged_installed27_live_owners']==5
 if code==0:assert snapshot.read_bytes()==src.read_bytes() and log.read_bytes()==b''
 for q in [p,log,snapshot,Path(x['source'])]:closed[str(q)]=sha(q)
 trials.append({'record':ref(p),'actual_exit_code':code,'original_started_at_utc':x['started_at_utc'],'original_finished_at_utc':x['finished_at_utc'],'raw_log':ref(log),'source_snapshot':ref(snapshot),'actual_warning_diagnostics':nwarn})
primary=[R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean',R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean',R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean',R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean',R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean']
for p in primary:closed[str(p)]=sha(p)
groups=[{'id':'actual_rectangular_frechet_chain_and_jacobian_product','approved':True,'lean_declarations':[names[2],names[3],names[5]],'hypotheses':['Arbitrary finite n,m,k; g differentiable at x and f differentiable at g(x).'],'correspondence':'Actual fderiv composition and coordinate-basis expansion derive the complete J(f∘g)=Jf·Jg matrix identity. Under these differentiability premises each entry is a genuine coordinate partial, so the total fderiv definition never supplies a spurious nondifferentiable Jacobian.','missing_clauses':[]},{'id':'scalar_curve_gradient_transpose_and_dot_product','approved':True,'lean_declarations':[names[0],names[1],names[4],names[6],names[7],names[8]],'hypotheses':['Actual scalar differentiability at the curve point and HasDerivAt for each supplied real-time curve.'],'correspondence':'The Riesz gradient is identified with all actual coordinate partial derivatives. Composition derives the scalar curve derivative and Jg-transpose gradient formula; the genuine real inner-product product rule supplies both displayed dot-product terms, with exact orientation.','missing_clauses':[]},{'id':'actual_control_affine_lie_row_and_derived_trajectory_derivative','approved':True,'lean_declarations':[names[9],names[10]],'hypotheses':['C1 at the trajectory point; arbitrary finite state/input dimensions; actual HasDerivAt trajectory with drift+G(x)u, precisely the stated controlled dynamics.'],'correspondence':'driftLie is the true gradient pairing and inputLieRow is the actual transpose-matrix product. Finite coordinate sums prove the row-times-input identity; the actual h∘trajectory derivative follows from C1 and the dynamics rather than being supplied as a premise.','missing_clauses':[]}]
material=[]
for u in d['current_source55_full_literal_records']:
 material.append({'inventory_key':u['key'],'entire_inventory_record':u,'entire_original_owner_claim_rows':[c for c in old if u['key'] in c.get('source_unit_keys',[])],'whole_unit_approved':True,'missing_clauses':[],'component_group_ids':[g['id'] for g in groups if (u['key'].endswith(('192','195')) and g['id']!='actual_control_affine_lie_row_and_derived_trajectory_derivative') or (u['key'].endswith(('196','199')) and g['id']=='actual_control_affine_lie_row_and_derived_trajectory_derivative')],'lean_declarations':names,'hypotheses':['Exact printed differentiability/curve derivative/C1 controlled-dynamics scope; no existence or uniqueness of an ODE solution is inferred.']})
result={'status':'passed_independent_full_chain_lie11_source_and_four_literal_review28','errors':[],'reviewer':'Applied independent mathematical full source/literal reviewer','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'source':d['source'],'all11_complete_public_bodies_definitions_read':True,'entire_selected_notation_and_spectral_sources_read':True,'exact_four_selected_notation_bodies_preserved':True,'material_units':material,'component_groups':groups,'original_actual_lean_trials':trials,'full_context147_to190':d['full_current_teaching_context147_to190'],'primary_used_apis_read':[ref(p) for p in primary],'explicit_remaining_units':['primer-optimization.html::node-200','primer-optimization.html::node-202'],'no_other_whole_unit_or_exercise_approved':True,'canonical_or_named_compilation_or_selection_claimed':False,'current27_cutoff_changed':False,'closed_evidence_sha256':closed,'no_owner_or_source_or_canonical_proof_or_publication_mutation':True}
with OUT.open('x')as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'findings':ref(OUT),'whole_units':4,'complete_bodies':11}))
