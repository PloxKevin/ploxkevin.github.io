from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,copy
R=Path('/home/oxrexkevin/SafetyBased');Q=Path('/tmp/foundations-innerproduct14-three-full-literals-review28-v1.json');O=Path('/tmp/foundations-innerproduct14-independent-modules28-peer-original-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists() and sha(Q)=='cd4b3a1136b175cef13f3b9dcb51e92e68ca83123ee7a79d1e46c71422fd678c'
start=datetime.now(timezone.utc).isoformat();q=json.loads(Q.read_bytes())
def checkref(v):
 p=Path(v['file']);assert sha(p)==v['sha256'] and p.stat().st_size==v['bytes'];return p
source=checkref(q['proof_source']);s=source.read_text();assert s==q['entire_proof_source']
names=['SafeLearning.CompleteFoundationsLiteralInnerProduct28.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
assert names==q['public_theorem_names'] and len(names)==q['public_theorem_count']==14
assert s.count('private def sourceCore')==1 and all(t in s for t in ['[AddCommGroup F] [Module ℝ F]','(hpos : ∀ x, x≠0 → 0<b x x)','have hn (v : F) : ‖v‖=Real.sqrt (b v v) := rfl','have hi (u v : F) : ⟪u,v⟫=b u v := rfl'])
inv=json.loads((R/'book/coverage/inventory-after-correction60.json').read_bytes());units={u['key']:u for u in inv['material_source_units']}
owner=json.loads((R/'book/coverage/foundations.json').read_bytes())
assert q['whole_scope_requested']==[f'primer-linalg.html::node-{n}'for n in [126,128,136]]
for u in q['entire_literal_units']:assert u==units[u['key']]
for c in q['entire_original_pending_rows']:assert c in owner['material_claims'] and c['status']=='pending'
html=R/'SafeLearning/primer-linalg.html';a,b=q['full_literal_context']['lines'];assert '\n'.join(html.read_text().splitlines()[a-1:b])==q['full_literal_context']['text']
refs=[Q,source,checkref(q['actual_guard_context']),checkref(q['original_runner'])]
for v in q['complete_selected_dependencies_and_primary_sources']:
 p=checkref(v);refs.append(p);assert p.read_text()
trials=[]
for i,row in enumerate(q['actual_native_trials_and_failures']):
 p=checkref(row['actual']);d=json.loads(p.read_bytes());snap=checkref(row['source_snapshot']);log=checkref(row['raw_log']);refs.extend([p,snap,log])
 assert d['actual_exit_code']==row['actual_exit_code']==[1,1,0][i]
 assert d['actual_runner_exit_code']==row['actual_runner_exit_code']==[1,1,0][i]
 assert d['protection_errors']==[] and d['source_sha256_before']==d['source_sha256_after']==sha(snap)
 assert d['raw_log_sha256']==sha(log) and log.read_text().count('warning:')==row['actual_warning_count']==[7,13,13][i]
 for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert d[k]==row[k]
 assert d['actual_command']==['lake','env','lean',d['source']] and d['actual_workdir']==str(R/'verification/lean')
 trials.append({'actual':row['actual'],'source_snapshot':row['source_snapshot'],'raw_log':row['raw_log'],'original_full_native_body_and_time_preserved':True,'actual_warning_count':row['actual_warning_count']})
assert q['actual_native_trials_and_failures'][-1]['source_snapshot']['sha256']==q['proof_source']['sha256']
def scopecheck(x):
 assert x['whole_scope_requested']==q['whole_scope_requested'] and x['entire_literal_units']==q['entire_literal_units']
 assert x['public_theorem_names']==names and x['public_theorem_count']==14
 assert x['entire_proof_source']==s and x['whole_approval_claimed_before_independent_reader'] is False
 assert x['live_source_owner_proof_install_or_coverage_promotion'] is False
scopecheck(q);tests=[]
def reject(label,change):
 x=copy.deepcopy(q);change(x)
 try:scopecheck(x)
 except AssertionError:tests.append(label);return
 raise AssertionError('fixture accepted:'+label)
reject('dropped weighted literal',lambda x:x['entire_literal_units'].pop())
reject('expanded surrounding theorem scope',lambda x:x['whole_scope_requested'].append('primer-linalg.html::node-134'))
reject('changed full proof',lambda x:x.__setitem__('entire_proof_source',s+'\n'))
reject('invented mapped declaration',lambda x:x['public_theorem_names'].append('fake'))
reject('claimed author whole before peer',lambda x:x.__setitem__('whole_approval_claimed_before_independent_reader',True))
reject('installed coverage during peer',lambda x:x.__setitem__('live_source_owner_proof_install_or_coverage_promotion',True))
decisions=[]
for n in [126,128]:
 decisions.append({'source_unit_key':f'primer-linalg.html::node-{n}','entire_literal_approved':True,'missing_clauses':[],'full_clause_reason':'The actual real pairing has symmetry, both additivities and scalar linearities, strict self-positivity and sqrt length. EuclideanSpace pairing is explicitly the source finite dot sum; its l2 length is the sqrt sum of squares. A real symmetric positive-definite matrix supplies all five weighted bilinear identities, strict positivity, sqrt length and zero iff. Positive diagonal entries supply actual positive definiteness and exact weighted sum. The exact source definition and examples are covered without asserting that the ordinary Pi sup norm is the Euclidean norm.'})
decisions.append({'source_unit_key':'primer-linalg.html::node-136','entire_literal_approved':True,'missing_clauses':[],'full_clause_reason':'The selected quadratic expansion is read in full. New completed-square and attained-minimum bodies prove every real t bound and nonnegativity at the printed t-star; they derive CS by clearing the positive squared norm rather than assuming CS. Equality gives zero squared norm of x-t-star*y and the printed scalar. The zero-y clause gives both sides zero. The last three bodies construct a genuine local InnerProductSpace.Core from only symmetry, left additivity/scalar linearity and strict positivity on an arbitrary real module, explicitly identify inner=b and norm=sqrt(b self), and derive the same argument. Symmetry derives right linearity. This applies to weighted or function spaces satisfying those axioms without assuming completeness or a desired inequality. It does not promote the separate surrounding iff-parallel theorem or actual integral definitions outside this unit.'})
primaryscope={'InnerProductSpace/Defs.lean':'entire file, including Core norm construction and ofCore; no desired-CS premise in sourceCore','InnerProductSpace/Basic.lean':'full used symmetry/linearity/self positivity/sqrt norm and norm-sub-square proof bodies','InnerProductSpace/PiL2.lean':'actual finite PiLp innerProductSpace construction and inner_apply','Analysis/Matrix/PosDef.lean':'entire file and weighted Core construction','LinearAlgebra/Matrix/PosDef.lean':'actual PosDef/PSD definitions, positive diagonal proof, finite iff/dotProduct positivity full bodies','Data/Matrix/Mul.lean':'actual matrix-vector and dot-product definitions, diagonal action, transpose/bilinear identities full bodies'}
extra=[R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean',R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean']
refs.extend(extra)
out={'status':'passed_independent_full_innerproduct14_three_literal_semantic_review','errors':[],'reviewer':'/root/modules_finish28','request':{'file':str(Q),'sha256':sha(Q)},'proof_source':q['proof_source'],'reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'individual_full_literal_decisions':decisions,'entire_14_public_bodies_and_private_Core_defs_read':True,'entire_selected_Geometry_and_NormDuality_sources_read':True,'used_primary_definition_and_full_proof_body_scope':primaryscope,'actual_three_native_trials_and_original_failures_preserved':trials,'warning_scope':'Final genuine Lean pass retains exactly13 style/unused-section/reducibility warnings; no empty-log or zero-warning claim. They do not change the proven propositions.','meaningful_scope_negative_fixtures':tests,'full_current_inventory_and_owner_rows_match':True,'new_compiler_or_live_source_owner_selection_canonical_or_publication_change':False,'coverage_complete':False,'original_read_byte_refs':[{'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size} for p in dict.fromkeys(refs)]}
O.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':str(O),'sha256':sha(O),'three_whole_decisions':len(decisions),'negative_fixtures':len(tests)}))
