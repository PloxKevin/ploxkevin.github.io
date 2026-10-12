from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
TMP=Path('/tmp/applied30b-shelf-composition-v1')
OUT=ROOT/'book/coverage/checks/future30-core/shelf83-whole-composition-independent-applied30b-v1'
REQUEST='book/coverage/checks/modules-future30/shelf-continuous-control-association-v1/modules-shelf-continuous-control-full-association-and-prospective-whole-composition-review-request30-v1.json'
REQUEST_SHA='ac9b1a36854e48ae8e59bb7948daa306ac35175314f00ecb1fb447eba60a8d75'
OLD='book/coverage/checks/future30-core/shelf57-independent-applied30b-v1/modules-shelf57-all-components-current1122-1131-prospective1126-independent-applied30b-with-association-gap-closed-peer-v1.json'
OLD_SHA='0871675302e18aa30f180ee6b751644b36d20ba66205205459227bf9e1a44342'
NEW='book/coverage/checks/modules-future30/shelf-continuous26-independent-foundations-v1/modules-shelf-continuous26-full-source-actual-control-association-independent-foundations30-closed-peer-v1.json'
NEW_SHA='909e7f385530cda92c7f86b940b5d8ced9d5b57b130f136676a01da1399e9b5a'
NARROW='book/coverage/checks/future30-core/shelf-rounding-independent-foundations-v1/modules-shelf-rounding-unnumbered-narrow-full-literal-parser-independent-foundations30-closed-peer-v1.json'
NARROW_SHA='f6b08448e34b08aaabde74602eaacafe8e9db36e28549fccf5533a62d1fc2fed'
CTX=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CTX_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
physical={};aliases={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def path(p):return Path(p) if Path(p).is_absolute() else ROOT/p
def close(p,h=None):
 p=path(p);assert p.is_file() and not p.is_symlink()
 b=p.read_bytes();actual=hashlib.sha256(b).hexdigest();assert h is None or h==actual,str(p)
 if p.resolve().is_relative_to(ROOT):q=p.resolve()
 else:
  q=OUT/'exact-original-by-sha256'/actual/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==b
  else:
   with q.open('xb') as f:f.write(b)
 n=q.relative_to(ROOT).as_posix();physical[n]=actual;r={'file':n,'sha256':actual,'bytes':len(b)};aliases[str(p)]=r;return r
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str) and isinstance(x.get('sha256'),str):
   r=close(x['file'],x['sha256']);assert 'bytes' not in x or r['bytes']==x['bytes']
  for k,v in x.items():
   if k in ('required_evidence_artifacts_sha256','all_physical_original_copies_sha256'):
    for p,h in v.items():close(p,h)
   else:walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
def guard():
 assert sha(CTX)==CTX_SHA;c=json.loads(CTX.read_bytes())
 for n,h in {**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}.items():
  p=ROOT/n;assert not p.is_symlink() and p.resolve().is_relative_to(ROOT) and sha(p)==h,n
 return {'protection_errors':[],'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5}
before=guard();OUT.mkdir(exist_ok=False)
objects=[]
for name,h in [(REQUEST,REQUEST_SHA),(OLD,OLD_SHA),(NEW,NEW_SHA),(NARROW,NARROW_SHA)]:
 assert sha(ROOT/name)==h
 obj=json.loads((ROOT/name).read_bytes());walk(obj);objects.append(obj);close(name,h)
j,old,new,narrow=objects
assert old['errors']==new['errors']==narrow['errors']==[]
assert old['all57_entire_public_proofs_five_definitions_two_private_proofs_read'] is True
assert new['all26_entire_bodies_12_other_declarations_and_model_fields_read'] is True
assert new['public_theorem_count']==26 and new['public_declaration_count']==38
assert new['whole_current1130_or_current_or_prospective_exercise7_3_decision_made_by_this_component_review'] is False
assert new['no_desired_return_value_optimality_or_attainment_premise'] is True
assert new['generic_unsafe_controller_optimality_or_discontinuous_ODE_uniqueness_approved'] is False
assert [t['actual_exit_code'] for t in j['genuine_original_native_history']]==[1,1,0]
for t in j['genuine_original_native_history']:
 n=json.loads(path(t['actual_native']['file']).read_bytes())
 assert n['actual_exit_code']==n['actual_runner_exit_code']==t['actual_exit_code'] and n['protection_errors']==[]
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==t['source']['sha256']==t['source_snapshot']['sha256']
 assert n['raw_log_sha256']==t['raw_log']['sha256']
 assert all(n[k]==v for k,v in t['original_actual_times'].items())
 assert n['actual_command']==['lake','env','lean',n['source']]
 assert len(re.findall(r'^.*:[0-9]+:[0-9]+: warning:',path(t['raw_log']['file']).read_text(),re.M))==t['actual_warning_headers']
source=path(j['source']['file']).read_text()
assert len(re.findall(r'^\s*theorem ',source,re.M))==26
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|ofReduceBool|sorryAx)\b',source)
assert 'x t = x0 + ∫ s in (0:ℝ)..t, u s' in source
assert 'IsGreatest (safeReturns L v tau x0) (safeValueFormula L v tau x0)' in source
assert 'sInf (safeOptimalValue 1 (1/5) tau' in source
assert 'actual_safe_control_integral_is_printed_dynamics' in source and 'actual_right_control_is_stationary_feedback' in source
ctx_ref=j['entire_current_and_prospective_context'];ctx=json.loads(path(ctx_ref['file']).read_bytes())
inventory=json.loads(path(j['current_inventory']['file']).read_bytes())
materials={u['key']:u for u in inventory['material_source_units']}
exercises={u['key']:u for u in inventory['exercises']}
current_ex=ctx['entire_current_exercise_inventory_row'];prospective_ex=ctx['entire_prospective_corrected_exercise_inventory_row']
assert exercises[current_ex['key']]==current_ex
for u in ctx['four_entire_current_material_inventory_rows']:assert materials[u['key']]==u
node=next(u for u in ctx['four_entire_current_material_inventory_rows'] if u['key']=='viability.html::node-1130')
assert hashlib.sha256(node['source_text'].encode()).hexdigest()==node['text_sha256']
assert sha(ROOT/'SafeLearning/viability.html')==node['source_sha256']==current_ex['source_sha256']
assert hashlib.sha256(prospective_ex['source_text'].encode()).hexdigest()==prospective_ex['text_sha256']
assert prospective_ex['source_sha256']=='ea88b9787aa437c78b6ebe5e839d33fc44e56053e2d9991f42f104345889f7e0'
current_old={d['inventory_key']:d for d in old['individual_current_decisions']}
prospective_old={d['inventory_key']:d for d in old['individual_prospective_decisions']}
assert current_old['viability.html::node-1130']['current_whole_literal_approved'] is False
assert current_old['viability.html::exercise-17']['current_whole_literal_approved'] is False
assert current_old['viability.html::node-1126']['current_whole_literal_approved'] is False
assert current_old['viability.html::node-1122']['current_whole_literal_approved'] is True
assert current_old['viability.html::node-1131']['current_whole_literal_approved'] is True
assert prospective_old['viability.html::node-1126']['prospective_whole_literal_approved'] is True
assert prospective_old['viability.html::node-1126']['conditional_on_actual_later_source_application'] is True
assert all(d['approved_in_exact_scope'] is True and d['missing_clauses']==[] for d in new['component_decisions'])
names=[n for c in old['component_approvals'] for n in c['names']]+new['public_theorem_names']
assert len(names)==len(set(names))==83
used=close(TMP/'used-continuous-primary-full-body-read-v1.txt')
after=guard()
association='The whole literal uses the intended safe integral/event-driven shelf trajectories already stated in its model context. For positive v and tau and 0<=x0<=L, the actual local-integral motion and admissible effective speeds give x(t)<=x0+vt, hence no safe path reaches the wall before (L-x0)/v. The genuine weighted -1/0 reward is integrable on positive infinite time. Its return is at most the exact right-driving return. The constructed clipped right motion min(x0+vt,L) is safe, absorbs at the wall and is generated by the stated stationary right feedback. Actual IsGreatest/sSup is derived, and actual IsLeast/sInf over safe states is attained at the ledge. The default L=1,v=1/5 infimum equals -tau*(1-exp(-5/tau)), exactly the earlier constrainedLedgeValue definition, so the previously approved derivative/monotonicity/limit facts now apply to this actual constrained quantity. No value, upper bound or optimizer is supplied as a control admissibility premise. Effective velocity is zero at the absorbing wall; choosing the zero command there preserves the state and reward. The bound permits locally interval-integrable time-dependent safe controls and contains the constructed stationary optimizer. The integral/event convention is explicit; the discontinuous bare ODE is not used to infer uniqueness or a converse solution theorem.'
composition=old['full_component_correspondence']+' '+association+' The exercise gives the threshold scalar formula as its calculation input; no full generic unsafe-controller optimum, tight-penalty theorem or neighboring analytic family follows. The paper attribution is the exact preserved VI-A/Fig2 original already read. The eight exact approximation edits change only the rounded coefficient/subtraction notation and ratio qualifier; all actual numeric enclosures, global shape, shifted scaling and asymptotic clauses match the corrected entire exercise.'
rounding_gap=current_old['viability.html::node-1126']['remaining_gaps']
decisions=[{'inventory_key':node['key'],'entire_current_literal':node,'current_whole_literal_approved':True,'remaining_gaps':[],'exact_support':names,'correspondence':composition},
 {'inventory_key':current_ex['key'],'entire_current_literal':current_ex,'current_whole_literal_approved':False,'remaining_gaps':rounding_gap,'controller_value_association_gap_now_closed':True,'exact_support':names,'correspondence':composition},
 {'inventory_key':prospective_ex['key'],'entire_prospective_literal':prospective_ex,'prospective_whole_literal_approved_if_exact_narrow_correction_applied':True,'remaining_gaps':[],'exact_support':names,'correspondence':composition}]
review={'status':'passed_full_shelf83_current1130_and_prospective_corrected_Exercise7_3_composition_independent_applied30b','errors':[],
 'reviewer':'/root/applied_review30b','request':close(REQUEST,REQUEST_SHA),
 'original_shelf57_whole_gap_peer':close(OLD,OLD_SHA),'new_continuous26_independent_mathematical_component_peer':close(NEW,NEW_SHA),'independent_eight_phrase_narrow_peer':close(NARROW,NARROW_SHA),
 'full_old57_proof_bodies_and_literal_context_previously_read_and_reused_without_change':True,
 'all_new26_entire_theorem_bodies_12_other_declarations_and_control_fields_read':True,
 'all_requested_current_and_prospective_literal_clauses_and_model_analytic_context_read':True,
 'used_continuous_primary_full_statement_and_proof_bodies_read':used,
 'actual_controller_value_association':association,'full_whole_composition_correspondence':composition,
 'individual_current_and_prospective_decisions':decisions,
 'entire_original_pending_exercise_owner_row':ctx['entire_original_pending_exercise_owner_row'],
 'entire_five_old_owner_rows_preserved':ctx['five_entire_affected_old_owner_material_rows_including_the_prior_proved_component'],
 'entire_current_and_prospective_context':close(ctx_ref['file'],ctx_ref['sha256']),
 'original57_verdict_body_and_original_reader_time_unchanged':True,
 'original57_fourteen_actual_native_histories_preserved_verbatim_in_original_peer':old['genuine_original_fourteen_native_histories_unchanged'],
 'new26_three_actual_native_histories_preserved_verbatim':new['genuine_original_native_history'],
 'new26_native_codes':[1,1,0],'new26_warning_headers':[2,0,0],
 'actual_83_public_theorem_support_names':names,'actual_model_scope':j['actual_model_scope'],
 'no_desired_value_or_control_optimality_premise':True,'generic_unsafe_ODE_optimum_or_uniqueness_or_converse_promoted':False,
 'before_guard':before,'after_guard':after,'producer_or_compiler_invoked_by_reviewer':False,
 'source_ordinal_reserved':False,'source_applied':False,'whole_promotion_performed':False,
 'canonical_source_owner_or_publication_mutated':False,'coverage_complete':False,
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':physical,
 'scope':'New whole review of current1130 and the exact prospective eight-phrase corrected entire Exercise7.3 only. Current full Exercise7.3/node1126 remain pending their original false rounded equalities; original57 gap verdict and times remain historical. No source application or neighboring family promotion.'}
with (TMP/'shelf83-whole-composition-semantic-base-v1.json').open('x') as f:json.dump(review,f,indent=2);f.write('\n')
print(json.dumps({'status':review['status'],'current_whole_units':1,'prospective_whole_exercises':1,'current_whole_exercise_still_pending':True,'all83_public_support_bodies':83,'protection_errors':[]}))
