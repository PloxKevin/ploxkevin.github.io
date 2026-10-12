from pathlib import Path
from fractions import Fraction as F
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased')
Q=Path('/tmp/foundations-logcube13-full-current1306-review31-v1/foundations-logcube13-full-source-entire-current1306-whole-independent-review-request31-v1.json')
B=Path('/tmp/foundations-logcube13-independent-modules31-v2')
assert not B.exists();B.mkdir()
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(r):
 p=Path(r['file']);return p if p.is_absolute() else R/p
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(Q)=='5236f366f4df90e708b0a6abd9ed440cec85f2fefcb8953b3fec3f0fa6c90c60'
q=json.loads(Q.read_bytes());checked={}
for p,h in q['all_physical_original_inputs_sha256'].items():assert sha(p)==h,p;checked[p]=h
for old,r in q['all_original_byte_aliases'].items():assert sha(path(r))==r['sha256']
for k in ['current_source','current_inventory','current_installed30_foundations_owner','final_actual_passed_source','entire_complete_selected_dependency']:
 assert sha(path(q[k]))==q[k]['sha256']
t=path(q['final_actual_passed_source']).read_text();decl=lean_names.declarations(t)
qualified_names=[d['name']for d in decl if d['kind']in ['theorem','lemma']]
names=[n.removeprefix('SafeLearning.CompleteFoundationsLogCubeCrossover31.')for n in qualified_names]
assert names==q['public_theorem_names']and len(names)==q['public_theorem_count']==13
assert set(q['full13_exact_literal_correspondence'].values())==set(names)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(t))
source=path(q['current_source']).read_text();inv=json.loads(path(q['current_inventory']).read_bytes())
unit={u['key']:u for u in inv['material_source_units']}['primer-basics.html::node-1306']
assert unit==q['entire_current_literal']
assert hashlib.sha256(unit['source_text'].encode()).hexdigest()==unit['text_sha256']
assert q['full_context_lines1338_1388']==''.join(source.splitlines(keepends=True)[1337:1388])
owner=json.loads(path(q['current_installed30_foundations_owner']).read_bytes());rows={r['id']:r for r in owner['material_claims']}
assert len(q['entire_current_pending_rows'])==1
for row in q['entire_current_pending_rows']:assert row==rows[row['id']]and row['status']=='pending'and row['lean_declarations']==[]
hist=[]
for i,h in enumerate(q['genuine_original_compiler_histories']):
 n=json.loads(path(h['native']).read_bytes());raw=path(h['raw_log']).read_bytes()
 assert n['actual_exit_code']==n['actual_runner_exit_code']==h['actual_exit_code']==[1,1,1,1,0,0][i]
 assert n['protection_errors']==[]and n['source_unchanged']
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
 for key,nkey in [('source','source_sha256_before'),('snapshot','source_snapshot_sha256'),('raw_log','raw_log_sha256')]:
  assert sha(path(h[key]))==h[key]['sha256']==n[nkey]
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']
 assert [n[k]for k in ['protected_selected30_proof_sources','unchanged_current79_final_css_book_assets','unchanged_current_source79_raw_owner30_files']]==[1242,31,5]
 assert len(re.findall(rb'^.*?:\d+:\d+: warning:',raw,re.M))==h['emitted_diagnostic_warning_headers']==0
 for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert h[k]==n[k]
 hist.append(h)
assert t.encode().startswith(path(hist[-2]['source']).read_bytes())
assert path(hist[-1]['raw_log']).read_bytes()==b''
assert hist[-1]['source']['sha256']==q['final_actual_passed_source']['sha256']
prep=Path('/tmp/foundations-logcube13-full-current1306-review31-preparation-actual-v1.json');pn=json.loads(prep.read_bytes())
assert pn['actual_exit_code']==0 and pn['protection_errors']==[]
for p,h in pn['helper_sha256_before'].items():assert sha(p)==h==pn['helper_sha256_after'][p]
assert sha(pn['log'])==pn['log_sha256']
exact={'endpoint4_cube_above_sqrt':F(1386,1000)**3>2,'endpoint24M_lower_cube_above_4899':F(169935,10000)**3>4899,'sqrt24M_below4899':24000000<4899**2,'endpoint24_5M_upper_cube_below4949':F(17035,1000)**3<4949,'sqrt24_5M_above4949':4949**2<24500000,'unique_bracket_rounds_to_two_significant_24M':24500000<25000000}
assert all(exact.values())
primary=q['complete_used_primary_files']
for r in primary.values():assert sha(path(r))==r['sha256']
# This actual quotient derivative provider is additional to the submitted Mul file.
extra=R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean'
assert 'theorem HasDerivAt.div' in extra.read_text()
decision={'inventory_key':unit['key'],'entire_current_literal':unit,'entire_original_owner_rows':q['entire_current_pending_rows'],'current_whole_literal_approved':True,'remaining_gaps':[],'all13_exact_support':q['full13_exact_literal_correspondence'],'correspondence':'Both generic little-o statements are derived from the complete selected RatesCosts proofs and actual logarithm/power asymptotics. An actual quotient derivative supplies increasing and decreasing branches; exact certified logarithm bounds and rational endpoint inequalities prove every real budget from4 to24million has log-cube above square-root. A genuine IVT and strict decrease prove the unique upper crossover strictly between24 and24.5million, consistent with about2.4e7. Strict decrease excludes any later recrossing. Arbitrary finite-point modification preserves little-o and gives any prescribed finite-budget value, closing the final pedagogical clause without asserting anything about an algorithm.'}
d={'status':'passed_independent_logcube13_full_source_entire_current1306_whole_literal_review','errors':[],'reviewer':'/root/modules_finish28','request':ref(Q),'source':q['final_actual_passed_source'],'all13_entire_public_bodies_ratio_definition_and_entire_selected_RatesCosts_source_read':True,'individual_decisions':[decision],'full_context':q['full_context_lines1338_1388'],'domain_assessment':{'budget_domain':'Real budgets, not only natural integers; all logarithm/square-root derivative uses have actual t>0 from t>=4.','approximate_crossover':'The true upper crossover is unique and strictly between24M and24.5M; the printed about2.4e7 is justified. It is not asserted equal to24M.','finite_budget_limitation':'Little-o is preserved under arbitrary modification at a prescribed finite point; no finite-time algorithm guarantee follows.','source_correction_required':False},'exact_independent_Fraction_endpoint_checks':exact,'complete_selected_source':q['entire_complete_selected_dependency'],'complete_submitted_primary_files':primary,'additional_actual_quotient_rule_provider':ref(extra),'used_primary_full_proof_bodies_read':['IsLittleO quantifier definition, eventual equality invariance and quotient-limit equivalence','Log-rpow little-o through actual logarithm growth, rpow composition and eventual positive denominator','Square-root identity with real rpow and negative-power limit','Log derivative, square-root derivative, power derivative and genuine quotient derivative','Mean-value derivation of monotone/antitone/strict antitone on convex intervals','Full logarithm-series remainder and actual log2/log3/log5 certified rational bounds','Actual real square-root order and square identities','Full interval IVT via preconnected continuous images'],'genuine_original_compiler_histories':hist,'actual13_exact_entire_passed12_byte_prefix_verified':True,'actual_author_preparation':ref(prep),'author_preparation_exact_helpers':[ref(p)for p in pn['helper_sha256_before']],'author_preparation_exact_raw_log':ref(pn['log']),'author_preparation_wrapper':ref('/tmp/run-foundations-logcube13-full-current1306-review31-preparation-v1.py'),'original_checked_closure':checked,'current_owner_row_preserved_without_status_or_time_mutation':True,'node1308_cost_algorithm_or_neighbor_promotion':False,'source_applied':False,'compiler_or_owner_or_source_or_canonical_or_publication_mutation':False,'coverage_complete':False}
O=B/'foundations-logcube13-full-current1306-independent-modules31-peer-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':ref(O),'whole':unit['key'],'missing':[]}))
