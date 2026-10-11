"""Independent literal/parser/semantic evidence closure; no Lean or source mutation."""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import hashlib,importlib.util,json,sys,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased')
packet=Path('/tmp/mpc-assumption1-domain-clarification28-v1/mpc-assumption1-domain-clarification28-v1.json')
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(packet)=='9c3300f80180548c5c18c1b4e1dad48ebe30f91d09eae79abe0d3100adbc8baa'
d=json.loads(packet.read_bytes())
def checkref(r):
 p=Path(r['file']);assert digest(p)==r['sha256'];return p
for r in d['original_closed_byte_aliases'].values():checkref(r)
for k in ['before_inventory','source','parser','proposed_source','proposed_full29_inventory','original_full_domain_gap_audit','proposed_component_source']:checkref(d[k])
gap=json.loads(checkref(d['original_full_domain_gap_audit']).read_bytes());assert gap==d['entire_original_full_domain_gap_audit_body_and_time']
for r in gap['original_closed_byte_aliases'].values():checkref(r)
for k in ['primary_paper','primary_thesis','primary_thesis_text','original_gap_review','original13_component_peer']:checkref(gap[k])
assert json.loads(checkref(gap['original_gap_review']).read_bytes())==gap['complete_original_gap_review_body_and_time']
assert json.loads(checkref(gap['original13_component_peer']).read_bytes())==gap['entire_original13_peer_body_and_time']
before=checkref(d['source']).read_bytes();after=checkref(d['proposed_source']).read_bytes()
constructed=before.decode()
for row in d['raw_replacements']:
 assert constructed.count(row['before'])==1;constructed=constructed.replace(row['before'],row['after'],1)
assert constructed.encode()==after
inverse=after.decode()
for row in reversed(d['raw_replacements']):
 assert inverse.count(row['after'])==1;inverse=inverse.replace(row['after'],row['before'],1)
assert inverse.encode()==before
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'book'))
spec=importlib.util.spec_from_file_location('independent_foundations_inventory28',checkref(d['parser']));parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
old=parser.inventory();stored=json.loads(checkref(d['before_inventory']).read_bytes())
for k in ['source_sha256','counts','exercises','material_source_units']:assert old[k]==stored[k]
simulation=Path(tempfile.mkdtemp(prefix='mpc-domain28-independent-full29-'))
(simulation/'SafeLearning').mkdir()
for path in sorted((ROOT/'SafeLearning').glob('*.html')):
 target=simulation/'SafeLearning'/path.name
 if path.name=='lyapunov-mpc.html':target.write_bytes(after)
 else:target.symlink_to(path)
parser.ROOT=simulation;new=parser.inventory();proposed=json.loads(checkref(d['proposed_full29_inventory']).read_bytes())
for k in ['source_sha256','counts','exercises','material_source_units']:assert new[k]==proposed[k]
diff={}
for kind in ['exercises','material_source_units']:
 a={r['key']:r for r in old[kind]};b={r['key']:r for r in new[kind]};assert a.keys()==b.keys()
 changed=[k for k in a if a[k]['source_text']!=b[k]['source_text']]
 diff[kind]=changed
 assert changed==d['actual_fresh_parser_changed_text_keys'][kind]
 for k in a:
  if k not in changed:assert {x:v for x,v in a[k].items() if x!='source_sha256'}=={x:v for x,v in b[k].items() if x!='source_sha256'}
assert diff=={'exercises':[],'material_source_units':['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739']}
for k,record in d['entire_changed_records'].items():
 assert record['entire_original_inventory_record']==next(r for r in old['material_source_units'] if r['key']==k)
 # Accept the packet's explicit naming, then require the full proposed row.
 candidates=[v for name,v in record.items() if 'proposed' in name and isinstance(v,dict)]
 assert len(candidates)==1 and candidates[0]==next(r for r in new['material_source_units'] if r['key']==k)
assert next(r for r in old['exercises'] if r['key']=='lyapunov-mpc.html::exercise-18')==d['entire_current_exercise18_record']
assert checkref(d['proposed_component_source']).read_text()==d['entire_uncompiled_component_source']
assert d['whole_exercise18_approved'] is False and d['whole_material_units_approved'] is False and d['compiler_or_kernel_execution_claimed'] is False

# Exact counterexample to deriving successor membership from the weaker total
# ambient V interpretation. Uniform contraction is an identity for this model.
x=Fraction(9,10);z=Fraction(4,5);v=Fraction(3,5);rho=Fraction(1,4);delta=Fraction(1,10)
f=lambda state,input:state/2+input
xp=f(x,v);zp=f(z,v);V=lambda a,b:(a-b)**2
assert -1<=x<=1 and -1<=z<=1 and -1<=v<=1 and -1<=zp<=1 and xp>1
assert V(x,z)<=delta and V(xp,zp)==rho*V(x,z)
counterexample={'model':'X=U=[-1,1]; f(x,u)=x/2+u; tracking(x,z,v)=v; total ambient V(x,z,v)=(x-z)^2; cL=cU=kmax=1; rho=1/4; delta=1/10','uniform_scalar_contraction_identity':'f(x,v)-f(z,v)=(x-z)/2, so V(next)=V(old)/4 for every ambient pair and every next reference input; feedback deviation is zero.','old_state':str(x),'old_nominal':str(z),'reference_input':str(v),'nominal_successor':str(zp),'tracking_successor':str(xp),'old_value':str(V(x,z)),'next_value':str(V(xp,zp)),'nominal_successor_in_X':True,'tracking_successor_in_X':False,'scope':'Shows the total ambient interpretation is weaker. It is not a counterexample to the explicitly typed partial-domain assumption or to the complete MPC theorem.'}
report={'status':'passed_independent_full_primary_literal_parser_and_scoped_typed_domain_interpretation_review','approved_source_clarification_as_explicit_typed_reading':True,'errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/foundations_recovery28','packet':{'file':str(packet),'sha256':digest(packet)},'full_current_and_proposed_source_context_read':True,'full_primary_assumption_and_recursive_proof_context_read':True,'full_proposed6838byte_draft_read':True,'preserved_original_gap_and_component_review_bodies_and_times_checked':True,'fresh_full29_parser_counts':new['counts'],'actual_changed_text_keys':diff,'exact_two_raw_replacements_and_inverse_passed':True,'interpretation_decision':{'wellformed_partial_domain_reading':'On the displayed V_delta:X×X×U domain, the universally asserted contraction term at (x+,z+,v+) is meaningful only with x+ in X. Coupling that witness with contraction preserves the old local hypotheses and nominal-successor/reference-input domain quantifiers. The added witness supplies a one-step domain clause, not shifted-plan existence, tightened rows, attained optimization or online recursive feasibility.','primary_attribution_limit':'Neither paper nor thesis prints a separate x+ in X line. Approval is of an explicitly adopted typed interpretation, not a verbatim primary clause, uniquely established author intent, or a derivation from a total ambient V extension. The proposal explicitly says the contraction clause is understood to include the witness.','total_ambient_reading_requires_extra_hypothesis':True,'feedback_continuity_assumed':False,'recommended_optional_wording':'Here we use the typed reading of the stated domain: the contraction clause includes x+ in X, so that its left-hand side is defined.','source_reference':'https://arxiv.org/abs/1806.04167'},'weaker_total_ambient_counterexample':counterexample,'complete_draft_scope':{'structure':'TypedLocalIncrementalCertificate encodes the local successor-domain witness explicitly with contraction. Lower and feedback clauses are assumptions extracted for the listed components. It omits several full Assumption1 clauses and is not a whole-unit encoding.','generated_induction':'The generated dynamics remain in X by induction from the local one-step witness; geometric locality uses rho in [0,1), nonnegative B and B<=delta. The old nominal and next-reference domain hypotheses are explicit.','constraint_components':'The Euclidean radius, continuous linear row margin and terminal-offset lemmas are valid mathematical conditional components on their written premises. Their exact source epsilon/sqrt-rho/matrix-norm and old-terminal instantiation remains unproved and uncompiled.','missing_whole_construction':d['remaining_actual_proof_obligations']},'original_gap_audit':d['original_full_domain_gap_audit'],'whole_exercise18_approved':False,'whole_material_units_approved':False,'compiler_or_kernel_execution_claimed':False,'current27_cutoff_changed':False,'independent_parser_simulation':str(simulation),'scope':'Read-only independent primary/literal/parser/semantic review of this proposal. Authoritative domain interpretation is stated explicitly; total ambient scalar contraction never silently implies state membership. No Lean execution, source correction, current55/27 owner/selection/progress/coverage promotion/Git/publication mutation.'}
out=Path('/tmp/mpc-assumption1-domain-clarification28-independent-foundations-review-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'review':str(out),'sha256':digest(out),'changed_text_keys':diff,'full29_parser_counts':new['counts']}))
