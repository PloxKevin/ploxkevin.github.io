"""Actual read-only full source/evidence checker; no Lean or source mutation."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def file(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def check(r):assert H(file(r['file']))==r['sha256'];return file(r['file'])
def ref(n):return {'file':str(n),'sha256':H(file(n))}
REQUEST='/tmp/applied-cvar-fractional-selector26-eight-body-component-review-request-v1.json'
assert H(REQUEST)=='9f8f307b3d241cf20732b404a5c63aabb9711646dc0d23d883499eba0f55441a'
x=json.loads(Path(REQUEST).read_text());source=check(x['proof_source']);body=source.read_text();assert body==x['complete_source_body']
original=check(x['preserved_original_quantile_source']);assert body.startswith(original.read_text())and original.read_text()==x['preserved_entire_original_quantile_body']
assert len(re.findall(r'^theorem ',body,re.M))==len(x['public_theorems'])==8
assert not re.search(r'\b(sorry|admit|axiom)\b',body)
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-24-selection.json').read_text())
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-24-manifest.json').read_text())
assert len(selection['proof_files'])==1144
history=[]
for row in x['all_original_actual_trials_and_raw_history']:
 actual=json.loads(check(row['record']).read_text());assert actual==row['entire_original_actual_record']
 assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==row['actual_exit_code']
 assert actual['actual_command']==['lake','env','lean',actual['source']]
 assert actual['actual_workdir']==str(ROOT/'verification/lean')
 log=check(row['raw_log']);snapshot=check(row['source_snapshot'])
 assert H(log)==actual['raw_log_sha256']and H(snapshot)==actual['source_snapshot_sha256']==actual['source_sha256_before']==actual['source_sha256_after']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_diagnostic_warning_count']
 check(actual['original_actual_runner']);history.append(row)
last=x['actual_standalone_evidence'];actual=json.loads(check(last['record']).read_text())
assert actual==last['entire_original_actual_record']and type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0
assert H(source)==actual['source_sha256_after']=='afd0f7b7a8cad0197cfd9096f6612b73ceb463e7da47aa7d1d00a77eb80a7677'
check(last['raw_log']);check(last['source_snapshot']);check(x['original_actual_runner'])
for d in x['selected_dependency_full_bodies_and_actual_evidence']:
 p=check(d['proof_source']);assert p.read_text()==d['complete_source_body'];row=d['entire_selected24_proof_and_actual_evidence_row'];assert row==selection['proof_files'][d['proof_source']['file']]
 for n,h in row['evidence_sha256'].items():assert H(ROOT/n)==h
for d in x['primary_local_mathlib_sources']:check(d)
inv=json.loads(check(x['current_inventory']).read_text());assert H(ROOT/'book/coverage/inventory.json')==x['current_inventory']['sha256']
units=[]
for unit in x['material_units']:
 row=unit['entire_inventory_record'];assert row==next(r for r in inv['material_source_units']if r['key']==unit['source_unit_key'])
 context=unit['full_source_context'];p=check(context);assert '\n'.join(p.read_text().splitlines()[context['first_line']-1:context['last_line']])==context['complete_lines']
 units.append(unit)
for n,r in selection['proof_files'].items():assert H(ROOT/n)==r['sha256']==H(ROOT/'reports/full-coverage/checkpoint-24'/n)
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
for n,h in assets.items():assert H(ROOT/n)==h
reasons=[
 'The actual CDF upper set is nonempty and bounded below by the interior level and the true endpoint limits. Its infimum is attained using right continuity; the monotone left limit brackets alpha. Neither continuity of the law nor absence of atoms is assumed.',
 'The measurable pushed-forward real loss law is a genuine probability. Its strict tail is 1-CDF(q), its atom is CDF(q)-CDF(q-), so the attained quantile brackets the required tail mass. This derives the two probabilities from the actual law.',
 'The explicit fraction numerator/boundary lies in [0,1] and matches missing mass. If boundary=0 both inequalities force numerator=0, so Lean real division0=0 is harmless and total mass still matches.',
 'The nested measurable strict-threshold/equality indicator construction is bounded pointwise and takes1 above,0 below. Every arbitrary atom fraction is allowed within[0,1].',
 'Strict-tail and equality events are disjoint. Their finite-probability integrable indicator decomposition derives the actual Bochner mass integral, without assuming it as a selector property.',
 'The prior threshold and fraction results construct a genuine measurable admissible selector of mass1-alpha for every measurable real loss. No atomless condition, continuity assumption or existing mass-matched selector appears in the hypotheses.',
 'The complete selected FractionalTailDual body proves all selectors are integrable and bounded by every actual RU threshold, with equality at this constructed selector. Thus this selector is a genuine greatest tail value and the attained threshold is the global least RU objective. The result derives the sSup identity rather than assuming it.',
 'Specializing alpha=19/20 and mass1/20 yields the literal factor20. The attained least RU value gives both directions of the strict <10 equivalence for every measurable integrable episode law, including atomic laws. No empirical sample mean is substituted.'
]
groups=[]
for g,reason in zip(x['component_groups'],reasons):
 groups.append(dict(g,decision='approved_complete_formal_component',missing_clauses=[],hypotheses=x['explicit_hypotheses'],per_component_reason=reason))
report={'status':'independent_eight_full_body_arbitrary_law_fractional_selector_CVaR_component_review_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent','request':ref(REQUEST),'proof_source':x['proof_source'],'complete_source_body':body,'public_theorems':x['public_theorems'],'components':groups,'material_units_whole_scope_retained':units,'whole_material_unit_approved':False,'scope_limits':['No quantile-integral formula or inverse-transform sampling theorem is inferred.','Neither endpoint alpha->0 expectation nor alpha->1 essential-supremum limit is proved by these eight declarations; whole156/1351 remain pending.','The combined source includes exactly the original quantile theorem namespace, so selecting a duplicate standalone quantile module exporting the same name requires a distinct deliberate selection plan.','TMP genuine standalone-only; no canonical installation, named build, kernel aggregate26 or current25 offer amendment.'],'preserved_original_quantile_source':x['preserved_original_quantile_source'],'preserved_entire_original_quantile_body':original.read_text(),'original_quantile_source_is_exact_byte_prefix':True,'selected_dependency_full_bodies_and_actual_evidence':x['selected_dependency_full_bodies_and_actual_evidence'],'all_original_actual_trials_and_raw_history':history,'actual_standalone_evidence':last,'primary_local_mathlib_sources':x['primary_local_mathlib_sources'],'primary_semantic_reads':['Probability/CDF: true CDF endpoint limits, monotonicity, halfline probability, equality of its Stieltjes measure with original probability.','Measure/Stieltjes: genuine right continuity and iInf over right-neighborhood, singleton atom equals CDF minus its left limit.','All selected FractionalTailDual/CVaRQuotients/HingeExpectations full bodies and actual selected24 evidence.'],'all1144_current_and_frozen_selected24_sources_exact':True,'all31_current52_assets_exact':True,'live_owner_scope':'The original request truthfully pins held24 owners at its actual trial time. Root authorized live integration25 may change those owners now; this fresh proof review instead preserves old frozen24 sources/evidence and unchanged current52 literal identity. It makes no fresh held24 live-owner claim.','coverage_complete':False}
OUT=Path('/tmp/applied-cvar-fractional-selector26-independent-foundations-observations-v1.json');assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'observation':ref(OUT),'public_bodies':8,'components':len(groups),'original_trials':len(history)}))
