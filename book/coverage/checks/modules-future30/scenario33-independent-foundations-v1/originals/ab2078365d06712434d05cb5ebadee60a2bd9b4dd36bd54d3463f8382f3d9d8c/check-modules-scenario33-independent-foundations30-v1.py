from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction
from math import comb
import json, hashlib, re, sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/scenario33-full-components-v1/modules-scenario33-full-source-current-literals-component-independent-review-request30-v1.json'
OUT=Path('/tmp/modules-scenario33-independent-foundations30-findings-v1.json')
EXTRA=Path('/tmp/modules-scenario33-independent-foundations30-extra-primary-v1')
assert not OUT.exists() and not EXTRA.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def path(q):
 p=Path(q['file']);return p if p.is_absolute() else ROOT/p
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q);assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
 closed[str(p)]=q['sha256'];return p
assert sha(REQUEST)=='e77d5f0c0dd1967629413dffd407cfd3caef9b28e490bd7542afe5f45b0f42ff'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 add(q);p=Path(n);p=p if p.is_absolute() else ROOT/p
 assert sha(p)==q['sha256']
source=add(d['source']);body=source.read_text()
sys.path.insert(0,str(ROOT/'book/coverage'));import lean_names
closed[str(ROOT/'book/coverage/lean_names.py')]=sha(ROOT/'book/coverage/lean_names.py')
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(body))
decls=lean_names.declarations(body);names=[r['name'] for r in decls if r['kind'] in ['theorem','lemma']];other=[r for r in decls if r['kind'] not in ['theorem','lemma']]
assert len(names)==d['public_theorem_count']==33 and names==d['public_theorem_names']
assert len(decls)==d['public_declaration_count']==39 and other==d['other_public_declarations'] and len(other)==6
assert d['genuine_native_codes']==[1,1,0] and d['genuine_warning_headers']==[0,2,0]
for row,code,warnings in zip(d['genuine_original_native_history'],[1,1,0],[0,2,0]):
 a=json.loads(add(row['actual_native']).read_bytes());raw=add(row['raw_log'])
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k]) is int and a[k]==code
 assert row['actual_exit_code']==code and a['status']==('passed_actual_tmp_lean_only' if code==0 else 'failed_actual_tmp_lean_or_protection')
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['protection_errors']==[] and a['source_unchanged'] is True
 assert sha(add(row['source']))==sha(add(row['source_snapshot']))==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==warnings==row['actual_warning_headers']
 assert row['original_actual_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 assert [a[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 for k in ['original_actual_runner','actual_source65_installed29_context']:
  q=d['original_closed_byte_aliases'][a[k]['file']];assert q['sha256']==a[k]['sha256'];add(q)
 for k in ['actual_installed29_selection','actual_frozen29_original_audit']:add(a[k])
 assert all(sha(ROOT/n)==h for n,h in a['installed29_owner_sha256'].items())
assert d['genuine_original_native_history'][-1]['source']['sha256']==sha(source)
assert not add(d['genuine_original_native_history'][-1]['raw_log']).read_bytes()
assert len(d['uncompiled_historical_sources'])==2 and all(r['compiled'] is False for r in d['uncompiled_historical_sources'])
for r in d['uncompiled_historical_sources']:add(r['source'])
inv=json.loads(add(d['current_inventory']).read_bytes());owner=json.loads(add(d['immutable_original_owner29']).read_bytes())
assert path(d['current_inventory']).read_bytes()==(ROOT/'book/coverage/inventory.json').read_bytes()
assert path(d['immutable_original_owner29']).read_bytes()==(ROOT/'book/coverage/modules.json').read_bytes()
assert d['entire_current_exercise']==next(r for r in inv['exercises'] if r['key']=='verification.html::exercise-19')
assert d['entire_original_owned_exercise_row']==next(r for r in owner['exercises'] if r['inventory_key']=='verification.html::exercise-19')
for u in d['entire_current_material_literals']:assert u==next(r for r in inv['material_source_units'] if r['key']==u['key'])
keys={u['key'] for u in d['entire_current_material_literals']}
assert d['entire_original_material_rows']==[r for r in owner['material_claims'] if any(k in keys for k in r['source_unit_keys'])]
page=add(d['entire_current_page_original_byte_alias']);assert page.read_bytes()==(ROOT/'SafeLearning/verification.html').read_bytes()
lines=page.read_text().splitlines(keepends=True)
for k in ['entire_used_scenario_section_context','entire_exercise_context']:
 c=d[k];assert c['keepends_exact_full_html']==''.join(lines[c['start_line_inclusive']-1:c['end_line_exclusive']-1])
for row in d['complete_selected_sources']:
 assert add(row['source']).read_bytes()==add(row['entire_source']).read_bytes()
for row in d['entire_physical_primary_API_sources']:add(row['entire_physical_API_source'])
extra=[]
base=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'
for p in [base/'Analysis/Complex/Exponential.lean',base/'Analysis/Complex/ExponentialBounds.lean',base/'Analysis/SpecialFunctions/Log/Deriv.lean',base/'Algebra/Order/Floor/Semiring.lean',ROOT/'verification/lean/SafeLearning/CompleteAppliedFailureCounts.lean']:
 q=EXTRA/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());extra.append({'original_historical_path':str(p),'entire_physical_source':ref(q)});add(ref(q))
author=Path('/tmp/modules-scenario33-full-components30-preparation-actual-v1.json');a=json.loads(author.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['raw_log'])==a['raw_log_sha256']
for p in [author,Path(a['raw_log']),Path(a['actual_command'][1])]:add(ref(p))
for k in ['source_ordinal_reserved','source_applied','whole_promotion_performed','canonical_pairs_executed','whole_current_exercise_requested','compiler_or_parser_started_by_preparation','coverage_complete']:assert d[k] is False
assert d['whole_current_exercise_expected_pending'] is True and len(d['exact_components_requested'])==7
# Independently recompute the literal's rational binomial/old-bound crossings.
def tail(n,k):return sum((Fraction(comb(n,i)*19**(n-i),20**n) for i in range(k)),Fraction(0))
crossings=[]
for lo,hi,k,beta in [(642,643,10,Fraction(1,10**6)),(1137,1138,36,Fraction(1,1000))]:
 x,y=tail(lo,k),tail(hi,k);assert x>beta and y<beta
 crossings.append({'n_before':lo,'n_after':hi,'support_dimension':k,'beta':str(beta),'exact_fraction_before_above':True,'exact_fraction_after_below':True,'before_fraction_sha256':hashlib.sha256(str(x).encode()).hexdigest(),'after_fraction_sha256':hashlib.sha256(str(y).encode()).hexdigest()})
oldlo=Fraction(comb(1395,10)*19**1385,20**1385);oldhi=Fraction(comb(1396,10)*19**1386,20**1386)
assert oldlo>Fraction(1,10**6) and oldhi<Fraction(1,10**6)
specs=[
 (0,7,'Actual binomial tail least sizes','The independent-event count mass is genuinely derived from event independence and pattern cardinalities in selected BinomialModel/FailureCounts, then finite disjoint unions identify lowerTail. The source derives successor antitonicity on its support domain, controls every smaller n by the zeroth mass, and proves all-natural-n iff minima643/1138 from exact rational adjacent crossings. No scenario design violation law or fully-supported tightness is assumed or concluded by this component.'),
 (7,12,'Old support-union expression on n>=10','The exact expression choose(n,10)*(19/20)^(n-10) crosses at1395/1396. The actual binomial choose recurrence proves successor nonincrease for n>=199; for10<=n<=199 choose>=1 and the genuine power bound exclude earlier success. The all-n iff minimum1396 is restricted to n>=10. Values below10 are not scenario-design bounds.'),
 (12,16,'Genuine logarithm ceilings and rounded displays','The full selected rigorous log20 exponential enclosure and actual log2 remainder bound yield a strict log10 enclosure; powers derive log1000/log1000000. Actual Nat.ceil characterizations prove953/1717. Absolute error bounds and strict non-equalities certify the printed decimal displays as approximate. Current exact equality signs remain an explicit whole-literal gap.'),
 (16,19,'Chernoff parameter domain and exponent algebra','For d>=0 and mu>0, t=1-d/mu is in[0,1] iff d<=mu. The exponent identity is algebraic on mu!=0, with nonnegative slack only on positive mu. Positive epsilon, beta in(0,1] and positive N*epsilon put the explicit rule in the admissible domain. This component does not prove a new multiplicative Chernoff probability bound.'),
 (19,21,'Parameter count and sample comparison','The displayed count2*4^2+4=36 is exact arithmetic. Genuine strict integer ordering643<953<1396 and1138<1717 and the explicit≈50-percent overhead follow. The actual paper LMI variable semantics are not silently derived from this arithmetic.'),
 (21,30,'Scalar adaptive common-gain infeasibility on genuine open sets','B>0 converts actual |A+BK|<1 into the printed open gain interval. Nonempty open sets A>1,B>0 and A<-1,B>0 force opposite K signs and exclude a common gain. Positive scalar P Lyapunov inequalities are equivalent to scalar stability and provide the exact common certificate infeasibility. Full support is explicitly IsOpenPosMeasure; product-law openness/positive mass and monotonicity give positive mass to the infeasible-pair event. This is a scalar independent-pair result, with no matrix-valued posterior identification or matrix-pair/LMI association inferred.'),
 (30,33,'Fixed-gain and unbounded-input distinction','Actual A=0,K=0 stabilizes every B, so unbounded B support alone is insufficient. For every fixed K, continuity gives a nonempty open unstable region, witnessed by(2-K,1), and stated full support gives positive mass. This fixed-gain fact is kept distinct from adaptive common-gain infeasibility.')]
groups=[{'scope':label,'public_theorem_names':names[lo:hi],'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':reason} for lo,hi,label,reason in specs]
assert [n for g in groups for n in g['public_theorem_names']]==names
finding={'status':'passed_independent_scenario33_full_source_current_literal_components_semantic_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'source':ref(source),'public_theorem_count':33,'public_declaration_count':39,'public_theorem_names':names,'other_public_declarations':other,'all33_entire_bodies_and_all6_definitions_read':True,'all_six_complete_selected_sources_and_used_primary_proof_chains_read':True,'complete_current_exercise_five_literals_and_contexts_read':True,'component_decisions':groups,'independent_exact_rational_crossing_observations':crossings,'independent_old1395_1396_rational_crossing_verified':True,'complete_selected_sources':d['complete_selected_sources'],'primary_physical_sources':d['entire_physical_primary_API_sources'],'additional_used_primary_physical_sources':extra,'genuine_original_native_history':d['genuine_original_native_history'],'genuine_native_codes':[1,1,0],'genuine_warning_header_counts':[0,2,0],'uncompiled_historical_sources':d['uncompiled_historical_sources'],'original_author_preparation_actual':ref(author),'all_original_sources_snapshots_logs_failures_and_native_body_times_preserved':True,'whole_current_Exercise19_or_any_material_literal_approved':False,'whole_remaining_associations':d['explicit_remaining_whole_associations'],'paper_full_factual_attribution_or_general_scenario_design_theorem_approved':False,'scalar_to_matrix_pair_or_posterior_or_actual_matrix_LMI_bridge_approved':False,'semantic_decisions_from_full_math_read_not_integrity':True,'compiler_or_parser_launched_by_reviewer':False,'canonical_or_source_or_owner_or_publication_mutation':False,'source_ordinal_reserved':False,'source_applied':False,'coverage_complete':False,'prospective_postfreeze_evidence_not_part_of_frozen29':True,'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':d['original_closed_byte_aliases'],'errors':[]}
OUT.write_text(json.dumps(finding,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'components':33,'groups':7,'whole_decision':False,'errors':[]}))
