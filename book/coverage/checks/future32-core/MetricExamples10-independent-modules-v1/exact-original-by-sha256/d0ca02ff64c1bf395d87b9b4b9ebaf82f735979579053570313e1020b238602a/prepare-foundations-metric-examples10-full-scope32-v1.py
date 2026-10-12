from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future32-foundations/metric-examples10-full-scope-v1';assert not B.exists()
S=Path('/tmp/CompleteFoundationsMetricExamplesAndCertifiedBalls32-draft-v3.lean');V=R/'book/coverage/inventory-after-correction81.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def retain(n):
 p=path(n);r=ref(p)
 if p.is_relative_to(R) and '.lake' not in p.parts and not str(p.relative_to(R)).startswith('SafeLearning/'):
  refs[str(p)]=r;return r
 t=B/'exact-original-by-sha256'/r['sha256']/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:t.write_bytes(p.read_bytes())
 a=ref(t);refs[str(p)]=a;return a
assert sha(S)=='997c6c8e1fcdb534637db0b2e09e5ca91a7c02f67f371573aa7e354da1b0ff90'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a' and path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes()
assert sha(V)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
inv=json.loads(V.read_bytes());key='primer-linalg.html::node-202';unit=next(r for r in inv['material_source_units'] if r['key']==key)
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if key in r.get('source_unit_keys',[])];assert len(rows)==1 and rows[0]['status']=='pending'
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
s=S.read_text();names=declarations(s);ts=[r['name'] for r in names if r['kind']=='theorem'];assert len(names)==11 and len(ts)==10 and sum(r['kind']=='def' for r in names)==1
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
hist=[]
for role,p in [('first_failed_source9','/tmp/foundations-metric-examples-certified-balls9-installed31-trial1.json'),('passed_source10','/tmp/foundations-metric-examples-certified-balls10-installed31-trial2.json'),('all10_standard_axiom_inspection','/tmp/foundations-metric-examples-certified-balls10-all-public-axioms-installed31-actual-v1.json')]:
 n=json.loads(path(p).read_bytes());assert n['actual_exit_code']==n['actual_runner_exit_code'] and n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after'] and sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'history_role':role,'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),'original_body_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [h['actual_exit_code'] for h in hist]==[1,0,0] and hist[1]['source']['sha256']==sha(S) and [h['actual_emitted_location_first_warning_headers'] for h in hist]==[0,1,1]
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",path('/tmp/foundations-metric-examples-certified-balls10-all-public-axioms-installed31-actual-v1.log').read_text(),re.S)
assert [n for n,_ in ax]==ts and all(set(x.strip() for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'} for _,v in ax)
providers={n:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n) for n in ['Topology/MetricSpace/HausdorffDistance.lean','Analysis/Normed/Lp/PiLp.lean','Analysis/InnerProductSpace/PiL2.lean','Analysis/Normed/Group/Basic.lean','Analysis/Normed/Group/Constructions.lean','Analysis/Normed/Module/Basic.lean','Topology/MetricSpace/Lipschitz.lean','Topology/MetricSpace/Pseudo/Defs.lean','Topology/MetricSpace/Defs.lean','Combinatorics/SimpleGraph/Metric.lean','Combinatorics/SimpleGraph/Hasse.lean','Combinatorics/SimpleGraph/Prod.lean','Combinatorics/SimpleGraph/Connectivity/Connected.lean']}
selected={n:retain('verification/lean/SafeLearning/'+n) for n in ['CompleteFoundationsGeometry.lean','CompleteFoundationsMetricAndSetDistance26.lean']}
full=path('SafeLearning/primer-linalg.html');assert sha(full)==unit['source_sha256']=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
first=path('/tmp/CompleteFoundationsMetricExamplesAndCertifiedBalls32-draft-v1.lean').read_text();headers=lambda text:[m.group(0).split(':=',1)[0] for m in re.finditer(r'(?ms)^theorem .*?:=',text)]
assert headers(s)[:9]==headers(first)
body=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1] if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsMetricExamplesAndCertifiedBalls32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
lines=full.read_text().splitlines(keepends=True)
q={'status':'prepared_full_MetricExamples10_source_entire_current202_independent_mathematical_review_request','errors':[],
 'final_genuine_passed_source':retain(S),'public_theorem_count':10,'public_name_count':11,'definition_count':1,'all_public_declarations':names,'public_theorem_names':ts,'all10_complete_body_signatures':body,
 'entire_current_literal':unit,'actual_installed_owner31_pending_row':rows[0],'immutable_actual_installed_owner31':retain(OWN),'current_inventory81':retain(V),'full_current_Source81_linalg':retain(full),'full_current_metric_examples_and_signed_distance_context_lines194_239':''.join(lines[193:239]),
 'entire_two_selected_metric_and_positive_L_certificate_sources':selected,'old_selected_positive_L_ball_body_unchanged':True,
 'full_actual_used_Mathlib_primary_source_copies':providers,'all_genuine_native_histories':hist,'actual_standard_axioms_per_public_theorem':{n:[x.strip() for x in v.replace('\n',' ').split(',')] for n,v in ax},
 'uncompiled_offline_draft2_retained_without_native_claim':retain('/tmp/CompleteFoundationsMetricExamplesAndCertifiedBalls32-draft-v2.lean'),'original_first9_statement_headers_retained_exactly_after_repairs':True,
 'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),
 'requested_full_mathematical_scope':'Read all10 complete proofs/one exact rectangular-grid definition, both complete selected sources and actual used primary chains, entire current202 with full domain/context. Decide each exact component and the entire unit independently, retaining any actual dimension/grid/domain qualifier gap found. No author whole approval, source edit, neighboring unit or imported old scope widening is asserted.',
 'actual_all_input_halfspace_scope':'For every finite Euclidean coordinate index i and every input x, actual infDist to {y:y_i<=0} equals max(x_i,0). The actual coordinate-single projection attains the upper bound; every point in the halfspace provides the lower bound through the genuine coordinate norm inequality. Existence of i is explicit and hence this clause has a nonempty coordinate domain.',
 'actual_all_input_unit_disc_scope':'In every real normed vector space, actual infDist to the closed unit ball equals max(norm x-1,0) at every input, including zero-dimensional and infinite-dimensional spaces. The outside case constructs the radial unit point, proves its norm and exact distance; the inside case uses actual membership, and the norm triangle inequality proves the universal lower bound. The planar unit-disc clause is a specialization, not a single numerical fixture.',
 'actual_infinity_box_scope':'On every nonempty finite real coordinate type, norm(x-x0)<=epsilon iff all coordinate absolute deviations<=epsilon, for every real epsilon. The negative-radius branch is included and uses the explicitly nonempty coordinate domain. No empty-dimensional all-coordinate convention is silently inferred.',
 'actual_grid_scope':'The exact rectangular grid on Fin(r+1)timesFin(c+1) is the Cartesian box product of two genuine pathGraph graphs. Its adjacency is proved exactly horizontal or vertical unit steps, and connectivity is derived from actual path-graph connectivity. Actual library shortest-walk length is shown nonnegative, zero iff same vertex, symmetric and triangle; a finite walk attains it and is no longer than every competitor. An additional arbitrary connected-graph theorem proves the same metric/attainment, including infinite connected grid models with supplied structural connectivity. No disconnected or arbitrarily masked grid is claimed to carry a finite metric.',
 'actual_certified_ball_scope':'The genuine LipschitzWith L lower margin g(z)-L*dist(y,z)<=g(y) is derived. The whole union of all positive-center balls of radius g(z)/L is certified for L>0 by the unchanged actual selected positive-L certificate. If L=0, the actual Lipschitz inequality derives g(y)=g(z) for every domain point; a positive center certifies the whole domain, without any division.',
 'original_genuine_trial1_error_scope':'Only implicit halfspace-set choice/membership reduction, Pi norm rewriting, explicit shortest-walk bound API and missing NNReal notation scope prevented elaboration. The final first9 theorem headers remain byte-exact; new10 is the separately appended connected-graph bridge. No desired distance, bound or connectivity conclusion is assumed.',
 'one_unused_DecidableEq_section_warning_preserved':True,'current_whole202_approved_by_author':False,'no_Source_ordinal_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
retain(Path(__file__));q['physical_original_leaf_refs']=refs;q['required_evidence_artifacts_sha256']={r['file']:r['sha256'] for r in refs.values()}
O=B/'foundations-metric-examples10-entire-source-all-input-distances-grid-and-certified-balls-current202-independent-review-request32-v1.json';O.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':ref(O),'public_theorems':10,'public_names':11,'source_codes':[h['actual_exit_code'] for h in hist],'physical_refs':len(refs)}))
