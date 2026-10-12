from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future32-foundations/signed-distance-Hausdorff10-full-scope-v1';assert not B.exists()
S=Path('/tmp/CompleteFoundationsSignedDistanceHausdorff32-draft-v1.lean');V=R/'book/coverage/inventory-after-correction81.json'
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
assert sha(S)=='2944bae9e6187ffd55b8660dc3c7aedc7a21232b5cbb1844032073700aa9b7af'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a' and path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes()
assert sha(V)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
inv=json.loads(V.read_bytes());key='primer-linalg.html::node-205';unit=next(r for r in inv['material_source_units'] if r['key']==key)
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if key in r.get('source_unit_keys',[])];assert len(rows)==1 and rows[0]['status']=='pending'
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
s=S.read_text();names=declarations(s);ts=[r['name'] for r in names if r['kind']=='theorem'];assert len(names)==12 and len(ts)==10 and sum(r['kind']=='def' for r in names)==2
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
hist=[]
for role,p in [('first_passed_source10','/tmp/foundations-signed-distance-Hausdorff10-installed31-trial1.json'),('all10_standard_axiom_inspection','/tmp/foundations-signed-distance-Hausdorff10-all-public-axioms-installed31-actual-v1.json')]:
 n=json.loads(path(p).read_bytes());assert n['actual_exit_code']==n['actual_runner_exit_code']==0 and n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after'] and sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'history_role':role,'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),'actual_exit_code':0,'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),'original_body_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert hist[0]['source']['sha256']==sha(S) and [h['actual_emitted_location_first_warning_headers'] for h in hist]==[2,2]
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",path('/tmp/foundations-signed-distance-Hausdorff10-all-public-axioms-installed31-actual-v1.log').read_text(),re.S)
assert [n for n,_ in ax]==ts and all(set(x.strip() for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'} for _,v in ax)
providers={n:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n) for n in ['Topology/MetricSpace/HausdorffDistance.lean','Topology/Closure.lean','Topology/MetricSpace/Bounded.lean','Topology/Compactness/Compact.lean','Topology/Order/Compact.lean','Topology/MetricSpace/Pseudo/Real.lean','Order/ConditionallyCompleteLattice/Basic.lean']}
full=path('SafeLearning/primer-linalg.html');assert sha(full)==unit['source_sha256']=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
before='A signed distance to a closed set equals';after=r'For a closed set $C$ with $C\ne\emptyset$ and $C^c\ne\emptyset$, a signed distance equals';assert full.read_text().count(before)==1
new=full.read_text().replace(before,after,1);assert new.replace(after,before,1).encode()==full.read_bytes()
P=B/'primer-linalg-signed-distance-proper-closed-domain-prospective-unnumbered32.html';P.parent.mkdir(parents=True,exist_ok=True);P.write_text(new)
prop={**unit,'source_text':unit['source_text'].replace(before,after,1),'source_sha256':sha(P)};assert prop['source_text']!=unit['source_text'];prop['text_sha256']=hashlib.sha256(prop['source_text'].encode()).hexdigest()
body=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1] if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsSignedDistanceHausdorff32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
lines=full.read_text().splitlines(keepends=True);viability=path('SafeLearning/viability.html');vl=viability.read_text().splitlines(keepends=True)
q={'status':'prepared_full_SignedDistanceHausdorff10_source_current205_component_prospective205_whole_review_request','errors':[],
 'final_genuine_passed_source':retain(S),'public_theorem_count':10,'public_name_count':12,'definition_count':2,'all_public_declarations':names,'public_theorem_names':ts,'all10_complete_body_signatures':body,
 'entire_current_literal':unit,'exact_planned_prospective_domain_qualified_literal':prop,'prospective_full_Source81_page':ref(P),'unnumbered_exact_planned_replacements':[{'before':before,'after':after}],
 'actual_installed_owner31_pending_row':rows[0],'immutable_actual_installed_owner31':retain(OWN),'current_inventory81':retain(V),'full_current_Source81_linalg':retain(full),'full_current_metric_signed_distance_Hausdorff_context_lines213_239':''.join(lines[212:239]),
 'full_current_Source81_viability_local_convention_context':retain(viability),'actual_current_viability_signed_distance_and_positive_safety_side_lines140_147':''.join(vl[139:147]),
 'full_actual_used_Mathlib_primary_source_copies':providers,'all_genuine_native_histories':hist,'actual_standard_axioms_per_public_theorem':{n:[x.strip() for x in v.replace('\n',' ').split(',')] for n,v in ax},
 'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),
 'requested_full_mathematical_scope':'Read all10 complete proofs and both actual definitions, all used primary provider bodies, the entire current205 and exact planned proper-closed-domain205 including local reachability sign convention. Decide all components and prospective entire205 independently; current205 is not approved by this author packet. No trajectory-value or neighboring literal scope is included.',
 'actual_signed_distance_domain_scope':'In an arbitrary metric space, signedDistance(C,x)=infDist(x,C)-infDist(x,C complement) is exactly distance to C outside and minus distance to its complement inside. For a nonempty closed C with nonempty complement its zero set is exactly frontier C. Outside-positive and its opposite inside-positive convention are both proved, with interior membership for positive inside values. Both nonstrict-minus-strict sign sets equal frontier C; no zero-level infinite-horizon safety identification is inferred.',
 'actual_Hausdorff_scope':'Actual Metric.hausdorffDist between nonempty compact sets is the maximum of the two real sSup images of actual infDist. Finiteness and both real supremum bounds are derived from compact boundedness and nonemptiness, not assumed. The actual object has zero iff equal, symmetry and triangle on this domain; the full real interval example is exactly1 by upper witness selection and attained endpoint distance1.',
 'explicit_real_totalization_domain_limit':'Mathlib real infDist to the empty set is0 by totalization; for C=univ the actual difference is0 everywhere although frontier is empty. This is an explicit proof-convention countermodel requiring the nonempty proper domain for a finite real-valued signed-distance construction, not a claimed counterexample to an extended-infinite-distance convention. The planned wording follows the exact nonempty closed failure set/nonempty complement convention already printed in Module7.',
 'unused_compact_C_hypothesis_warnings_preserved':'Both genuine logs emit two location-first unused variable headers for hC/hCn in the metric-properties conjunction. The printed compact domain remains explicit; no source or warnings were rewritten.',
 'current_or_prospective_whole205_approved_by_author':False,'no_Source_ordinal_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
retain(Path(__file__));q['physical_original_leaf_refs']=refs;q['required_evidence_artifacts_sha256']={r['file']:r['sha256'] for r in refs.values()}
O=B/'foundations-signed-distance-Hausdorff10-entire-source-current205-component-prospective205-whole-independent-review-request32-v1.json';O.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':ref(O),'public_theorems':10,'public_names':12,'source_codes':[h['actual_exit_code'] for h in hist],'physical_refs':len(refs)}))
