from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future32-foundations/cube-radius-netmargin9-full-scope-v1';assert not B.exists()
S=Path('/tmp/CompleteFoundationsCubeRadiusAndNetMargin32-draft-v3.lean');V=R/'book/coverage/inventory-after-correction81.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def retain(n):
 p=path(n);r=ref(p)
 if p.is_relative_to(R) and '.lake' not in p.parts and str(p.relative_to(R)) not in ['SafeLearning/primer-linalg.html','SafeLearning/primer-basics.html','SafeLearning/primer-optimization.html']:refs[str(p)]=r;return r
 t=B/'exact-original-by-sha256'/r['sha256']/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:t.write_bytes(p.read_bytes())
 a=ref(t);refs[str(p)]=a;return a
assert sha(S)=='e52fb2820e744fe329ce21e895083ab04aafb58d5460b0be11208a543b09921e'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a' and path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes()
inv=json.loads(V.read_bytes());key='primer-linalg.html::node-191';unit=next(r for r in inv['material_source_units'] if r['key']==key)
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if key in r.get('source_unit_keys',[])];assert len(rows)==1 and rows[0]['status']=='pending'
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
s=S.read_text();names=declarations(s);ts=[r['name'] for r in names if r['kind']=='theorem'];assert len(names)==10 and len(ts)==9 and sum(r['kind']=='def' for r in names)==1
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
old5=Path('/tmp/CompleteFoundationsCubeRadiusAndNetMargin32-draft-v2.lean');assert S.read_bytes().startswith(old5.read_bytes())
hist=[]
for role,p in [('first_source5_trial1','/tmp/foundations-cube-radius-netmargin5-installed31-trial1.json'),('passed_source5_trial2','/tmp/foundations-cube-radius-netmargin5-installed31-trial2.json'),('passed_source9_trial3','/tmp/foundations-cube-radius-netmargin9-installed31-trial3.json'),('all9_standard_axiom_inspection','/tmp/foundations-cube-radius-netmargin9-all-public-axioms-installed31-actual-v1.json')]:
 n=json.loads(path(p).read_bytes());assert n['actual_exit_code']==n['actual_runner_exit_code'] and n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after'] and sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'history_role':role,'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),'original_body_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [h['actual_exit_code'] for h in hist]==[1,0,0,0] and hist[2]['source']['sha256']==sha(S) and all(h['actual_emitted_location_first_warning_headers']==0 for h in hist)
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",path('/tmp/foundations-cube-radius-netmargin9-all-public-axioms-installed31-actual-v1.log').read_text(),re.S)
assert [n for n,_ in ax]==ts and all(set(x.strip() for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'} for _,v in ax)
selected={n:retain('verification/lean/SafeLearning/'+n) for n in ['CompleteFoundationsNormDuality.lean','CompleteFoundationsGeometry.lean','CompleteFoundationsCenteredCubeNetsWhole30.lean','CompleteFoundationsQuadraticTwentyNet24.lean']}
oldpeer=retain('book/coverage/checks/future30-core/foundations-centered-cube-nets14-independent-modules-v1/foundations-centered-cube-nets14-full-source-two-component-independent-modules30-closed-peer-v2.json')
assert oldpeer['sha256']=='66c25534faca6754728b3585eb54597980c8a6c34ce19dce308301291bc6ef96'
providers={n:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n) for n in ['Analysis/Normed/Group/Constructions.lean','Analysis/Normed/Lp/PiLp.lean','Analysis/InnerProductSpace/PiL2.lean','Analysis/Real/Sqrt.lean','Topology/MetricSpace/Isometry.lean','Topology/UnitInterval.lean','Order/Interval/Set/ProjIcc.lean','Topology/Order/ProjIcc.lean','Data/Finset/Image.lean','Data/Nat/Find.lean']}
full=path('SafeLearning/primer-linalg.html');assert sha(full)==unit['source_sha256']=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
before='A cube of side $s$ lies';after=r'Assume $s\ge0$, $\tau>0$ and $d\ge1$. '+before;assert full.read_text().count(before)==1
new=full.read_text().replace(before,after,1);assert new.replace(after,before,1).encode()==full.read_bytes()
P=B/'primer-linalg-cube-covering-positive-domain-prospective-unnumbered32.html';P.parent.mkdir(parents=True,exist_ok=True);P.write_text(new)
prop={**unit,'source_text':unit['source_text'].replace(before,after,1),'source_sha256':sha(P)};assert prop['source_text']!=unit['source_text'];prop['text_sha256']=hashlib.sha256(prop['source_text'].encode()).hexdigest()
body=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1] if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
lines=full.read_text().splitlines(keepends=True)
q={'status':'prepared_full_CubeRadiusNetMargin9_source_current191_component_prospective_domain_qualified191_whole_review_request','errors':[],
 'final_genuine_passed_source':retain(S),'public_theorem_count':9,'public_name_count':10,'definition_count':1,'all_public_declarations':names,'public_theorem_names':ts,'all9_complete_body_signatures':body,
 'entire_current_literal':unit,'exact_planned_prospective_domain_qualified_literal':prop,'prospective_full_Source81_page':ref(P),'unnumbered_exact_planned_replacements':[{'before':before,'after':after}],
 'actual_installed_owner31_pending_row':rows[0],'immutable_actual_installed_owner31':retain(OWN),'current_inventory81':retain(V),'full_current_Source81_linalg':retain(full),'full_norm_comparison_cube_and_radius_context_lines188_235':''.join(lines[187:235]),
 'full_current_Primer0_net_definitions':retain('SafeLearning/primer-basics.html'),'full_current_PrimerB_margin_and_net_context':retain('SafeLearning/primer-optimization.html'),
 'entire_four_selected_dependencies':selected,'old_Grid14_full_component_peer_original_scope_body_time_unchanged':oldpeer,'old_peer_does_not_decide_linalg191':True,
 'genuine_entire_passed5_byte_prefix':retain(old5),'full_passed5_is_exact_prefix_of9':True,
 'full_actual_used_Mathlib_primary_source_copies':providers,'all_genuine_native_histories':hist,'actual_standard_axioms_per_public_theorem':{n:[x.strip() for x in v.replace('\n',' ').split(',')] for n,v in ax},
 'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),
 'requested_full_mathematical_scope':'Read all9 new complete proofs/one projection definition, all four entire selected dependencies and actual used primary chains, entire current and prospective191 and linked net/margin context. Decide exact component scopes and prospective whole independently after separate positive-domain full29 proposal verification. Current191 is not approved by this author packet; no neighboring unit or existing old scope is widened.',
 'actual_cube_geometry_scope':'A cube defined by coordinate deviations <=s/2 about any center lies in the actual Euclidean ball of radius s sqrt(card I)/2; the actual corner attains that radius. The bound is invariant under an actual isometry, covering rotated cubes. New proofs include s0 and empty dimensions correctly; prospective cutting paragraph restricts d>=1 and positive tau.',
 'actual_centered_grid_count_scope':'Old full Grid14 genuinely derives the actual centered points(k+1/2)/N, coverage at endpoints, injectivity and exactN^d cardinality, ceilingN=ceil(sqrt d/(2tau)) and cover radius<=tau. Its genuine64 and1,099,511,627,776 values are construction counts/upper bounds for least covering number, not claims that they are the exact minimal numbers. Strict1.05e12<count<1.15e12 supports the printed about1.1e12.',
 'actual_full_margin_scope':'The actual Net24 arbitrary lower-margin provider proves m0-L*tau at every domain point for any finite domain-contained net and LipschitzOnWith L. New source supplies the exact finite-net wrapper and combines it with the actual ceiling grid. The result is the printed arbitrary m0 inequality, not merely a zero-threshold special case.',
 'actual_general_covering_number_scope':'The old selected least finite inside-cube net exists from the actual grid construction. Four new bodies use actual coordinate projection onto[0,1], prove it never increases Euclidean distance to any cube point, and map any ambient finite cover to an inside-cube cover with no larger cardinality. Thus the constructed least value is also IsLeast among all finite ambient-centered ball covers. No centre convention or minimum value is assumed.',
 'explicit_domain_and_scope_limits':'At tau0,d>0 a finite cube net is impossible; the reciprocal formula needs positive tau. The selected dimension0 branch is a singleton and does not justify ordinary m0 cutting wording. The one planned s>=0,tau>0,d>=1 opening qualification is explicit. General PrimerB algorithm, tight minimal numerical covering values, infinite-dimensional cube nets and other source units are not approved.',
 'current_or_prospective_whole191_approved_by_author':False,'no_Source_ordinal_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
retain(Path(__file__));q['physical_original_leaf_refs']=refs;q['required_evidence_artifacts_sha256']={r['file']:r['sha256'] for r in refs.values()}
O=B/'foundations-cube-radius-netmargin9-entire-source-current191-component-prospective191-whole-independent-review-request32-v1.json';O.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':ref(O),'public_theorems':9,'public_names':10,'source_codes':[h['actual_exit_code'] for h in hist[:3]],'physical_refs':len(refs)}))
