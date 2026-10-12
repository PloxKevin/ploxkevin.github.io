from pathlib import Path
import contextlib,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
B=Path('/tmp/foundations-common-matrixnorm-positive-dimensions-unnumbered32-v1');assert not B.exists()
Q=R/'book/coverage/checks/future32-foundations/common-mixed-matrixnorm21-full-scope-v1/foundations-common-mixed-inducednorm21-entire-source-three-literals-full-mathematical-independent-review-request32-v1.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
S=R/'SafeLearning/primer-linalg.html';V=R/'book/coverage/inventory-after-correction81.json';H=R/'book/inventory_claims.py'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute() else R/p;assert sha(p)==r['sha256'];return p
assert sha(Q)=='f79f36b9f416047769fe1a0f73cd8220a577541db7154a9f664b19a01647f7f7'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
assert sha(S)=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
assert sha(V)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
q=json.loads(Q.read_bytes());old=S.read_text()
before=r'$\|A\|_1=\max_j\sum_i|a_{ij}|$ (largest absolute <strong>column</strong> sum);'
after=r'For $m,n\ge1$, '+before
assert old.count(before)==1 and after not in old
new=old.replace(before,after,1);assert new.replace(after,before,1).encode()==S.read_bytes()
assert old.count('\n')==new.count('\n')
sys.path.insert(0,str(R/'book'));from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(old).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
B.mkdir();current=B/'primer-linalg-source81-immutable-original.html';current.write_bytes(S.read_bytes())
P=B/'primer-linalg-common-norms-positive-dimensions-prospective-unnumbered32.html';P.write_text(new)
I=B/'isolated-full29-parser';(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):
 (I/'SafeLearning'/p.name).write_bytes(P.read_bytes() if p==S else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('common_norms_dimensions32_author_both_ROOT_OUT',H)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.ROOT=I;m.OUT=I/'book/coverage'
assert m.ROOT.resolve().is_relative_to(B) and m.OUT.resolve().is_relative_to(B)
raw=B/'actual-author-full29-parser-stdout.log'
with raw.open('x') as f,contextlib.redirect_stdout(f):m.inventory()
parsed=json.loads((m.OUT/'inventory.json').read_bytes());inv=json.loads(V.read_bytes())
assert parsed['counts']==inv['counts'] and parsed['counts']['exercises']==556 and parsed['counts']['material_source_units']==12774
assert parsed['source_sha256']=={**inv['source_sha256'],'SafeLearning/primer-linalg.html':sha(P)}
changes={};literals={}
for field in ['exercises','material_source_units']:
 a={r['key']:r for r in inv[field]};b={r['key']:r for r in parsed[field]};assert a.keys()==b.keys();changes[field]=[]
 for k in a:
  x=dict(a[k]);y=dict(b[k])
  if x['source']=='SafeLearning/primer-linalg.html':x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {n:v for n,v in x.items() if n not in ['source_text','text_sha256']}=={n:v for n,v in y.items() if n not in ['source_text','text_sha256']}
   changes[field].append(k);literals[k]={'entire_current':a[k],'entire_proposed':b[k]}
assert changes=={'exercises':[],'material_source_units':['primer-linalg.html::node-305','primer-linalg.html::node-307']}
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if any(k in r.get('source_unit_keys',[]) for k in changes['material_source_units'])]
passed=q['all_genuine_native_histories'][6];native=json.loads(checked(passed['native']).read_bytes())
assert native['actual_exit_code']==native['actual_runner_exit_code']==0 and native['protection_errors']==[]
assert q['public_theorem_count']==21 and q['public_name_count']==25 and passed['source']['sha256']==q['final_genuine_passed_source']['sha256']
qprep=Path('/tmp/foundations-common-mixed-matrixnorm21-full-scope-author-preparation32-actual-v1.json')
qp=json.loads(qprep.read_bytes());assert qp['actual_exit_code']==0 and qp['protection_errors']==[]
d={'status':'prepared_TMP_only_unnumbered_common_induced_norms_positive_dimensions_author_actual_full29_parser_passed',
 'prospective_source_number':None,'source_number_reserved':False,'source_applied':False,
 'source':ref(current),'live_source_original_path':'SafeLearning/primer-linalg.html','before_inventory':ref(V),
 'before_corrections':ref(R/'book/coverage/material-corrections.json'),'parser':ref(H),'validator':ref(R/'book/validate.py'),
 'proposed_source':ref(P),'exact_replacements':[{'before':before,'after':after}],
 'both_parser_ROOT_and_OUT_isolated':True,'fresh_changed_literal_keys':changes,
 'entire_current_and_proposed_literal_records':literals,
 'entire_unchanged_current_and_prospective311_proof_fixture':{
  'current':next(r for r in inv['material_source_units'] if r['key']=='primer-linalg.html::node-311'),
  'prospective':next(r for r in parsed['material_source_units'] if r['key']=='primer-linalg.html::node-311')},
 'full_current_p_norm_domain_and_induced_formula_context_lines139_350':''.join(old.splitlines(keepends=True)[138:350]),
 'full_proposed_p_norm_domain_and_induced_formula_context_lines139_350':''.join(new.splitlines(keepends=True)[138:350]),
 'exact_installed_owner31_changed_material_rows':rows,'immutable_installed_owner31_candidate':ref(OWN),
 'proposed_full29_inventory':ref(m.OUT/'inventory.json'),'actual_parser_stdout':ref(raw),'parser_counts':parsed['counts'],
 'all_other28_pages_and_all_other_literal_records_exact':True,'full_nodes_tags_attrs_lines_preserved':True,
 'exact_inverse_returns_entire_current81_page_bytes':True,
 'supporting_entire21_source_and_histories_request':ref(Q),'actual_supporting_passed_source':q['final_genuine_passed_source'],
 'actual_supporting_source_trial7':passed,'actual_all21_standard_axiom_inspection':q['all_genuine_native_histories'][-1],
 'supporting_full_math_request_genuine_preparation_native':ref(qprep),'full_three_selected_sources':q['entire_three_selected_dependencies'],
 'old_dependency_independent_peers_unchanged':q['old_dependency_independent_peer_refs_no_body_or_time_redecision'],
 'mathematical_rationale':[
  'The previous induced-norm definition already requires a nonempty input domain. The simultaneous table also uses row and entry maxima; positive m,n makes every printed maximum, unit sphere and named largest singular value literal.',
  'The actual proofs permit empty non-maximizing dimensions where a formula still has a defined maximum and gives0. They do not invent a finite maximum on an empty index set. This narrow wording adopts one common positive-dimensional domain for the whole table.',
  'Exponent p>=1 and infinity endpoints are already the preceding source p-norm convention. The generic mixed formulas prove all Holder conjugates, including both endpoints. The new named singularValues correspondence is proved using actual Gram eigenvalues and adjoint composition.',
  'The following proof paragraph and2x2 running matrix have unchanged text, values, approximate2.83 and true full ellipse association. Zero-matrix sign0 is a valid ball attainer of a zero bound, not a claim that the zero sign vector has norm1.' ],
 'current_or_prospective_whole_units_not_approved_by_this_narrow_packet':True,
 'independent_narrow_literal_support_and_fresh_parser_review_pending':True,
 'compiler_canonical_owner_selection_or_publication_mutations':False,'coverage_complete':False}
O=B/'foundations-common-inducednorms-positive-dimensions-one-phrase-unnumbered-full29-proposal32-v1.json'
O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'proposal':ref(O),'changed':changes,'proposed_source':ref(P)}))
