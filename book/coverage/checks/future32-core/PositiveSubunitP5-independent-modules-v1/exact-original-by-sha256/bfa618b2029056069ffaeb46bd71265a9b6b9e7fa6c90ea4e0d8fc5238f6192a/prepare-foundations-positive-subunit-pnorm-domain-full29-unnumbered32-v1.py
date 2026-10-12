from pathlib import Path
import contextlib,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
B=Path('/tmp/foundations-positive-subunit-pnorm-domain-unnumbered32-v1');assert not B.exists()
Q=R/'book/coverage/checks/future32-foundations/positive-subunit-pnorm5-full-scope-v1/foundations-positive-subunit-pnorm5-entire-source-current171-components-prospective171-whole-independent-review-request32-v1.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
S=R/'SafeLearning/primer-linalg.html';V=R/'book/coverage/inventory-after-correction81.json';H=R/'book/inventory_claims.py'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute() else R/p;assert sha(p)==r['sha256'];return p
assert sha(Q)=='299db96c3057620a3284dedcc7d14d719d63095d2dbeaba0528f69eca1cc6b11'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
assert sha(S)=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
assert sha(V)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
q=json.loads(Q.read_bytes());old=S.read_text()
before=r'For $p\lt1$ the formula is not a norm:'
after=r'In dimensions $n\ge2$, for $0\lt p\lt1$ the formula is not a norm:'
assert old.count(before)==1 and after not in old
new=old.replace(before,after,1);assert new.replace(after,before,1).encode()==S.read_bytes()
assert old.count('\n')==new.count('\n')
sys.path.insert(0,str(R/'book'));from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(old).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
B.mkdir();current=B/'primer-linalg-source81-immutable-original.html';current.write_bytes(S.read_bytes())
P=B/'primer-linalg-positive-subunit-pnorm-domain-prospective-unnumbered32.html';P.write_text(new)
I=B/'isolated-full29-parser';(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):
 (I/'SafeLearning'/p.name).write_bytes(P.read_bytes() if p==S else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('positive_subunit_pnorm_domain32_author_both_ROOT_OUT',H)
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
assert changes=={'exercises':[],'material_source_units':['primer-linalg.html::node-171']}
assert P.read_bytes()==checked(q['prospective_full_Source81_page']).read_bytes()
assert literals['primer-linalg.html::node-171']['entire_proposed']==q['exact_planned_prospective_domain_qualified_literal']
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if any(k in r.get('source_unit_keys',[]) for k in changes['material_source_units'])]
passed=q['all_genuine_native_histories'][2];native=json.loads(checked(passed['native']).read_bytes())
assert native['actual_exit_code']==native['actual_runner_exit_code']==0 and native['protection_errors']==[]
assert q['public_theorem_count']==5 and q['public_name_count']==6 and passed['source']['sha256']==q['final_genuine_passed_source']['sha256']
qprep=Path('/tmp/foundations-positive-subunit-pnorm5-full-scope-author-preparation32-actual-v1.json')
qp=json.loads(qprep.read_bytes());assert qp['actual_exit_code']==0 and qp['protection_errors']==[]
d={'status':'prepared_TMP_only_unnumbered_positive_subunit_pnorm_domain_author_actual_full29_parser_passed',
 'prospective_source_number':None,'source_number_reserved':False,'source_applied':False,
 'source':ref(current),'live_source_original_path':'SafeLearning/primer-linalg.html','before_inventory':ref(V),
 'before_corrections':ref(R/'book/coverage/material-corrections.json'),'parser':ref(H),'validator':ref(R/'book/validate.py'),
 'proposed_source':ref(P),'exact_replacements':[{'before':before,'after':after}],
 'both_parser_ROOT_and_OUT_isolated':True,'fresh_changed_literal_keys':changes,
 'entire_current_and_proposed_literal_records':literals,
 'full_current_norm_context_lines155_190':''.join(old.splitlines(keepends=True)[154:190]),
 'full_proposed_norm_context_lines155_190':''.join(new.splitlines(keepends=True)[154:190]),
 'exact_installed_owner31_changed_material_rows':rows,'immutable_installed_owner31_candidate':ref(OWN),
 'proposed_full29_inventory':ref(m.OUT/'inventory.json'),'actual_parser_stdout':ref(raw),'parser_counts':parsed['counts'],
 'all_other28_pages_and_all_other_literal_records_exact':True,'full_nodes_tags_attrs_lines_preserved':True,
 'exact_inverse_returns_entire_current81_page_bytes':True,
 'supporting_entire5_source_and_histories_request':ref(Q),'actual_supporting_passed_source':q['final_genuine_passed_source'],
 'actual_supporting_source_trial3':passed,'actual_all5_standard_axiom_inspection':q['all_genuine_native_histories'][-1],
 'supporting_full_math_request_genuine_preparation_native':ref(qprep),
 'full_current_Module11_norm_convention_source':q['full_current_Module11_norm_convention_source'],'bounded_actual_two_primary_norm_facts':q['bounded_two_remote_primary_norm_facts_with_actual_HTTP200_text0_receipts'],
 'mathematical_rationale':[
  'The actual positive-power formula is considered on the standard finite coordinate domain. For every exponent0<p<1 and every dimension at least2, two actual coordinate units yield strict triangle violation; no desired violation is a premise.',
  'The printed half-exponent fixture is exactly4 versus1+1=2. On Fin1 for every positive p, the formula equals absolute value, so dimension at least2 is necessary for this generic non-norm assertion. Nonpositive exponents are excluded rather than silently defined by totalized real powers.',
  'The primary citations and local Module11 norm conventions remain unchanged and are checked in the separate full mathematical request: Berkenkamp actual1norm assumptions; actual robustMPC infinity-input bounds and explicit local Euclidean-state convention.' ],
 'current_or_prospective_whole_units_not_approved_by_this_narrow_packet':True,
 'independent_narrow_literal_support_and_fresh_parser_review_pending':True,
 'compiler_canonical_owner_selection_or_publication_mutations':False,'coverage_complete':False}
O=B/'foundations-positive-subunit-pnorm-domain-one-phrase-unnumbered-full29-proposal32-v1.json'
O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'proposal':ref(O),'changed':changes,'proposed_source':ref(P)}))
