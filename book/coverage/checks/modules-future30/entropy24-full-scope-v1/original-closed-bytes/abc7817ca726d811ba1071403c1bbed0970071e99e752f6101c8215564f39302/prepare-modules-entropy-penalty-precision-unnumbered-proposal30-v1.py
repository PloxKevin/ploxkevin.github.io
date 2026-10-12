from pathlib import Path
import contextlib, hashlib, importlib.util, json, sys
sys.dont_write_bytecode = True
R = Path('/home/oxrexkevin/SafetyBased')
B = Path('/tmp/modules-entropy-penalty-precision-unnumbered-proposal30-v1')
assert not B.exists()
B.mkdir()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p)
 return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p), 'sha256':sha(p), 'bytes':p.stat().st_size}
source=R/'SafeLearning/viability.html'
invpath=R/'book/coverage/inventory-after-correction65.json'
parser=R/'book/inventory_claims.py'
ownerpath=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(source)=='0b0a8a5710cd4ce278e30c1c7a5534ba5f4388c7956d60a1e701c02b572490c0'
assert sha(invpath)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert sha(ownerpath)=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
old=source.read_text()
replacements=[
 {'before':r'with $-\ln 10^{-2} = 4.605$.', 'after':r'with $-\ln 10^{-2} = 2\ln10\approx4.605$.'},
 {'before':r'$p_1 = 10 + 0.5(2 + 4.605) = 13.30$', 'after':r'$p_1 = 11+\ln10\approx13.30$'},
 {'before':r'$p_1 = 10 + 2(6.605) = 23.21$', 'after':r'$p_1 = 14+4\ln10\approx23.21$'},
 {'before':r'$1.15$ at $\alpha = 0.5$ and $4.61$ at $\alpha = 2$', 'after':r'$0.5\ln10\approx1.15$ at $\alpha = 0.5$ and $2\ln10\approx4.61$ at $\alpha = 2$'},
 {'before':'Each decade of safety costs a penalty increment proportional to the temperature, which is why a fixed penalty is eventually overcome by a high temperature and why the paper recommends scaling $p$ with $\\alpha$.',
 'after':'Each decade of safety costs a penalty increment proportional to the temperature, and the sufficient threshold above grows with $\\alpha$. Its bound alone does not prove that every fixed-penalty problem becomes unsafe at high temperature; the paper recommends scaling $p$ with $\\alpha$ and reports this competition in its cliff-world example.'}]

new=old
for replacement in replacements:
 assert new.count(replacement['before'])==1 and replacement['after'] not in new
 new=new.replace(replacement['before'],replacement['after'],1)
inverse=new
for replacement in reversed(replacements):
 inverse=inverse.replace(replacement['after'],replacement['before'],1)
assert inverse.encode()==source.read_bytes()
assert old.count('\n')==new.count('\n')
proposed=B/'viability-entropy-penalty-precision-proposed-unnumbered.html'
proposed.write_text(new)
sys.path.insert(0,str(R/'book'))
from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(old).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
I=B/'isolated-full29-parser'
(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):
 (I/'SafeLearning'/p.name).write_bytes(proposed.read_bytes() if p==source else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('entropy_penalty_precision_author_tmp_both_roots',parser)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
m.ROOT=I
m.OUT=I/'book/coverage'
assert m.ROOT.resolve().is_relative_to(B) and m.OUT.resolve().is_relative_to(B)
parserraw=B/'actual-author-full29-parser-stdout.log'
with parserraw.open('x') as f, contextlib.redirect_stdout(f): m.inventory()
parsed=json.loads((m.OUT/'inventory.json').read_bytes())
inv=json.loads(invpath.read_bytes())
assert parsed['counts']==inv['counts']
assert parsed['source_sha256']=={**inv['source_sha256'],'SafeLearning/viability.html':sha(proposed)}
changes={}; literals={}
for field in ['exercises','material_source_units']:
 a={r['key']:r for r in inv[field]}; b={r['key']:r for r in parsed[field]}
 assert a.keys()==b.keys()
 changes[field]=[]
 for k in a:
  x=dict(a[k]); y=dict(b[k])
  if x['source']=='SafeLearning/viability.html': x.pop('source_sha256'); y.pop('source_sha256')
  if x!=y:
   assert {n:v for n,v in x.items() if n not in ['source_text','text_sha256']}=={n:v for n,v in y.items() if n not in ['source_text','text_sha256']}
   changes[field].append(k); literals[k]={'entire_current':a[k],'entire_proposed':b[k]}
assert changes=={'exercises':['viability.html::exercise-20'],'material_source_units':['viability.html::node-1174']}
owner=json.loads(ownerpath.read_bytes())
ex=next(r for r in owner['exercises'] if r['inventory_key']=='viability.html::exercise-20')
assert ex['status']=='pending'
affected=[r for r in owner['material_claims'] if set(r.get('source_unit_keys',[])) & {'viability.html::node-1174'}]
proof=Path('/tmp/CompleteModulesViabilityEntropyWhole30-draft-v5.lean')
native=Path('/tmp/modules-viability-entropy-whole30-owner29-trial5.json')
n=json.loads(native.read_bytes())
assert n['actual_exit_code']==0 and n['protection_errors']==[] and n['source_sha256_before']==n['source_sha256_after']==sha(proof)
out={'status':'prepared_TMP_only_unnumbered_entropy_exact_logarithmic_penalties_rounded_original_targets_and_sufficient_bound_scope_proposal_actual_full29_author_parser_passed',
 'prospective_source_number':None,'source_number_reserved':False,'source_applied':False,
 'source':ref(source),'before_inventory':ref(invpath),'before_corrections':ref(R/'book/coverage/material-corrections.json'),
 'parser':ref(parser),'validator':ref(R/'book/validate.py'),'proposed_source':ref(proposed),
 'exact_replacements':replacements,'both_parser_ROOT_and_OUT_isolated':True,
 'fresh_changed_literal_keys':changes,'entire_current_and_proposed_literal_records':literals,
 'full_current_entropy_exercise_context_lines958_972':''.join(old.splitlines(keepends=True)[957:972]),
 'full_proposed_entropy_exercise_context_lines958_972':''.join(new.splitlines(keepends=True)[957:972]),
 'exact_current_owned_exercise_body':ex,'exact_current_owned_changed_material_claim_rows':affected,
 'original_owner29_candidate':ref(ownerpath),'proposed_full29_inventory':ref(m.OUT/'inventory.json'),
 'actual_parser_stdout':ref(parserraw),'parser_counts':parsed['counts'],
 'all_other28_page_bytes_and_all_other_literal_records_exact':True,
 'full_nodes_tags_attrs_lines_preserved':True,'exact_inverse_returns_entire_current65_page_bytes':True,
 'actual_supporting_full_entropy_support_KL_softmax_exact_threshold_and_rounding_source':ref(proof),'actual_supporting_passed_trial5':ref(native),
 'actual_supporting_source_snapshot':ref(n['source_snapshot']),'actual_supporting_raw_log':ref(n['raw_log']),
 'rationale':['The logarithm is exactly -ln(10^-2)=2ln10, not4.605; both actual rational bounds and a genuine non-equality theorem support retaining4.605 only as an approximation.',
 'The two exact sufficient thresholds are11+ln10 and14+4ln10. The printed13.30 is slightly below the first threshold; neither rounded decimal is asserted to itself guarantee safety. Exact symbolic thresholds come first, followed by unchanged two-decimal approximations.',
 'An extra decade costs exactly alpha ln10/u3. The two concrete costs are0.5ln10 and2ln10, followed by the unchanged valid approximations1.15 and4.61.',
 'Actual normalized softmax and the two-sided Q estimates derive the sufficient threshold. A conservative sufficient bound growing with temperature does not alone imply universal actual unsafety. The true affine growth and eventual comparison are proved, while the cliff-world behavior is separately attributed to the directly read primary experimental section6.1.2/Fig3.',
 'Only five phrases in one numerical/explanatory answer paragraph1174 change; full Exercise7.6 follows automatically. All other text, hypotheses, source tags, lines, original owner claims and native source/body/time remain exact. No source ordinal/application/whole semantic promotion is claimed.'],
 'whole_exercise_or_whole_node1174_mathematical_approval_pending_separate_full_peer':True,
 'compiler_canonical_owner_selection_or_publication_mutations':False,'coverage_complete':False}
P=B/'modules-entropy-penalty-precision-unnumbered-full29-proposal30-v1.json'
P.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'proposal':ref(P),'changed':changes,'proposed_source':ref(proposed),'parser_stdout_bytes':parserraw.stat().st_size}))
