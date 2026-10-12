from pathlib import Path
import contextlib, hashlib, importlib.util, json, sys
sys.dont_write_bytecode = True
R = Path('/home/oxrexkevin/SafetyBased')
B = Path('/tmp/modules-thermal-threshold-unnumbered-proposal30-v1')
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
 {'before':r'Requiring it to be strictly smaller gives $p\gt(27.4-8.852459)/0.8\approx23.184426$.',
  'after':r'Requiring it to be strictly smaller gives $p\gt(27.4-540/61)/0.8=5657/244\approx23.184426$.'}]

new=old
for replacement in replacements:
 assert new.count(replacement['before'])==1 and replacement['after'] not in new
 new=new.replace(replacement['before'],replacement['after'],1)
inverse=new
for replacement in reversed(replacements):
 inverse=inverse.replace(replacement['after'],replacement['before'],1)
assert inverse.encode()==source.read_bytes()
assert old.count('\n')==new.count('\n')
proposed=B/'viability-threshold-proposed-unnumbered.html'
proposed.write_text(new)
sys.path.insert(0,str(R/'book'))
from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(old).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
I=B/'isolated-full29-parser'
(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):
 (I/'SafeLearning'/p.name).write_bytes(proposed.read_bytes() if p==source else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('gp_discrepancy_author_tmp_both_roots',parser)
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
assert changes=={'exercises':['viability.html#book-m7-b2'],'material_source_units':['viability.html::node-875']}
owner=json.loads(ownerpath.read_bytes())
ex=next(r for r in owner['exercises'] if r['inventory_key']=='viability.html#book-m7-b2')
assert ex['status']=='partial'
affected=[r for r in owner['material_claims'] if set(r.get('source_unit_keys',[])) & {'viability.html::node-875'}]
proof=Path('/tmp/CompleteModulesThermalPenaltyBellmanWhole30-draft-v5.lean')
native=Path('/tmp/modules-thermal-penalty-bellman-whole30-owner29-trial5.json')
n=json.loads(native.read_bytes())
assert n['actual_exit_code']==0 and n['protection_errors']==[] and n['source_sha256_before']==n['source_sha256_after']==sha(proof)
out={'status':'prepared_TMP_only_unnumbered_thermal_exact_strict_penalty_threshold_and_rounded_decimal_proposal_actual_full29_author_parser_passed',
 'prospective_source_number':None,'source_number_reserved':False,'source_applied':False,
 'source':ref(source),'before_inventory':ref(invpath),'before_corrections':ref(R/'book/coverage/material-corrections.json'),
 'parser':ref(parser),'validator':ref(R/'book/validate.py'),'proposed_source':ref(proposed),
 'exact_replacements':replacements,'both_parser_ROOT_and_OUT_isolated':True,
 'fresh_changed_literal_keys':changes,'entire_current_and_proposed_literal_records':literals,
 'full_current_thermal_commissioning_and_B2_context_lines674_709':''.join(old.splitlines(keepends=True)[673:709]),
 'full_proposed_thermal_commissioning_and_B2_context_lines674_709':''.join(new.splitlines(keepends=True)[673:709]),
 'exact_current_owned_exercise_body':ex,'exact_current_owned_changed_material_claim_rows':affected,
 'original_owner29_candidate':ref(ownerpath),'proposed_full29_inventory':ref(m.OUT/'inventory.json'),
 'actual_parser_stdout':ref(parserraw),'parser_counts':parsed['counts'],
 'all_other28_page_bytes_and_all_other_literal_records_exact':True,
 'full_nodes_tags_attrs_lines_preserved':True,'exact_inverse_returns_entire_current65_page_bytes':True,
 'actual_supporting_full_thermal_infinite_return_and_optimal_policy_source':ref(proof),'actual_supporting_passed_trial5':ref(native),
 'actual_supporting_source_snapshot':ref(n['source_snapshot']),'actual_supporting_raw_log':ref(n['raw_log']),
 'rationale':['The actual best safe gamma.8 infinite return is exactly540/61 and the exact strict penalty threshold is5657/244. The actual all-history optimal first-action theorem proves strict necessity and sufficiency for nonnegative penalties and includes an unsafe maximizing history at equality.',
 'The source currently substitutes the rounded8.852459 inside an exact strict inequality. That rounded safe value is strictly less than540/61, so its derived threshold is strictly greater than5657/244. The proposed exact rational formula corrects this small discrepancy while preserving the original approximate23.184426 target.',
 'The complete actual40-body proof separately establishes arbitrary-history Bellman/infinite-return correspondence, attained optimal histories, best safe histories at gamma.8 and.9, p24, the equality tie, and the shorter-horizon comparison. This narrow proposal itself neither promotes that whole proof nor changes any owner.'],
 'whole_exercise_or_whole_node875_mathematical_approval_pending_separate_full_peer':True,
 'compiler_canonical_owner_selection_or_publication_mutations':False,'coverage_complete':False}
P=B/'modules-thermal-threshold-unnumbered-full29-proposal30-v1.json'
P.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'proposal':ref(P),'changed':changes,'proposed_source':ref(proposed),'parser_stdout_bytes':parserraw.stat().st_size}))
