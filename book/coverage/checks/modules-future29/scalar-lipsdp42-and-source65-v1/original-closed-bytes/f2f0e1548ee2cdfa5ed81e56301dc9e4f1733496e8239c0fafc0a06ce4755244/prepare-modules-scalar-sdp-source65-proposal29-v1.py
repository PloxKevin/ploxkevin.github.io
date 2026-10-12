from pathlib import Path
from datetime import datetime,timezone
import sys,json,hashlib,importlib.util
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules-scalar-sdp-source65-proposal29-v1');assert not B.exists();B.mkdir();sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def read(p):return json.loads(Path(p).read_bytes())
invpath=R/'book/coverage/inventory.json';corrpath=R/'book/coverage/material-corrections.json';source=R/'SafeLearning/lipsdp.html';parserpath=R/'book/inventory_claims.py';assert sha(invpath)=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a';assert sha(corrpath)=='90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81';assert sha(source)=='c246dca4323f90c9d390c74dbd253872564627c225e24321b363fb2e4ffba5dc'
old=source.read_text();replacements=[{'before':"A larger supplied $\\beta$ makes it loose by the factor $\\beta/\\sup\\varphi'$.",'after':"When $\\sup_u\\varphi'(u)\\gt0$, a larger supplied $\\beta$ makes it loose by the factor $\\beta/\\sup_u\\varphi'$. If the activation is constant, its true Lipschitz constant is $0$ while a positive supplied $\\beta$ still gives a positive bound; there is no finite multiplicative ratio."},{'before':'has eigenvalues $-1.318$ and $0$.','after':'has eigenvalues $-1.3181$ and $0$ (the negative eigenvalue rounds to $-1.318$ at three decimal places).'}]
new=old
for p in replacements:assert new.count(p['before'])==1 and p['after']not in new;new=new.replace(p['before'],p['after'],1)
back=new
for p in reversed(replacements):back=back.replace(p['after'],p['before'],1)
assert back.encode()==source.read_bytes()and old.count('\n')==new.count('\n')
proposed=B/'lipsdp-proposed-source65.html';proposed.write_text(new)
sys.path.insert(0,str(R/'book'));from validate import Document
assert [(n.tag,n.attrs,n.line)for n in Document(old).nodes]==[(n.tag,n.attrs,n.line)for n in Document(new).nodes]
I=B/'isolated-full29-parser';(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):(I/'SafeLearning'/p.name).write_bytes(proposed.read_bytes()if p==source else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('source65_author_parser_tmp_bothroots_v1',parserpath);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.ROOT=I;m.OUT=I/'book/coverage';assert m.ROOT.resolve().is_relative_to(B)and m.OUT.resolve().is_relative_to(B);m.inventory();parsed=read(m.OUT/'inventory.json');inv=read(invpath);assert parsed['counts']==inv['counts'];assert parsed['source_sha256']=={**inv['source_sha256'],'SafeLearning/lipsdp.html':sha(proposed)}
changes={};literals={}
for field in ['exercises','material_source_units']:
 a={x['key']:x for x in inv[field]};b={x['key']:x for x in parsed[field]};assert a.keys()==b.keys();changes[field]=[]
 for key in a:
  x=dict(a[key]);y=dict(b[key])
  if x['source']=='SafeLearning/lipsdp.html':x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {n:v for n,v in x.items()if n not in ['source_text','text_sha256']}=={n:v for n,v in y.items()if n not in ['source_text','text_sha256']};changes[field].append(key);literals[key]={'entire_current':a[key],'entire_proposed':b[key]}
assert changes=={'exercises':['lipsdp.html::exercise-19'],'material_source_units':['lipsdp.html::node-1328','lipsdp.html::node-1329']}
owner=read(R/'book/coverage/modules.json');ex=next(x for x in owner['exercises']if x['inventory_key']=='lipsdp.html::exercise-19');rows=[x for x in owner['material_claims']if set(x.get('source_unit_keys',[]))&set(changes['material_source_units'])]
proof=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v7.lean');native=Path('/tmp/modules-scalar-lipsdp-optimum29-owner28-trial7.json');d=read(native);assert d['actual_exit_code']==0 and d['protection_errors']==[]and d['source_sha256_before']==d['source_sha256_after']==sha(proof)
P=B/'modules-scalar-sdp-source65-proposal29-v1.json';out={'status':'TMP_only_reserved_future_source65_positive_loose_factor_and_exact_eigenvalue_proposal_genuine_author_full29_parser_passed','author':'/root/modules_finish28','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'prospective_source_batch':65,'source65_reserved_by_Root':True,'source65_applied':False,'exact_replacements':replacements,'source':ref(source),'before_inventory':ref(invpath),'before_corrections':ref(corrpath),'parser':ref(parserpath),'proposed_source':ref(proposed),'proposed_full29_inventory':ref(m.OUT/'inventory.json'),'both_parser_ROOT_and_OUT_isolated':True,'full_nodes_tags_attrs_lines_preserved':True,'exact_inverse_returns_entire_current60_page_bytes':True,'fresh_changed_literal_keys':changes,'counts':parsed['counts'],'entire_current_and_proposed_literal_records':literals,'full_current_exercise_context_lines1007_1026':''.join(old.splitlines(keepends=True)[1006:1026]),'full_proposed_exercise_context_lines1007_1026':''.join(new.splitlines(keepends=True)[1006:1026]),'exact_current_owned_exercise_body':ex,'exact_current_owned_changed_material_claim_rows':rows,'immutable_owner28_snapshot':ref(R/'reports/full-coverage/checkpoint-28/book/coverage/modules.json'),'supporting_full42_lean_source':ref(proof),'actual_supporting_trial7':ref(native),'source_snapshot':ref(Path(d['source_snapshot'])),'raw_log':ref(Path(d['raw_log'])),'genuine_support_compiled':True,'actual_emitted_warning_count':Path(d['raw_log']).read_text().count('warning:'),'rationale':['The nonnegative slope-restricted constant activation phi(x)=k has actual least activation/network Lipschitz constant0; positive supplied beta gives a positive network certificate for nonzero weights. A finite multiplicative ratio beta/sup deriv needs a positive supremum. The genuine derivative supremum least-constant theorem covers arbitrary slope-restricted Lipschitz nonsmooth activations via absolute continuity and FTC, not a differentiability-everywhere assumption.','Exact printed ReLU weights produce M=[[-.8281,.637],[.637,-.49]], determinant0/trace-1.3181. Genuine characteristic polynomial and two nonzero eigenvectors prove eigenvalues-1.3181 and0. The negative value lies strictly within.0005 of-1.318, preserving the original numerical rounding target.'],'whole_exercise12_5_or_material_approved_before_full_independent_peer':False,'canonical_source_owner_selection_publication_changes':False,'coverage_complete':False,'original_context_current60_explicitly_historical_after_later_source61_64_application':True};P.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'proposal':ref(P),'changed':changes,'supporting_public_bodies':42}))
