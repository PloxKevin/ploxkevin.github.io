from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,importlib.util,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp/foundations-hertneck-source53-fresh-parser-review26-v1');OUT=Path('/tmp/hertneck-source53-independent-foundations-semantic-parser-observation26-v1.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(p),'sha256':H(p)}
assert not TMP.exists()and not OUT.exists()
P=Path('/tmp/hertneck-finite-entry-clarification-source53-proposal26-v1.json');A=Path('/tmp/hertneck-current52-eventual-entry-independent-applied-semantic-review26-v1.json');G=Path('/tmp/lyapunov-two-core-exercises26-independent-applied-full-gap-review-v1.json')
assert H(P)=='c5bed7f3a865cc1197801707605c592129b4c09c02493dc2c21d1395f78cf66a';assert H(A)=='c4cc8077c33d033aebda2a6bb28875336a4a1202ce715bc81e00c6cd70e061c0';assert H(G)=='b780754b5d330c88ecf8aacf1e173e85383ecfada980ffe880dca2f00c16e162'
p=json.loads(P.read_text());a=json.loads(A.read_text());gap=json.loads(G.read_text());assert a['preserved_entire_original_gap_review_body_and_time']==gap
INV=ROOT/'book/coverage/inventory-after-correction52.json';assert H(INV)==H(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';inv=json.loads(INV.read_text())
source=ROOT/p['source'];before=source.read_text();assert H(source)==p['source_sha256_before']=='228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'
primary=ROOT/'sources/text/hertneck.txt';assert H(primary)=='f0d8687a0368e2c4eec9ea3a6bad70ea5456793c5a275b9c0f1b4a8942746c97';pl=primary.read_text().splitlines();bl=before.splitlines()
for c in a['primary_direct_locations_actually_read']:assert '\n'.join(pl[c['first_line']-1:c['last_line']])==c['complete_lines']
for k in ['full_current_theorem_and_validation_context','full_current_exercise_context']:
 c=a[k];assert '\n'.join(bl[c['first_line']-1:c['last_line']])==c['complete_lines']
units={r['key']:r for r in inv['material_source_units']};exercises={r['key']:r for r in inv['exercises']}
assert p['entire_original_exercise']==exercises['lyapunov-mpc.html::exercise-18']
for r in p['entire_original_material_records']:assert r==units[r['key']]
assert len(p['replacements'])==2;after=before
for r in p['replacements']:
 assert r['count']==1 and after.count(r['before'])==1 and '\n'not in r['before']+r['after'];after=after.replace(r['before'],r['after'],1)
assert hashlib.sha256(after.encode()).hexdigest()==p['proposed_source_sha256_after']=='d92f5baf636ce523cfd741097cf8a333ca1797096982a083c87991ef2e68b752'
rev=after
for r in reversed(p['replacements']):assert rev.count(r['after'])==1;rev=rev.replace(r['after'],r['before'],1)
assert rev==before and after.count('\n')==before.count('\n')
protocol='A run counts as a success only if it reaches $X_f$ and the error bound held at every step before; in finite computation, fix a maximal horizon and count non-entry by then as failure (conservative).';assert before.count(protocol)==after.count(protocol)==1
sys.path.insert(0,str(ROOT/'book'));from validate import Document
od,nd=Document(before),Document(after);assert[(n.tag,n.attrs,n.line)for n in od.nodes]==[(n.tag,n.attrs,n.line)for n in nd.nodes]
# Fresh full29 parser is imported with its ROOT and OUT redirected before calling inventory.
(TMP/'SafeLearning').mkdir(parents=True)
html=list((ROOT/'SafeLearning').glob('*.html'));assert len(html)==29
protected={str(q.relative_to(ROOT)):H(q)for q in (ROOT/'SafeLearning').iterdir()if q.suffix in {'.html','.css','.js'}};assert len(protected)==31
for q in html:shutil.copyfile(q,TMP/'SafeLearning'/q.name)
(TMP/p['source']).write_text(after)
parser=ROOT/'book/inventory_claims.py';assert H(parser)=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
spec=importlib.util.spec_from_file_location('independent_hertneck53_tmp_parser',parser);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);g.ROOT=TMP;g.OUT=TMP/'book/coverage';assert g.ROOT!=ROOT and g.OUT.resolve().is_relative_to(TMP);g.inventory()
fresh=json.loads((g.OUT/'inventory.json').read_text());assert fresh['counts']==inv['counts']
changes={}
for section in ['exercises','material_source_units']:
 old={r['key']:r for r in inv[section]};new={r['key']:r for r in fresh[section]};assert old.keys()==new.keys();changed=[]
 for k,r in old.items():
  nr=new[k];assert r.keys()==nr.keys();assert all(r[f]==nr[f]for f in r if f not in {'source_sha256','source_text','text_sha256'}),(k,'structure')
  if r['source_text']!=nr['source_text']:changed.append(k)
  else:assert r['text_sha256']==nr['text_sha256']
  if r['source']!=p['source']:assert r==nr
 changes[section]=changed
assert changes==p['expected_changed_text_keys']=={'exercises':['lyapunov-mpc.html::exercise-18'],'material_source_units':['lyapunov-mpc.html::node-753','lyapunov-mpc.html::node-755','lyapunov-mpc.html::node-1387']}
selection=ROOT/'reports/full-coverage/checkpoint-25-selection.json';sel=json.loads(selection.read_text());assert len(sel['proof_files'])==1156
for n,r in sel['proof_files'].items():assert H(ROOT/n)==r['sha256']
owners={n:H(ROOT/'book/coverage'/ (n+'.json'))for n in ['core','foundations','applied','modules','applied-promotions']}
for n,h in protected.items():assert H(ROOT/n)==h
assert H(ROOT/'book/coverage/inventory.json')==H(INV)
decisions=[{'id':'indicator-exact-success-event','approved':True,'reason':'Finite first terminal entry and the error bound at each pre-entry applied approximate-control step make explicit the already present conservative success protocol. Non-entry is failure; entry at time0 is a vacuous pre-entry check. The terminal controller replaces the approximate controller from entry onward.'},
{'id':'exercise18d-fixed-controller-fresh-event','approved':True,'reason':'The two probability levels remain distinct. For one fixed controller and fresh iid initial-state validation, the confidence event implies that an accepted test certifies population probability at least mucrit for finite entry plus the pre-entry error bound. This is a high-probability accepted-test implication; no posterior conditional-on-accept or unbudgeted repeated-until-pass confidence is inferred.'},
{'id':'terminal-switch-invariance-and-origin-convergence','approved':True,'reason':'Theorem5 supplies recursive feasibility and constraints on the finite pre-entry segment under Assumptions1–4 and the actual error bound. At the actual entry, Assumption4 terminal invariance and its quadratic decrease with positive definite Q/R give subsequent invariance and convergence under kf. No extra small-eta condition is needed for trajectories whose success event already includes actual entry.'},
{'id':'practical-RPI-convergence-and-Remark6','approved':True,'reason':'Assumptions1–4 alone promise practical RPI convergence, not finite entry/origin convergence. Remark6 small-eta containment is a distinct route, and mere convergence to a subset of closed Xf does not prove finite entry. The proposed edit makes no such inference; the unchanged x_n=1+2^-n counterexample is scoped only to that invalid set-convergence inference.'},
{'id':'no-whole-proof-or-other-source-promotion','approved':True,'reason':'Only the two exact snippets are semantically approved. The old full gap review body/time, Exercise18 generic MPC/Hoeffding formalization gaps, numerical parts a–c, all other source clauses and fixed25 offers remain unchanged.'}]
report={'status':'independent_source53_two_snippet_finite_entry_semantic_and_fresh_full29_parser_review_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; proposal author Applied','proposal':ref(P),'proposal_original_body_and_time':p,'fresh_primary_scope_review':ref(A),'original_scope_review_body_and_time':a,'preserved_original_gap_review':ref(G),'preserved_entire_original_gap_body_and_time':gap,'primary_source':ref(primary),'primary_locations_read':a['primary_direct_locations_actually_read'],'full_current_theorem_validation_context':a['full_current_theorem_and_validation_context'],'full_current_exercise_context':a['full_current_exercise_context'],'decisions':decisions,'semantic_proposal_approved':True,'whole_exercise_approved':False,'generic_Lean_gap_review_changed':False,'source_sha256_before':H(source),'proposed_source_sha256_after':p['proposed_source_sha256_after'],'fresh_full29_parser':{'parser':ref(parser),'inventory':ref(g.OUT/'inventory.json'),'counts':fresh['counts'],'exact_changed_text_keys':changes,'other28_pages_entire_records_equal':True,'all_keys_lines_locators_DOM_and_structure_exact':True,'unique_forward_reverse_and_newlines_exact':True},'current_authoritative_inventory':ref(INV),'selected25_sources_checked':1156,'current_installed25_owner_sha256':owners,'all31_current_assets_sha256':protected,'scope':'TMP-only semantic/proposal/parser review. No working HTML/inventory/ledger, canonical source, selected proof, publication, build or deployment action. Original full gap decisions and times remain exact; no new Lean theorem execution is claimed.'}
OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'observation':ref(OUT),'changed':changes}))
