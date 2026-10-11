from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,sys,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/mpc-primary-row-definitions-source60-proposal28-v1');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert not OUT.exists()
basepacket=Path('/tmp/root-mpc-explicit-adopted-domain-source56-proposal-v2/root-mpc-explicit-adopted-domain-source56-proposal-v2.json');bp=json.loads(basepacket.read_bytes());base=Path(bp['proposed_source']['file']);assert sha(base)==bp['proposed_source']['sha256']=='cfd10ffdd5c689e0254bc022d330bbd5046a7e64427e40060b7a54709caeb68b'
baseinvpath=Path(bp['proposed_full29_inventory']['file']);assert sha(baseinvpath)==bp['proposed_full29_inventory']['sha256'];baseinv=json.loads(baseinvpath.read_bytes())
currentinvpath=ROOT/'book/coverage/inventory.json';assert sha(currentinvpath)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf';currentinv=json.loads(currentinvpath.read_bytes());currenthtml=ROOT/'SafeLearning/lyapunov-mpc.html';assert sha(currenthtml)==bp['source']['sha256']
parser=ROOT/'book/inventory_claims.py';assert sha(parser)=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
primary=ROOT/'sources/text/hertneck.txt';text=base.read_text()
old1=r'tightened constraints $\bar X_k=(1-\epsilon_k)X$, $\bar U_k=(1-\epsilon_k)U_t$, $U_t=U\ominus\{\|d\|_\infty\le\eta\}$'
new1=r'tightened constraints $\bar X_k=\{x:Hx\le(1-\epsilon_k)\mathbf 1\}$ and $\bar U_k=\{u:L_tu\le(1-\epsilon_k)\mathbf 1\}$, with $X=\{x:Hx\le\mathbf 1\}$ and $U_t=\{u:L_tu\le\mathbf 1\}=U\ominus\{\|d\|_\infty\le\eta\}$'
old2=r'and $\epsilon_k=\epsilon\sum_{j=0}^{k-1}\sqrt\rho^{\,j}$.<br>'
new2=old2[:-4]+r' Define the tightened sets by the row inequalities in eq. 12: $\bar X_k=\{x:Hx\le(1-\epsilon_k)\mathbf 1\}$ and $\bar U_k=\{u:L_tu\le(1-\epsilon_k)\mathbf 1\}$. For $1-\epsilon_k\gt0$, these equal $(1-\epsilon_k)X$ and $(1-\epsilon_k)U_t$; scalar-multiplication notation is used here only for positive factors. The row definitions also specify zero or negative right-hand sides, without assuming $\epsilon_k\le1$.<br>'
replacements=[{'before':old1,'after':new1},{'before':old2,'after':new2}]
proposed=text
for r in replacements:assert proposed.count(r['before'])==1 and r['after'] not in proposed;proposed=proposed.replace(r['before'],r['after'],1)
reverse=proposed
for r in reversed(replacements):assert reverse.count(r['after'])==1;reverse=reverse.replace(r['after'],r['before'],1)
assert reverse==text and proposed.count('\n')==text.count('\n')
# Every exact adopted-domain clause is retained; the new edit is not a new successor-domain assumption.
for exact in [r'\qquad x^+\in X,', 'Here we adopt the typed-domain reading of Assumption 1:', 'The paper does not display this membership as a separate clause;']:
 assert text.count(exact)==proposed.count(exact)==1
OUT.mkdir();candidate=OUT/'lyapunov-mpc-source60-proposed-v1.html';candidate.write_bytes(proposed.encode())
sys.path.insert(0,str(ROOT/'book'))
with tempfile.TemporaryDirectory(prefix='source60-author-isolated-full29-') as td:
 isolate=Path(td);(isolate/'SafeLearning').mkdir();pages=sorted((ROOT/'SafeLearning').glob('*.html'));assert len(pages)==29
 for p in pages:(isolate/'SafeLearning'/p.name).write_bytes(candidate.read_bytes() if p.name=='lyapunov-mpc.html' else p.read_bytes())
 spec=importlib.util.spec_from_file_location('source60_author_full29_parser',parser);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.ROOT=isolate;m.OUT=isolate/'book/coverage';assert m.ROOT!=ROOT and m.OUT!=ROOT/'book/coverage' and m.OUT.is_relative_to(m.ROOT)
 m.inventory();freshbytes=(m.OUT/'inventory.json').read_bytes()
fresh=json.loads(freshbytes);freshpath=OUT/'inventory-proposed-source60-v1.json';freshpath.write_bytes(freshbytes)
assert fresh['counts']==baseinv['counts']==currentinv['counts'] and len(fresh['source_sha256'])==29
assert fresh['source_sha256']=={**baseinv['source_sha256'],'SafeLearning/lyapunov-mpc.html':sha(candidate)}
changes={};records={}
for field in ['exercises','material_source_units']:
 aa={x['key']:x for x in baseinv[field]};bb={x['key']:x for x in fresh[field]};cc={x['key']:x for x in currentinv[field]};assert aa.keys()==bb.keys();changes[field]=[]
 for k,a0 in aa.items():
  a=copy.deepcopy(a0);b=copy.deepcopy(bb[k])
  if a['source']=='SafeLearning/lyapunov-mpc.html':assert b['source_sha256']==sha(candidate);a.pop('source_sha256');b.pop('source_sha256')
  if a!=b:
   assert {n:v for n,v in a.items() if n not in ['source_text','text_sha256']}=={n:v for n,v in b.items() if n not in ['source_text','text_sha256']};changes[field].append(k)
   records[k]={'entire_current55_inventory_record':cc[k],'entire_virtual_source56_inventory_record':a0,'entire_proposed_source60_inventory_record':bb[k]}
assert changes=={'exercises':[],'material_source_units':['lyapunov-mpc.html::node-735','lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739']}
owner=ROOT/'book/coverage/core.json';od=json.loads(owner.read_bytes());oldclaims=[x for x in od['material_claims'] if any(k in x.get('source_unit_keys',[]) for k in records)];oldex=next(x for x in od['exercises'] if x['inventory_key']=='lyapunov-mpc.html::exercise-18')
closed=[basepacket,base,baseinvpath,currentinvpath,currenthtml,parser,primary,owner,candidate,freshpath]
packet={'status':'tmp_only_source60_primary_row_definition_proposal_requires_independent_full_primary_and_parser_review','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'Applied MPC proof branch','prospective_source_batch':60,'based_on_virtual_source56_not_actual_applied':True,'source_batch_order':'After Root planned56-59; lyapunov page edits apply on exact Source56 candidate while intervening other-page edits are independent. Current live Source55 is unchanged.','current_inventory':ref(currentinvpath),'current_source':ref(currenthtml),'base_source56_proposal':ref(basepacket),'base_source56_candidate':ref(base),'base_source56_inventory':ref(baseinvpath),'proposed_source':ref(candidate),'proposed_full29_inventory':ref(freshpath),'parser':ref(parser),'raw_replacements':replacements,'full_current55_context_lines500_to516':''.join(currenthtml.read_text().splitlines(keepends=True)[499:516]),'full_virtual_source56_context_lines500_to516':''.join(text.splitlines(keepends=True)[499:516]),'full_proposed_source60_context_lines500_to516':''.join(proposed.splitlines(keepends=True)[499:516]),'full_primary_reference':ref(primary),'primary_clause_locations':{'tightening_rows':'sources/text/hertneck.txt lines223-234, eq12','input_erosion':'same full section lines210-217'},'entire_changed_records':records,'entire_original_current55_claim_rows':oldclaims,'entire_original_current55_exercise18':oldex,'actual_fresh_parser_changed_text_keys':changes,'both_parser_ROOT_and_OUT_isolated':True,'exact_reverse_to_entire_virtual_source56_html':True,'all_source56_adopted_domain_clauses_preserved_exact':True,'all556_exercise_and12774_material_shapes_preserved':True,'no_epsilon_N_sign_inferred_from_scaled_origin_membership':True,'negative_factor_counterexample':{'state_dimension':1,'X':'[-1,1] defined by H=[1;-1] rows <=1','epsilon':2,'scalar_factor':-1,'scalar_multiple_set':'[-1,1], contains0','row_inequality_set':'x<=-1 and -x<=-1, hence empty','consequence':'Scalar-set equality cannot be asserted for negative factor. The proposed row definitions preserve the primary actual tightened inequalities for every factor.'},'positive_factor_equivalence_argument':'For a>0 and each linear H row, x=a*y with H*y<=1 iff H*x<=a; the converse takes y=a^-1*x. Same for Lt. This does not cover negative-factor scaling.','scope':'Only explicit primary eq12 row definitions and honest positive-factor scaling shorthand are restored. No new Theorem5 hypothesis, epsilon<=1 restriction, full shifted feasibility conclusion, whole18 promotion or live/source/owner/proof edit is claimed.','closed_evidence_sha256':{str(p):sha(p) for p in closed}}
p=OUT/'mpc-primary-row-definitions-source60-proposal28-v1.json'
with p.open('x') as f:f.write(json.dumps(packet,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'proposal':ref(p),'changed':changes,'proposed_source':ref(candidate)}))
