from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,sys,importlib.util
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/applied-lyapunov-scenario-validation-precision-proposal23-v1.json')
SIM=Path('/tmp/applied-lyapunov-scenario-validation-precision-simulation23-v1')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':H(p)}
invfile=ROOT/'book/coverage/inventory-after-correction48.json'
assert H(invfile)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inventory=json.loads(invfile.read_text());units={r['key']:r for r in inventory['material_source_units']}
source='SafeLearning/lyapunov-mpc.html'
original=(ROOT/source).read_text();assert H(ROOT/source)=='ad1afbe557c64272f1dd92abc452280cc661226de972ee57f4985273eec2b8d9'
old={i:next(l.strip() for l in original.splitlines() if l.strip().startswith('<p'+(' style="margin-top:0;"' if i==1397 else '')+'><strong>('+c+')</strong>')) for i,c in [(1397,'a'),(1401,'c'),(1403,'d')]}
# Use exact full paragraphs scoped by the unique exercise-specific text, because (a)/(c)/(d) repeat elsewhere.
old[1397]=next(l.strip() for l in original.splitlines() if '<strong>(a)</strong> Only the term $i=0$ remains:' in l)
old[1401]=next(l.strip() for l in original.splitlines() if '<strong>(c)</strong> Corrected: $\\ln100/' in l)
old[1403]=next(l.strip() for l in original.splitlines() if '<strong>(d)</strong> With probability at least $0.99$ over the validation samples' in l)
new={
1397:r'''<p style="margin-top:0;"><strong>(a)</strong> Only the term $i=0$ remains: $(1-\epsilon)^N\le\beta\iff N\ge\ln(1/\beta)/(-\ln(1-\epsilon))$. For the given values, $\ln1000/\ln(20/19)\approx134.7$ (with $\ln1000\approx6.9078$ and $\ln(20/19)\approx0.051293$), so $N=135$. Under the convex scenario-program assumptions, at most one sample can support the one-variable solution, and a violation above $\epsilon$ needs all $N$ samples to miss an $\epsilon$-mass region.</p>''',
1401:r'''<p><strong>(c)</strong> Corrected: $\ln100/(2\cdot0.02^2)\approx5756.5$, so $5757$. Misprinted: $\ln100/(2\cdot0.02)\approx115.1$, so $116$, for which $e^{-2\cdot116\cdot0.02^2}=e^{-0.0928}\approx0.911$. Hoeffding supplies the lower confidence bound $1-e^{-0.0928}\approx9\%$, rather than $99\%$ (a lower bound from this inequality, not the actual confidence of the procedure).</p>''',
1403:r'''<p><strong>(d)</strong> For a fixed $K^\ast$ and one fresh independent batch of at least $5757$ validation samples from the normalized $c=0.95$ credible posterior, with probability at least $0.99$ over that batch, acceptance (empirical stability at least $0.95$) implies that the full posterior probability that $K^\ast$ stabilises the true linearisation is at least $0.95-0.05-0.02=0.88$: a Bayesian statement, as good as the GP posterior. This is a fixed-batch implication; repeated validation attempts need a separate failure budget.</p>'''}
reasons={1397:'Preserve the exact logarithmic threshold and genuine least sample135; qualify each rounded logarithm/ratio as an approximation, and state the support-count clause under the convex scenario assumptions.',1401:'Preserve the exact corrected and misprinted rules and sample counts; qualify finite decimals as approximations and keep the exact exponential in the Hoeffding lower-confidence bound.',1403:'Express the actual one-fresh-independent-batch accepted-test implication, under the normalized credible posterior model, without a conditional-on-accept or unbudgeted repeated-testing guarantee.'}
replacements=[{'source_unit_key':f'lyapunov-mpc.html::node-{i}','before':old[i],'after':new[i],'count':1,'reason':reasons[i]} for i in [1397,1401,1403]]
after=original
for r in replacements:
 assert after.count(r['before'])==1 and '\n' not in r['before'] and '\n' not in r['after']
 after=after.replace(r['before'],r['after'],1)
reverse=after
for r in reversed(replacements):
 assert reverse.count(r['after'])==1
 reverse=reverse.replace(r['after'],r['before'],1)
assert reverse==original and after.count('\n')==original.count('\n')
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
old_dom,new_dom=Document(original),Document(after)
assert len(old_dom.nodes)==len(new_dom.nodes)
assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(old_dom.nodes,new_dom.nodes))
assert not SIM.exists();(SIM/'SafeLearning').mkdir(parents=True)
# Immutable checkpoint22 HTML is source48. Use it instead of racing Root's independent source49 apply.
frozen=ROOT/'reports/full-coverage/checkpoint-22'
for p in (frozen/'SafeLearning').glob('*.html'):
 if str(Path('SafeLearning')/p.name) in inventory['source_sha256']:
  assert H(p)==inventory['source_sha256'][str(Path('SafeLearning')/p.name)]
 shutil.copy2(p,SIM/'SafeLearning'/p.name)
(SIM/source).write_text(after)
spec=importlib.util.spec_from_file_location('lyapunov_precision_full_inventory',ROOT/'book/inventory_claims.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);g.ROOT=SIM;g.OUT=SIM/'book/coverage';g.inventory()
proposed=json.loads((g.OUT/'inventory.json').read_text());assert proposed['counts']==inventory['counts']
changes={}
for sec in ['exercises','material_source_units']:
 oldrows={r['key']:r for r in inventory[sec]};newrows={r['key']:r for r in proposed[sec]};assert oldrows.keys()==newrows.keys();changed=[]
 for key,a in oldrows.items():
  b=newrows[key];assert a.keys()==b.keys()
  assert all(a[f]==b[f] for f in a if f not in {'source_sha256','source_text','text_sha256'}),(key,'structural drift')
  if a['source_text']!=b['source_text']:changed.append(key)
  else:assert a['text_sha256']==b['text_sha256']
  if a['source']!=source:assert a==b
 changes[sec]=changed
assert changes=={'exercises':['lyapunov-mpc.html::exercise-19'],'material_source_units':[f'lyapunov-mpc.html::node-{i}' for i in [1397,1401,1403]]},changes
ex=next(r for r in inventory['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')
packpaths=[
'/tmp/applied-lyapunov-scenario-validation23-two-source-readiness-v1.json',
'/tmp/lyapunov-scenario-validation23-independent-foundations-components-review-v2.json',
'/tmp/applied-lyapunov-scenario-support23-independent-review-request-v1.json',
'/tmp/lyapunov-scenario-support23-independent-foundations-components-review-v1.json',
'/tmp/applied-lyapunov-scenario-convex-support23-independent-review-request-v1.json',
'/tmp/lyapunov-scenario-convex-support23-independent-foundations-components-review-v1.json']
proofs=[]
for sourcefile,rec in [
('/tmp/CompleteLyapunovScenarioNumbers23.lean','/tmp/applied-lyapunov-scenario-numbers23-trial5.json'),
('/tmp/CompleteLyapunovValidationBridge23.lean','/tmp/applied-lyapunov-validation-bridge23-trial2.json'),
('/tmp/CompleteLyapunovScenarioSupport23.lean','/tmp/applied-lyapunov-scenario-support23-trial2.json'),
('/tmp/CompleteLyapunovScenarioConvexSupport23.lean','/tmp/applied-lyapunov-scenario-convex-support23-trial1.json')]:
 rr=json.loads(Path(rec).read_text());assert rr['actual_exit_code']==0
 assert H(sourcefile)==rr['source_sha256_after']==H(rr['source_file'])
 assert H(rr['raw_log_file'])==rr['raw_log_sha256']
 proofs.append({'proof_source':ref(sourcefile),'actual_standalone_record':ref(rec),'raw_log':ref(rr['raw_log_file']),'original_source_snapshot':ref(rr['source_file']),'original_runner':ref(rr['runner_file']),'scope':'Actual immutable TMP standalone0; no named build, coverage selection or fresh aggregate claim.'})
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
assert sum(sum(d['kind'] in ['theorem','lemma'] for d in declarations(Path(p['proof_source']['file']).read_text())) for p in proofs)==37
manifestpath=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';manifest=json.loads(manifestpath.read_text())
for name,row in manifest['proof_files'].items():assert H(ROOT/name)==row['sha256'],name
assert H(ROOT/source)==ex['source_sha256'] and (ROOT/source).read_text()==original
primary=[{'file':p,'sha256':H(ROOT/p),'scope':scope} for p,scope in [
('sources/text/cg2008.txt','Assumption1, Proposition2.2, Theorem2.4 and Table2.2. Generic convex scenario optimizer/risk correspondence remains primary-attributed, not established by numerical evaluation.'),
('sources/text/2105.07668.txt','Section3.2 fixed-controller validation and its one-sided Hoeffding proof, under normalized credible-posterior sampling; Algorithm1 repeated-until-pass is not assigned an unbudgeted fixed-batch confidence guarantee.')]]
report={'status':'read_only_future23_lyapunov_scenario_precision_proposal_pending_independent_semantic_review','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'prepared_by':'/root/applied_next','source':source,'source_sha256_before':H(ROOT/source),'proposed_source_sha256_after':hashlib.sha256(after.encode()).hexdigest(),'original_inventory':ref(invfile),'entire_original_exercise':ex,'replacements':replacements,'expected_changed_text_keys':changes,'working_html_inventory_or_ledgers_written':False,'correction_number_assigned':False,'full_corrected_whole_exercise_approved':False,'exact_readonly_simulation':{'baseline':'Immutable checkpoint22 source48 HTML, preserving the source49 Root apply as an independent change.','full29_page_inventory_parser_completed':True,'counts_unchanged':True,'all_keys_lines_attributes_locators_and_structural_fields_preserved':True,'unique_forward_and_reverse_bytes_exact':True,'dom_node_signature_exact':True,'newlines_unchanged':True,'proposed_inventory':ref(g.OUT/'inventory.json')},'prior_component_packets_and_independent_peers':[ref(p) for p in packpaths],'proof_rows':proofs,'public_theorem_count':37,'primary_context_actually_read':primary,'precise_changed_math_scope':{'answer_a':'Genuine log iff and exact all-natural-number cutoff135 with independent certified source approximations. At-most-one scalar convex support theorem retains an attained feasible least optimizer and actual strict-removal support definition; generic optimized scenario violation is not inferred from fixed-threshold all-miss arithmetic.','answer_c':'True rational exponents and logarithmic rules yield ceil5757/116. Hoeffding lower confidence remains 1-exp(-.0928), approximately9%, below9%; .911 is a rounded failure bound rather than an exact exponential.','answer_d':'One fixed controller, one fresh independent batch n≥5757 from the normalized genuine .95 credible posterior. Probability≥.99 of (empirical stability≥.95 implies full posterior stability≥.88). This does not assert a .99 probability conditional on acceptance, a repeated-until-pass guarantee, a constructed/calibrated GP derivative posterior or nonlinear closed-loop stability.'},'retained_missing_clauses':['No general Campi–Garatti optimized scenario-risk probability theorem or general convex random missed-region correspondence is proved by these37 statements.','The posterior model/common independent test law and the GP/true-linearization interpretation are explicit assumptions, not constructed by the new numerical component pack.','No corrected whole-exercise decision, selection, aggregate23 audit or publication is inferred from this proposal.'],'protected_selected22_sources':{'manifest':ref(manifestpath),'proof_count':len(manifest['proof_files']),'all_exact':True},'actual_preparer':ref(Path(__file__))}
assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':'read_only_proposal_prepared','proposal':str(OUT),'sha256':H(OUT),'changed':changes,'theorem_count':37}))
