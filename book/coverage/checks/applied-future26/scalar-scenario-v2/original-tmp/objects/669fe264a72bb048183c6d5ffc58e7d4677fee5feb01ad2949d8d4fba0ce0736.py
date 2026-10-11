from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, shutil, sys

ROOT=Path('/home/oxrexkevin/SafetyBased')
REPORT=Path('/tmp/hertneck-current52-eventual-entry-independent-applied-semantic-review26-v1.json')
PROPOSAL=Path('/tmp/hertneck-finite-entry-clarification-source53-proposal26-v1.json')
SIM=Path('/tmp/hertneck-finite-entry-clarification26-full-parser-v1')
def H(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p): return {'file':str(p),'sha256':H(p)}
for p in [REPORT,PROPOSAL,SIM]: assert not p.exists(),str(p)
invpath=ROOT/'book/coverage/inventory-after-correction52.json'
assert H(invpath)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert H(ROOT/'book/coverage/inventory.json')==H(invpath)
inv=json.loads(invpath.read_text()); units={r['key']:r for r in inv['material_source_units']}
source='SafeLearning/lyapunov-mpc.html'; page=ROOT/source
assert H(page)=='228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'
before=page.read_text(); ex=next(r for r in inv['exercises'] if r['key']=='lyapunov-mpc.html::exercise-18')
oldreview=Path('/tmp/lyapunov-two-core-exercises26-independent-applied-full-gap-review-v1.json')
assert H(oldreview)=='b780754b5d330c88ecf8aacf1e173e85383ecfada980ffe880dca2f00c16e162'
original_review=json.loads(oldreview.read_text())
primary=ROOT/'sources/text/hertneck.txt'; primary_lines=primary.read_text().splitlines()
assert 'Remark 6' in '\n'.join(primary_lines[180:207])
context=[{'source_unit_key':key,'entire_inventory_record':units[key]} for key in
    ['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739',
     'lyapunov-mpc.html::node-753','lyapunov-mpc.html::node-755','lyapunov-mpc.html::node-1387']]
for r in context: assert r['entire_inventory_record']['source_sha256']==H(page)
protocol='A run counts as a success only if it reaches $X_f$ and the error bound held at every step before; in finite computation, fix a maximal horizon and count non-entry by then as failure (conservative).'
assert before.count(protocol)==1
findings=[
 {'id':'assumptions1-to4-give-practical-rpi-convergence',
  'decision':'precise_source_scope_confirmed',
  'reason':'Theorem5 explicitly concludes constraint satisfaction, recursive feasibility and convergence to an RPI set around the origin. It does not state convergence to the origin under Assumptions1–4 alone.',
  'primary_location':'Theorem5, primary text lines186–196; PDF page3'},
 {'id':'remark6-additional-origin-convergence-route',
  'decision':'additional_condition_must_not_be_omitted',
  'reason':'Remark6 makes an additional sufficiently-small-eta qualification before invoking containment of the RPI set in X_f and the terminal controller. The bound of Assumption3 alone must not be treated as this extra condition.',
  'primary_location':'Remark6, primary text lines200–204; PDF page3'},
 {'id':'closed-containment-does-not-prove-finite-entry',
  'decision':'generic_mathematical_implication_rejected',
  'reason':'Set convergence to Z with Z contained in the closed terminal set need not imply finite entry. A strict trapping neighborhood or separate actual finite-entry argument is required for that inference.',
  'explicit_counterexample_scope':'Only the set-convergence implication, not a counterexample purporting to satisfy every nonlinear MPC assumption.',
  'counterexample':'For X_f=[-1,1], Z={1}, and x_n=1+2^(-n), the distance to Z tends to zero and Z is a subset of X_f, but no x_n belongs to X_f. The map x↦1+(x−1)/2 leaves Z invariant.'},
 {'id':'current52-validation-protocol-already-requires-entry',
  'decision':'current_full_context_condition_sufficient',
  'reason':'The retained Validation protocol explicitly counts success only on finite terminal entry plus the pre-entry error bound, with non-entry by a fixed computational horizon classified as failure. On this event, Theorem5 applies up to the first entry and the disturbance-free terminal controller supplies subsequent invariance and convergence from Assumption4. No extra small-eta condition is needed to infer this already-qualified successful-trajectory claim.',
  'exact_current_protocol':protocol},
 {'id':'exercise18d-local-wording-is-ambiguous-without-linked-protocol',
  'decision':'minimal_clarification_recommended_not_blanket_retraction',
  'reason':'Read with the linked full success protocol, the switched-controller conclusion is qualified by actual entry. The answer’s local until-it-enters wording could nevertheless be read as certifying an error-only infinite non-entering trajectory. State entry explicitly in the success event and preserve the confidence and terminal-switch scope.'}]
review={'status':'fresh_current52_hertneck_eventual_entry_semantic_scope_audit_completed',
 'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'current_inventory':ref(invpath),'current_page':ref(page),'entire_current_exercise':ex,
 'material_units':context,'full_current_theorem_and_validation_context':{'first_line':502,'last_line':541,
   'complete_lines':'\n'.join(before.splitlines()[501:541])},
 'full_current_exercise_context':{'first_line':936,'last_line':951,
   'complete_lines':'\n'.join(before.splitlines()[935:951])},
 'primary_source':ref(primary),'primary_direct_locations_actually_read':[
   {'first_line':154,'last_line':215,'complete_lines':'\n'.join(primary_lines[153:215])},
   {'first_line':262,'last_line':310,'complete_lines':'\n'.join(primary_lines[261:310])}],
 'official_primary_verification':{'title':'Learning an Approximate Model Predictive Controller with Guarantees',
   'url':'https://arxiv.org/pdf/1806.04167','version':'arXiv1806.04167v1',
   'locations':'Assumptions1–4, Theorem5 and Remark6 on PDF page3; SectionIV-B finite trajectories eq14 and indicator on page4; Theorem8 on pages4–5',
   'access_scope':'Official arXiv abstract/PDF and PDF pages3–4 opened during this read; the full local primary text hash is bound separately.'},
 'findings':findings,'preserved_original_full_gap_review':ref(oldreview),
 'preserved_entire_original_gap_review_body_and_time':original_review,
 'whole_exercise_approved':False,'missing_generic_lean_bridges_unchanged':True,
 'scope':'Fresh primary-source correctness audit only. It neither converts the original partial exercise to whole proved nor executes a new Lean theorem. Working HTML, inventory, ledgers and fixed25 offers remain untouched.'}
REPORT.write_text(json.dumps(review,indent=2,ensure_ascii=False)+'\n')
replacements=[
 {'source_unit_keys':['lyapunov-mpc.html::node-753','lyapunov-mpc.html::node-755'],
  'before':r'simulate $\pi_{\mathrm{approx}}$ until $X_f$, and set $I(X_i)=1$ if the error bound held along the whole trajectory.',
  'after':r'simulate $\pi_{\mathrm{approx}}$ until its first entry into $X_f$, and set $I(X_i)=1$ only if that entry occurs in finite time and the error bound held at every step before entry.',
  'count':1,'reason':'Make the existing successful-entry validation protocol explicit at the definition of the indicator; no finite-entry inference from closed RPI containment is made.'},
 {'source_unit_keys':['lyapunov-mpc.html::node-1387'],
  'before':r'a fresh initial condition from the <em>same</em> $\Omega$ gives a trajectory with $\|\pi_{\mathrm{approx}}-\pi_{\mathrm{MPC}}\|_\infty\le\eta$ with probability at least $\mu_{\mathrm{crit}}$ until it enters $X_f$;',
  'after':r'with probability at least $\mu_{\mathrm{crit}}$, a fresh initial condition from the <em>same</em> $\Omega$ gives a trajectory that enters $X_f$ in finite time and satisfies $\|\pi_{\mathrm{approx}}-\pi_{\mathrm{MPC}}\|_\infty\le\eta$ at every step before entry;',
  'count':1,'reason':'Keep the same two probability levels while explicitly including finite entry in the certified fresh-trajectory event.'}]
after=before
for r in replacements:
 assert after.count(r['before'])==1 and '\n' not in r['before']+r['after']
 after=after.replace(r['before'],r['after'],1)
reverse=after
for r in reversed(replacements):
 assert reverse.count(r['after'])==1
 reverse=reverse.replace(r['after'],r['before'],1)
assert reverse==before and after.count('\n')==before.count('\n')
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
old_dom,new_dom=Document(before),Document(after)
assert len(old_dom.nodes)==len(new_dom.nodes)
assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(old_dom.nodes,new_dom.nodes))
(SIM/'SafeLearning').mkdir(parents=True)
for p in (ROOT/'SafeLearning').glob('*.html'):
 shutil.copy2(p,SIM/'SafeLearning'/p.name)
(SIM/source).write_text(after)
spec=importlib.util.spec_from_file_location('hertneck_entry_full_parser',ROOT/'book/inventory_claims.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);g.ROOT=SIM;g.OUT=SIM/'book/coverage';g.inventory()
proposed=json.loads((g.OUT/'inventory.json').read_text())
assert proposed['counts']==inv['counts']
changes={}
for section in ['exercises','material_source_units']:
 a={r['key']:r for r in inv[section]};b={r['key']:r for r in proposed[section]}
 assert a.keys()==b.keys()
 changed=[]
 for key,row in a.items():
  new=b[key];assert row.keys()==new.keys()
  assert all(row[f]==new[f] for f in row if f not in {'source_sha256','source_text','text_sha256'}),(key,'structural drift')
  if row['source_text']!=new['source_text']:changed.append(key)
  else: assert row['text_sha256']==new['text_sha256']
  if row['source']!=source: assert row==new
 changes[section]=changed
assert changes=={'exercises':['lyapunov-mpc.html::exercise-18'],
 'material_source_units':['lyapunov-mpc.html::node-753','lyapunov-mpc.html::node-755','lyapunov-mpc.html::node-1387']},changes
assert H(page)==ex['source_sha256'] and page.read_text()==before
assert H(ROOT/'book/coverage/inventory.json')==H(invpath)
selpath=ROOT/'reports/full-coverage/checkpoint-24-selection.json';selection=json.loads(selpath.read_text())
for name,row in selection['proof_files'].items():assert H(ROOT/name)==row['sha256'],name
proposal={'status':'read_only_future26_minimal_hertneck_finite_entry_clarification_pending_independent_semantic_review',
 'prepared_by':'/root/applied_next','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'source':source,'source_sha256_before':H(page),'proposed_source_sha256_after':hashlib.sha256(after.encode()).hexdigest(),
 'current_authoritative_inventory':ref(invpath),'entire_original_exercise':ex,
 'entire_original_material_records':[units[k] for k in changes['material_source_units']],
 'replacements':replacements,'expected_changed_text_keys':changes,
 'new_fresh_primary_semantic_review':ref(REPORT),'preserved_original_gap_review':ref(oldreview),
 'full29_page_parser':{'parser':ref(ROOT/'book/inventory_claims.py'),'proposed_inventory':ref(g.OUT/'inventory.json'),
  'counts_unchanged':True,'all_keys_lines_locators_and_structure_exact':True,'other28_pages_exact':True,
  'unique_forward_and_reverse_bytes_exact':True,'dom_signatures_exact':True,'newlines_exact':True},
 'protected_selected24':{'selection':ref(selpath),'proof_count':len(selection['proof_files']),'all_exact':True},
 'semantic_scope':'Clarify the existing successful finite-entry event, retaining terminal-switch asymptotic convergence after entry and the unchanged validation confidence. Do not claim Assumptions1–4 alone imply finite entry or convergence to the origin; do not add an unnecessary small-eta premise to successful trajectories that actually enter.',
 'working_html_inventory_or_ledger_written':False,'correction_number_assigned':False,
 'whole_current_or_proposed_exercise_approved':False,'actual_preparer':ref(Path(__file__))}
PROPOSAL.write_text(json.dumps(proposal,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'semantic_review':ref(REPORT),'proposal':ref(PROPOSAL),'changed':changes}))
