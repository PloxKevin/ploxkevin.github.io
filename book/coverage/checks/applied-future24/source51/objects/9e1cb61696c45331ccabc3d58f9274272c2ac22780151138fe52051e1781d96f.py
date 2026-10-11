from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,ast
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();R=lambda p:json.loads(Path(p).read_text())
REQUEST=Path('/tmp/applied-mixture-covariance-material24-ensemble-component-full-source-review-request-v1.json')
OUT=Path('/tmp/applied-mixture-covariance-material24-ensemble-independent-foundations-component-review-v2.json')
assert not OUT.exists();assert H(REQUEST)=='47071c349f67c8ba4e801c4a1b54233029e5ed64f76fc5cf57d9633c049609b7'
r=R(REQUEST);checked={}
def bind(ref):
 p=Path(ref['file']);assert H(p)==ref['sha256'],str(p);checked[str(p)]=H(p);return p
inv=R(bind(r['current_inventory']));assert H(ROOT/'book/coverage/inventory.json')==r['current_inventory']['sha256']
page=bind(r['source_page']);unit=next(u for u in inv['material_source_units']if u['key']==r['material_unit']['key']);assert unit==r['material_unit']
assert unit['source_sha256']==H(page)and hashlib.sha256(unit['source_text'].encode()).hexdigest()==unit['text_sha256']
assert r['exact_component_literal']in unit['source_text']
for c in r['complete_source_contexts']:assert ''.join(page.read_text().splitlines(keepends=True)[c['lines_start']-1:c['lines_end']])==c['exact_lines']
pack=r['proof_pack'];source=bind(pack['proof_source']);text=source.read_text();assert text==pack['entire_source_and_all_bodies']
assert not re.search(r'\b(sorry|admit|axiom)\b',text)
names=['SafeLearning.CompleteAppliedMixtureCovarianceMaterial24.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
assert names==pack['public_theorem_names']and len(names)==4
histories=[]
for i,t in enumerate(pack['original_trial_history'],1):
 p=bind(t['record']);record=R(p);assert record==t['entire_original_actual_record']
 snapshot=bind(t['source_snapshot']);log=bind(t['raw_log']);runner=bind(t['actual_runner'])
 assert record['actual_command']==['lake','env','lean',str(source)]and record['actual_workdir']==str(ROOT/'verification/lean')
 assert record['actual_exit_code']==(0 if i==3 else 1)and record['source_unchanged']
 assert record['source_sha256_before']==record['source_sha256_after']==H(snapshot)==record['source_snapshot_sha256']
 assert record['source_snapshot']==str(snapshot)and record['log']==str(log)and record['log_sha256']==H(log)
 assert record['actual_runner']==str(runner)and record['actual_runner_sha256']==H(runner)
 assert record['started_at_utc']<record['finished_at_utc']and record['elapsed_seconds']>0
 assert 'subprocess.run'in runner.read_text()and'returncode'in runner.read_text()
 if i==3:assert snapshot.read_bytes()==source.read_bytes()and len(re.findall(r'^.*:[0-9]+:[0-9]+: warning:',log.read_text(),re.M))==1 and'error:'not in log.read_text()
 else:assert'error'in log.read_text()
 histories.append(t)
assert len(histories)==3 and pack['actual_standalone']==histories[-1]
selectionp=ROOT/'reports/full-coverage/checkpoint-23-selection.json';selection=R(selectionp);assert len(selection['proof_files'])==1131
for n,row in selection['proof_files'].items():assert H(ROOT/n)==row['sha256'],n
guard_source=Path('/tmp/run-foundations-compact-lyapunov-audit24-trial-v1.py')
guards=next(ast.literal_eval(n.value)for n in ast.parse(guard_source.read_text()).body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='GUARDS'for t in n.targets))
for n,d in guards.items():assert H(ROOT/n)==d,n
primary=[]
for suffix,a,b in [('Mathlib/Probability/Moments/Covariance.lean',39,69),('Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean',113,145)]:
 p=ROOT/'verification/lean/.lake/packages/mathlib'/suffix
 primary.append({'file':str(p),'sha256':H(p),'lines_start':a,'lines_end':b,'exact_lines':''.join(p.read_text().splitlines(keepends=True)[a-1:b])})
reason=('Read all four full public bodies and every private probability/integral/L2/centered-product proof, the whole node401 and both complete contexts including line178 finite-second-moment assumptions and Section1 hatSigma. '
        'The scalar centered cross-product expansion uses actual integrable products of L2 component variables and actual Bochner moments. Actual finite weighted-measure integration derives the within/between covariance equality. '
        'The component-means term is the actual covariance under a genuine dirac-label law; its expectation is the weighted mean and its centered product is the outer-product estimate entry. '
        'Finite coordinate extensionality proves the entire covariance matrix equality, and a nonempty finite ensemble normalizes actual weights1/card before extracting the average component covariance. '
        'Taking actual Gaussian member laws with the inherited finite coordinate second moments is a valid specialization; Gaussianity is unnecessary for this covariance identity. '
        'No desired decomposition, covariance-of-means identity or equal-weight normalization is assumed. Aleatoric/epistemic are labels for these two precise mathematical terms, not calibrated uncertainty or posterior guarantees. '
        'The retained unused-hw warning is honest: the algebraic centered covariance equality also holds beyond normalized measures, while the private actual probability/L2 constructions and normalized equal-weight theorem justify the source probability interpretation.')
component={'component_id':'actual_equal_weight_gaussian_ensemble_covariance','exact_component_literal':r['exact_component_literal'],'lean_declarations':names,
 'hypotheses':r['intended_hypotheses'],'per_component_reason':reason,'missing_clauses':[],'remaining_gaps':[]}
report={'status':'passed_independent_equal_weight_ensemble_covariance_component_review_with_whole_node401_pending_future24_tmp_only',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),
 'original_request':{'file':str(REQUEST),'sha256':H(REQUEST)},'entire_original_request_body_and_time':r,
 'proof_source':pack['proof_source'],'entire_new_source_and_all_four_public_and_private_bodies':text,'public_theorem_names':names,
 'material_units':[{'source_unit_key':unit['key'],'entire_inventory_record':unit,'material_status':'pending','whole_unit_approved':False,
                   'components':[component],'lean_declarations':names,'hypotheses':r['intended_hypotheses'],'per_unit_reason':reason,
                   'missing_clauses':r['retained_missing_neighbor_clauses']}],
 'precise_component_groups_approved':1,'whole_mathematical_units_approved':0,'direct_primary_reads':primary,'original_actual_trial_history':histories,
 'checked_artifact_sha256':checked,'all1131_current23_selected_source_hashes_exact':True,'all37_current23_owner_and_source_guards_exact':guards,
 'scope_limits':['One final ensemble covariance clause only; all scalar Gaussian variance/tail numeric clauses remain pending.',
                'Section1 outer-product definition matches, but separate rank/invertibility/fusion claims are not approved here.',
                'Nonempty finite ensemble/finite-dimensional vector/actual component probability measures and actual coordinate L2 moments; no calibration or Bayesian construction claim.',
                'Original actual trial3 TMP standalone0 with one actual warning only; both failed histories exact. No fresh compiler, named/canonical build, whole401 or current23 amendment.'],
 'original_first_checker_failure':{'checker':{'file':str(Path('/tmp/applied-mixture-covariance-material24-ensemble-independent-foundations-component-review-v1.py')),'sha256':H('/tmp/applied-mixture-covariance-material24-ensemble-independent-foundations-component-review-v1.py')},'actual_execution':{'file':'/tmp/applied-mixture-covariance-material24-independent-foundations-actual-v1.json','sha256':H('/tmp/applied-mixture-covariance-material24-independent-foundations-actual-v1.json')},'raw_log':{'file':'/tmp/applied-mixture-covariance-material24-independent-foundations-actual-v1.log','sha256':H('/tmp/applied-mixture-covariance-material24-independent-foundations-actual-v1.log')},'reason':'The first reader counted warning: in both the diagnostic and its ordinary Hint text; corrected reader matches only actual diagnostic lines. Original source, request, semantic decision and compiler records unchanged.'},'errors':[],'coverage_complete':False}
with OUT.open('x')as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'report':str(OUT),'sha256':H(OUT),'whole_units':0,'groups':1,'public_bodies':4}))
