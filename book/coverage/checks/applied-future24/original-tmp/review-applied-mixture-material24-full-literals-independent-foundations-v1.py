from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, ast

ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/applied-mixture-material24-two-literals-full-source-review-request-v1.json')
OUT=Path('/tmp/applied-mixture-material24-two-literals-independent-foundations-review-v1.json')
H=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
R=lambda p: json.loads(Path(p).read_text())
assert not OUT.exists()
assert H(REQUEST)=='c8306b069f3308d2fdb4cec96c40a512bdb078107bc3931564e6a70e6cd56d8e'
request=R(REQUEST); checked={}
def bind(ref):
    p=Path(ref['file']); assert H(p)==ref['sha256'], str(p)
    checked[str(p)]=H(p); return p
inv=R(bind(request['current_inventory'])); page=bind(request['source_page'])
assert H(ROOT/'book/coverage/inventory.json')==request['current_inventory']['sha256']
rows={u['key']:u for u in inv['material_source_units']}
assert [u['key'] for u in request['material_units']]==['primer-probability.html::node-398','primer-probability.html::node-400']
for unit in request['material_units']:
    assert rows[unit['key']]==unit
    assert hashlib.sha256(unit['source_text'].encode()).hexdigest()==unit['text_sha256']
    assert unit['source_sha256']==H(page)
lines=page.read_text().splitlines(keepends=True)
for context in request['complete_source_contexts']:
    assert ''.join(lines[context['lines_start']-1:context['lines_end']])==context['exact_lines']
assert 'Assume finite second moments for the variance and covariance formulas below.' in page.read_text()
packs=[]; names=[]
for pack_index, pack in enumerate(request['proof_packs']):
    source_path=bind(pack['proof_source']); source=source_path.read_text()
    assert source==pack['entire_source_and_all_bodies']
    assert not re.search(r'\b(sorry|admit|axiom)\b',source)
    namespace=re.search(r'^namespace (\S+)',source,re.M)[1]
    source_names=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
    assert source_names==pack['public_theorem_names'] and len(source_names)==9
    names+=source_names
    histories=[]
    for index, trial in enumerate(pack['original_trial_history'],1):
        record_path=bind(trial['record']); record=R(record_path)
        assert record==trial['entire_original_actual_record']
        snapshot=bind(trial['source_snapshot']); raw=bind(trial['raw_log']); runner=bind(trial['actual_runner'])
        assert record['actual_command']==['lake','env','lean',str(source_path)]
        assert record['actual_workdir']==str(ROOT/'verification/lean')
        passed=index==len(pack['original_trial_history'])
        assert record['actual_exit_code']==(0 if passed else 1)
        assert record['source_unchanged'] and record['source_sha256_before']==record['source_sha256_after']==H(snapshot)
        assert record['source_snapshot']==str(snapshot) and record['source_snapshot_sha256']==H(snapshot)
        assert record['log']==str(raw) and record['log_sha256']==H(raw)
        assert record['actual_runner']==str(runner) and record['actual_runner_sha256']==H(runner)
        assert record['started_at_utc']<record['finished_at_utc'] and record['elapsed_seconds']>0
        assert 'subprocess.run' in runner.read_text() and 'r.returncode' in runner.read_text()
        if passed:
            assert snapshot.read_bytes()==source_path.read_bytes() and 'warning' in raw.read_text() and 'error:' not in raw.read_text()
        else:
            assert 'error' in raw.read_text()
        histories.append(trial)
    assert len(histories)==(3 if pack_index==0 else 5)
    assert pack['actual_standalone']==pack['original_trial_history'][-1]
    packs.append({'proof_source':pack['proof_source'],'entire_source_and_all_bodies':source,
                  'public_theorem_names':source_names,'entire_original_actual_trial_history':histories})
assert len(names)==18
primary_reads=[
    ('Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean',80,144),
    ('Mathlib/MeasureTheory/Measure/WithDensity.lean',110,139),
    ('Mathlib/MeasureTheory/Measure/WithDensity.lean',176,192),
    ('Mathlib/MeasureTheory/Measure/Prod.lean',225,247),
    ('Mathlib/MeasureTheory/Measure/Prod.lean',1110,1122),
    ('Mathlib/MeasureTheory/Measure/Prod.lean',1170,1180),
]
primary=[]
for suffix, first,last in primary_reads:
    p=ROOT/'verification/lean/.lake/packages/mathlib'/suffix
    primary.append({'file':str(p),'sha256':H(p),'lines_start':first,'lines_end':last,
                    'exact_lines':''.join(p.read_text().splitlines(keepends=True)[first-1:last])})
manifest_path=ROOT/'reports/full-coverage/checkpoint-22-manifest.json'; manifest=R(manifest_path)
assert len(manifest['proof_files'])==1113
for n in manifest['proof_files']: assert H(ROOT/n)==manifest['frozen_inputs_sha256'][n],n
guard_source=Path('/tmp/run-foundations-compact-lyapunov-audit24-trial-v1.py')
guards=next(ast.literal_eval(n.value) for n in ast.parse(guard_source.read_text()).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='GUARDS' for t in n.targets))
for n,d in guards.items(): assert H(ROOT/n)==d,n
assert len(guards)==37
reason=('Read all eighteen complete public theorem bodies, the private centered-second-moment expansion, both full mathematical literals and complete surrounding context. '
        'Both finite and countable normalized nonnegative weight families produce an actual probability measure. The two-stage measure is a weighted sum of actual dirac-label/product-component laws, '
        'not an assumed joint distribution: label/component rectangles, label probabilities and the actual second marginal are derived. The finite rectangle at the whole component space gives the label mass, '
        'and the countable theorem states that mass directly. Zero-weight labels need no undefined conditional-probability division. Measurable nonnegative component densities produce the exact weighted density '
        'via genuine withDensity scalar and countable-sum identities. Actual Bochner-integral HasSum gives the weighted mean. In the finite case, component L2 implies mixture L2. In the countable case '
        'the literal inherits line178 finite second moments: mixture L2 and actual component L2 are explicit, and no false implication from componentwise finiteness alone is used. '
        'The actual centered component second moments split into within-component variance plus squared mean displacement; nonnegative domination proves both real variance-series summabilities before their sums '
        'are added. Thus all printed scalar identities and the two-stage construction hold for arbitrary finite/countable labels under their full mathematical hypotheses. No desired mixture mean, variance, density, '
        'or sum convergence is supplied as a conclusion-shaped premise.')
groups=[
 {'component_id':'actual_label_component_joint_and_marginal','lean_declarations':[n for n in names if '.actual_two_stage_' in n],
  'hypotheses':['Finite or countable label type with measurable singleton labels; nonnegative NNReal weights normalized to total1; actual component probability measures.'],
  'per_component_reason':'Actual product/dirac joint, exact rectangles and second marginal; label probabilities follow directly (and are explicitly stated in countable source).','missing_clauses':[]},
 {'component_id':'actual_weighted_density','lean_declarations':[n for n in names if 'of_densities' in n],
  'hypotheses':['Each component law is the actual common-base measure with measurable nonnegative density; component probability normalization for probabilistic interpretation.'],
  'per_component_reason':'Equality of actual measures with the weighted density is derived by withDensity_smul and withDensity_tsum.','missing_clauses':[]},
 {'component_id':'actual_mean_and_variance_series','lean_declarations':[n for n in names if any(s in n for s in ['_integral','_mean','_variance','second_moment'])],
  'hypotheses':['Actual component probability measures and component finite second moments; finite weights normalized; countable case additionally has finite second moment under the actual mixture as required by page178.'],
  'per_component_reason':'Actual expectation and variance identities, with genuine HasSum and both variance series summability; mixture L2 is proved for finite labels.','missing_clauses':[]},
]
units=[{'source_unit_key':u['key'],'entire_inventory_record':u,'material_status':'proved','whole_unit_approved':True,
        'lean_declarations':names,'hypotheses':request['intended_hypotheses'],'components':groups,
        'per_unit_reason':reason,'missing_clauses':[]}for u in request['material_units']]
report={'status':'passed_independent_full_two_literal_finite_and_countable_mixture_source_review_future24_tmp_only',
        'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
        'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),
        'original_request':{'file':str(REQUEST),'sha256':H(REQUEST)},'entire_original_request_body_and_time':request,
        'material_units':units,'whole_mathematical_units_approved':2,'public_theorem_names':names,'proof_packs':packs,
        'direct_primary_reads':primary,'checked_artifact_sha256':checked,
        'all1113_selected22_source_hashes_exact':True,'all37_current23_installed_owner_and_source_guards_exact':guards,
        'scope_limits':['Scalar finite/countable mixtures; no uncountable-index mixture claim.',
                        'Countable mixture finite second moment is an honest overall assumption, not inferred from only componentwise finiteness.',
                        'Zero-weight labels are handled through the actual two-stage joint; no positive-event conditional law is claimed on a zero-probability label.',
                        'Node401 Gaussian-tail values and vector ensemble covariance remain separately pending; node399 is not remapped.',
                        'Both sources have genuine TMP standalone passes only, with real warning logs and all eight original failed/passed trials retained; no canonical/named execution, current23 amendment or whole exercise promotion.'],
        'errors':[],'coverage_complete':False}
with OUT.open('x')as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':str(OUT),'sha256':H(OUT),'whole_units':2,'public_theorem_count':18}))
