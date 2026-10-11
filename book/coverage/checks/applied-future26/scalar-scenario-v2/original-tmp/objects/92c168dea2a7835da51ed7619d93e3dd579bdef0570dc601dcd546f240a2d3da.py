"""Independent full five-body precise component review; TMP only."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(n):return {'file':str(n),'sha256':H(path(n))}
request_name='/tmp/lyapunov-convex-interval-risk26-five-body-component-review-request-v1.json'
assert H(Path(request_name))=='09b55b815c1cac2536c1e793e84c0ef724515b817e4e14ac3d4b574545a07dfe'
q=json.loads(Path(request_name).read_text())
source=path(q['proof_source']['file'])
assert H(source)==q['proof_source']['sha256']=='464735294fc223bed0b0ae5a23ff2895410a40a49246db9072111649cd7a385c'
text=source.read_text()
assert text==q['complete_source_body'] and not re.search(r'\b(sorry|admit|axiom)\b',text)
names=re.findall(r'^theorem (\w+)',text,re.M)
assert names==q['public_theorems'] and len(names)==5
for n,h in q['source_and_history_sha256'].items():assert H(path(n))==h,n
records=[]
for i in range(1,5):
    record_name='/tmp/lyapunov-convex-interval-risk26-trial'+str(i)+'.json'
    d=json.loads(Path(record_name).read_text())
    assert type(d['actual_exit_code'])is int and d['actual_exit_code']==(0 if i==4 else 1)
    assert d['actual_command']==['lake','env','lean',str(source)]
    assert d['actual_workdir']==str(ROOT/'verification/lean')
    assert d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']
    assert H(Path(d['source_snapshot']))==d['source_snapshot_sha256']
    assert H(Path(d['log']))==d['raw_log_sha256']
    if i==4:
        assert d['source_sha256_after']==H(source)
        assert len(re.findall(r'^/tmp/\S+:\d+:\d+: warning:',Path(d['log']).read_text(),re.M))==3
        assert 'error:'not in Path(d['log']).read_text()
    records.append({'reference':ref(record_name),'entire_original_record_and_time':d,'original_runner':ref('/tmp/run-lyapunov-convex-interval-risk26-trial'+str(i)+'.py')})
inventory=json.loads(path(q['current_inventory']['file']).read_text())
assert H(path(q['current_inventory']['file']))==q['current_inventory']['sha256']
assert H(ROOT/'book/coverage/inventory.json')==q['current_inventory']['sha256']
assert next(e for e in inventory['exercises']if e['key']==q['entire_current_exercise']['key'])==q['entire_current_exercise']
for u in q['current_material_units']:
    assert next(x for x in inventory['material_source_units']if x['key']==u['source_unit_key'])==u['entire_inventory_record']
    assert H(ROOT/u['entire_inventory_record']['source'])==u['entire_inventory_record']['source_sha256']
cg_name='sources/text/cg2008.txt'
assert H(ROOT/cg_name)==q['primary_source_scope']['sha256']=='8de2dbe7a0861782901460ed89237462571b302f9710a16e30a4800992e23f93'
assert '\n'.join((ROOT/cg_name).read_text().splitlines()[149:284])==q['primary_source_scope']['exact_read_context']
prior_name='/tmp/lyapunov-two-core-exercises26-independent-applied-full-gap-review-v1.json'
prior=json.loads(Path(prior_name).read_text())
assert prior==q['preserved_full_gap_review_entire_body_and_time']
dependency_name='verification/lean/SafeLearning/CompleteLyapunovScenarioContinuousRisk23.lean'
dependency_text=(ROOT/dependency_name).read_text()
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-24-manifest.json').read_text())
assert H(ROOT/dependency_name)==manifest['proof_files'][dependency_name]['sha256']
assert len(manifest['proof_files'])==1144
for n,p in manifest['proof_files'].items():assert H(ROOT/n)==p['sha256']
assert not re.search(r'\b(sorry|admit|axiom)\b',dependency_text)
primary=[]
for n,a,b in [('verification/lean/.lake/packages/mathlib/Mathlib/Probability/CDF.lean',48,93),('verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean',687,718)]:
    p=ROOT/n
    primary.append({'file':n,'sha256':H(p),'start_line':a,'end_line':b,'exact_source_text_read':'\n'.join(p.read_text().splitlines()[a-1:b])})
N='SafeLearning.CompleteLyapunovConvexIntervalRisk26.'
reasons=[
    'For an arbitrary real probability law including atoms, the sublevel event F(x)<t is measurable. Every compact subset has a greatest point x and is contained in (-infinity,x]; its mass is bounded by F(x)<t. Inner regularity then bounds the whole event by t. This is a genuine CDF domination theorem, with no assumed probability integral transform or nonatomic law.',
    'The sampled optimizer is constructed from actual attained one-constraint least minimizers. The maximum equals one sampled minimizer, so it belongs to the domain. A common feasible witness is above all singleton optima; convex order-connected intervals make the maximum satisfy every sampled constraint. The same augmented feasible witness proves a fresh constraint fails precisely when its own singleton minimum exceeds the sampled maximum. Measurability of the singleton map gives the actual pushforward law and the fresh violation is its actual CDF tail, rather than a stipulated risk distribution.',
    'Independent common-law uncertainty remains independent through the measurable singleton optimizer and CDF maps. The bad optimized-risk event is exactly the intersection of all strict CDF-coordinate events below 1-epsilon. Their actual probabilities are bounded by 1-epsilon by the arbitrary-law CDF theorem, and independence gives the product bound (1-epsilon)^N. This covers atomic laws and genuinely random optimized regions, within the explicitly least-coordinate optimization model.'
]
groups=[]
for g,reason in zip(q['component_groups'],reasons):
    groups.append({'component_id':g['group'],'decision':'approved_precise_component','lean_declarations':[N+n for n in g['lean_declarations']],'hypotheses':q['explicit_hypotheses'],'per_component_reason':reason,'missing_clauses':[]})
scope_limits=[
    'The five-body pack is in least-feasible scalar-coordinate orientation. A general nonzero scalar linear objective can be represented by a sign change, but that objective/reflection equivalence is not exported here and must be supplied explicitly before a whole general source(a) correspondence decision.',
    'The actual singleton minimizer map must be measurable and attained; every sampled-plus-fresh instance must have the stated feasible witness. These are explicit premises matching the corresponding scenario feasibility, existence and measurability domain, not derived facts about an arbitrary constraint family.',
    'No higher-dimensional general Campi theorem, generic GP posterior construction, robust MPC theorem, whole Exercise19 or full question1393 approval follows from these three component decisions.'
]
report={'status':'independent_convex_interval_risk26_five_full_bodies_three_precise_components_review_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; source/request author Applied','original_request':ref(request_name),'entire_original_request_body_and_time':q,'all_five_complete_source_bodies_read':{'source':q['proof_source'],'entire_source_text':text,'public_declarations':[N+n for n in names]},'entire_selected_generic_and_continuous_risk_dependency_read':{'source':ref(dependency_name),'entire_source_text':dependency_text},'entire_current_exercise_and_literal_units_read':{'exercise':q['entire_current_exercise'],'material_units':q['current_material_units']},'components':groups,'whole_exercise_approved':False,'whole_source_unit_approved':False,'remaining_whole_source_scope':scope_limits,'all_original_gap_review_body_and_time_retained':prior,'actual_original_trial_records_and_times':records,'actual_standalone_zero_count':1,'actual_failed_trial_count':3,'three_genuine_pass_warnings_retained':True,'primary_campi_garatti_full_assumptions_and_theorem_scope_read':q['primary_source_scope'],'primary_local_mathlib_passages_read':primary,'all1144_selected24_source_hashes_rechecked_exact':True,'coverage_complete':False,'scope':'TMP-only semantic component review. All five full mathematical bodies and full literal/source/primary scope read. No canonical/named compiler, held owner25 candidate amendment, installation, aggregate, publication or whole-source promotion is inferred. Original gap decisions/time and all trial failures/logs/runners remain unchanged.'}
report['first_reader_failure_preserved']={'reason': 'The first reader counted a linter explanatory warning: phrase as an extra diagnostic. The second counts only actual source-position warning lines; original log unchanged.', 'closed_originals': [{'file': '/tmp/check-lyapunov-convex-interval-risk26-independent-foundations-v1.py', 'sha256': '407cd2aae72707df557f1fa66e506958c3bd3db9204d8060befc6e341d954617'}, {'file': '/tmp/run-lyapunov-convex-interval-risk26-independent-foundations-v1.py', 'sha256': 'ed6902cf757c454eee5755fbb0f120e167714d6f02e0dec085d68ccfba5e98bb'}, {'file': '/tmp/lyapunov-convex-interval-risk26-independent-foundations-actual-v1.json', 'sha256': '7dc1b2a316a14e2ec5b06ed018c4ab42dddccaf21f914907dc7c8946457baa92'}, {'file': '/tmp/lyapunov-convex-interval-risk26-independent-foundations-actual-v1.log', 'sha256': 'f0ee8f8cc3d3e4b23505040cdde97ba3d6e4b2052cfdb4ce94c1dc748f5610b3'}]}
out=Path('/tmp/lyapunov-convex-interval-risk26-independent-foundations-observations-v2.json')
assert not out.exists()
out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'observation':ref(out),'public_bodies':5,'approved_components':3,'whole_source_unit_approved':False}))
