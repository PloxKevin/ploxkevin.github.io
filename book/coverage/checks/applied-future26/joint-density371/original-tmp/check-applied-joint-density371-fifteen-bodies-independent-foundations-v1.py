"""Fresh full-literal semantic peer, TMP only. No compiler or coverage writer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(n):return {'file':str(n),'sha256':H(path(n))}
def checked(r):
    assert H(path(r['file']))==r['sha256'],r['file']
    return json.loads(path(r['file']).read_text())
REQUEST='/tmp/applied-joint-density371-two-source-full-literal-review-request25-v1.json'
assert H(Path(REQUEST))=='1f8c634a083e37eb2a2ad6399fecf3d8290bd35a55312d44e6fb7b837481071a'
request=json.loads(Path(REQUEST).read_text())
inventory=checked(request['current_inventory'])
assert H(ROOT/'book/coverage/inventory.json')==request['current_inventory']['sha256']
unit=request['entire_current_material_unit']
current=next(u for u in inventory['material_source_units']if u['key']==unit['key'])
assert current==unit
context=request['full_page_context']
assert H(ROOT/context['source'])==context['sha256']==unit['source_sha256']
assert ''.join((ROOT/context['source']).read_text().splitlines(keepends=True)[309:330])==context['raw_lines310_through330']
assert hashlib.sha256(unit['source_text'].encode()).hexdigest()==unit['text_sha256']
assert 'With a joint density:' in unit['source_text']
sources=[]
trials=[]
theorem_count=0
for source in request['proof_sources']:
    p=path(source['source']['file'])
    assert H(p)==source['source']['sha256']
    text=p.read_text()
    assert text==source['entire_proof_source_text']
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    namespace=re.search(r'^namespace (\S+)',text,re.M).group(1)
    names=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
    declared=[d['name']for d in source['public_declarations']if d['kind']=='theorem']
    assert names==declared
    theorem_count+=len(names)
    for trial in source['actual_trials']:
        record=checked(trial['record'])
        assert record==trial['entire_actual_original_record']
        assert type(record['actual_exit_code'])is int and record['actual_exit_code']in(0,1)
        assert record['status']==('passed'if record['actual_exit_code']==0 else'failed')
        assert record['actual_command']==['lake','env','lean',str(p)]
        assert record['actual_workdir']==str(ROOT/'verification/lean')
        assert record['source']==str(p)
        assert record['source_sha256_before']==record['source_sha256_after']==record['source_snapshot_sha256']
        assert H(Path(record['source_snapshot']))==record['source_snapshot_sha256']
        assert H(Path(record['log']))==record['log_sha256']
        assert H(Path(record['actual_runner']))==record['actual_runner_sha256']
        for alias in trial['all_closed_original_byte_references']:
            assert H(path(alias['file']))==alias['sha256']
        if record['actual_exit_code']==0:
            assert record['source_sha256_after']==source['source']['sha256']
            assert 'error:'not in Path(record['log']).read_text()
        trials.append({'original_record':trial['record'],'entire_original_record_and_time':record,'original_closed_byte_references':trial['all_closed_original_byte_references']})
    sources.append({'source':source['source'],'entire_source_text':text,'all_public_theorem_declarations':names,'definitions_and_markov_instance_read':True})
assert theorem_count==15 and len(trials)==6
assert sum(x['entire_original_record_and_time']['actual_exit_code']==0 for x in trials)==2
assert sum(x['entire_original_record_and_time']['actual_exit_code']==1 for x in trials)==4
prior=checked({k:request['original_event_component_peer'][k]for k in ['file','sha256']})
assert prior==request['original_event_component_peer']['entire_original_body_and_time']
assert 'passed'in prior['status'] and prior['errors']==[]
prior371=next(u for u in prior['material_units']if u['key']==unit['key'])
assert prior371['entire_inventory_record']==unit and prior371['whole_source_unit_approved']is False
assert len(prior371['components'])==4
retained_sources=[]
for retained in request['retained_actual_event_canonical_sources']:
    assert H(ROOT/retained['file'])==retained['sha256']
    text=(ROOT/retained['file']).read_text()
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    pairs=[]
    for pair in retained['actual_native_pair']:
        record=checked(pair)
        exits=[record[k]for k in('exit_code','actual_exit_code')if k in record]
        assert exits and all(type(x)is int and x==0 for x in exits)
        assert record['source_sha256_before']==record['source_sha256_after']==retained['sha256']
        pairs.append({'reference':pair,'entire_original_record_and_time':record})
    retained_sources.append({'source':{k:retained[k]for k in ['file','sha256']},'entire_source_text':text,'retained_canonical_pairs':pairs})
primary_root=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'
primary_specs=[('Probability/Kernel/WithDensity.lean',23,71),('Probability/Kernel/Composition/WithDensity.lean',43,80),('Probability/Kernel/Composition/MeasureCompProd.lean',33,81),('MeasureTheory/Measure/WithDensity.lean',276,303),('MeasureTheory/Measure/Prod.lean',436,461),('MeasureTheory/Measure/Prod.lean',1013,1046),('MeasureTheory/Integral/Lebesgue/Basic.lean',304,339)]
primary=[]
for n,a,b in primary_specs:
    p=primary_root/n
    primary.append({'file':str(p.relative_to(ROOT)),'sha256':H(p),'start_line':a,'end_line':b,'exact_primary_source_read':''.join(p.read_text().splitlines(keepends=True)[a-1:b])})
manifest_name='reports/full-coverage/checkpoint-24-manifest.json'
manifest=json.loads((ROOT/manifest_name).read_text())
assert len(manifest['proof_files'])==1144
for n,r in manifest['proof_files'].items():assert H(ROOT/n)==r['sha256']
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
assert len(assets)==31
for n,h in assets.items():assert H(ROOT/n)==h
assert all(s['source']['file']not in manifest['proof_files']for s in sources)
G='SafeLearning.CompleteAppliedJointDensityBayesGeneral25.'
P='SafeLearning.CompleteAppliedPriorLikelihoodDensity25.'
components=prior371['components']+[
    {'component_id':'generic_joint_density_marginal_and_pointwise_ratio','lean_declarations':[G+'actual_joint_density_y_marginal_is_its_integrated_density',G+'actual_positive_finite_evidence_posterior_has_the_ratio_density',G+'posteriorKernel_markov'],'hypotheses':['Measurable nonnegative joint density on a product of SFinite reference measures. The printed pointwise ratio is used only at evidence density strictly between zero and infinity; an available fallback point is automatic for the ordinary nonempty Euclidean density domain.'],'per_component_reason':'The marginal is the pushforward of the actual density-weighted joint measure, not a formal denominator symbol. At positive finite marginal density the constructed measurable posterior is exactly the reference measure with density p(x,y)/p(y). Its normalization is derived by integrating and canceling the actual marginal. The separately verified Markov instance makes it a genuine conditional probability kernel.','missing_clauses':[]},
    {'component_id':'normalized_joint_regular_evidence_and_actual_disintegration','lean_declarations':[G+'actual_probability_joint_has_normalized_marginal',G+'actual_probability_joint_has_almost_everywhere_regular_evidence',G+'actual_probability_joint_reversed_is_its_marginal_and_ratio_posterior'],'hypotheses':['The measurable joint density has total integral one; SFinite reference measures. Conditional densities are versions determined up to actual marginal-law null sets. No finite-everywhere density premise or ratio at a zero/infinite evidence point is asserted.'],'per_component_reason':'Joint normalization derives marginal normalization and finite evidence almost everywhere under the reference measure; weighting by the marginal also removes its zero set. The posterior fallback at exceptional evidence therefore has no effect on the actual law. The full reversed joint equals marginal composed with the ratio posterior. The proof treats zero sections by a.e. vanishing of a nonnegative function with zero integral, so it does not smuggle a pointwise finite-density assumption or assume a disintegration conclusion.','missing_clauses':[]},
    {'component_id':'actual_prior_likelihood_data_marginal_integral','lean_declarations':[P+'actual_normalized_likelihood_is_markov',P+'actual_normalized_prior_is_probability',P+'actual_generated_joint_has_prior_times_likelihood_density',P+'actual_prior_times_likelihood_joint_is_normalized',P+'actual_generated_data_law_has_integrated_likelihood_density'],'hypotheses':['Measurable prior density with total integral one and jointly measurable likelihood density normalized for every input in its chosen conditional-law version, against SFinite reference measures. This is a density model, not an arbitrary singular distribution or an assertion about null conditioning values.'],'per_component_reason':'The actual conditional observation kernel is genuinely Markov and the prior measure genuinely probability. Their actual composition-product has density prior(x)*likelihood(x,y), its normalization is proved by Tonelli, and its data pushforward has exactly the printed integral of likelihood times prior. This derived normalized joint can be used in the general reversed-joint theorem. Neither the joint density identity nor the marginal formula is an assumed conclusion.','missing_clauses':[]}
]
declarations=list(dict.fromkeys(n for c in components for n in c['lean_declarations']))
decision={'key':unit['key'],'entire_inventory_record':unit,'disposition':'whole_mathematical_source_unit_approved','whole_source_unit_approved':True,'lean_declarations':declarations,'components':components,'hypotheses':['Event conditional formulas have the ordinary measurable positive-conditioning interpretation; finite partition cells of zero mass use the verified zero-weight convention. Bayes requires positive observed-event probability for its literal interpretation.','Density formulas refer to measurable normalized densities relative to the indicated SFinite product references, with positive finite evidence for pointwise ratios and a.e. conditional-density versions under the actual data law. No arbitrary null-evidence conditional value is determined.'],'per_component_reason':'All four event/finite-partition formulas remain supported by the unchanged canonical event source and exact original peer. The new two genuinely checked TMP sources derive the formerly missing arbitrary density marginal, normalized ratio posterior, actual reversed-law identity, and actual prior-times-likelihood marginal. These cover every mathematical clause of the complete definition under its ordinary conditioning and density domains.','missing_clauses':[]}
report={'status':'independent_fresh_whole371_generic_joint_density_fifteen_full_bodies_and_retained_event_proofs_review_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; proof/request author Applied','original_request':ref(REQUEST),'entire_original_request_body_and_time':request,'material_units':[decision],'whole_material_unit_count':1,'entire_prior_event_peer_body_and_original_time_retained':prior,'prior371_four_component_decisions_body_and_time_unchanged':prior371,'all_fifteen_new_public_bodies_definitions_and_markov_instance_read':sources,'retained_complete_canonical_event_proof_sources_read':retained_sources,'primary_local_mathlib_source_passages_read':primary,'all_six_unique_actual_trial_records_and_times_retained':trials,'genuine_tmp_standalone_zero_count':2,'genuine_tmp_failure_count':4,'pass_warning_logs_retained_exact':True,'all1144_selected24_sources_and_all31_current52_assets_rehashed_exact':True,'coverage_complete':False,'scope':'Fresh TMP-only complete371 semantic decision. The previous four event component decisions and their original partial whole status/time remain immutable history. The two new density sources have genuine TMP standalone evidence only; no canonical/named execution, held seven-source43 offer amendment, live owner/inventory/source write, aggregate, parent exercise or whole section approval is inferred. Ordinary positive-conditioning, positive-finite evidence and a.e. density-version domains are explicit.'}
out=Path('/tmp/applied-joint-density371-independent-foundations-full-source-review25-v1-observation.json')
assert not out.exists()
out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'observation':ref(out),'whole_material_units':1,'public_bodies':15,'actual_standalone_zero':2,'actual_failed_trials':4}))
