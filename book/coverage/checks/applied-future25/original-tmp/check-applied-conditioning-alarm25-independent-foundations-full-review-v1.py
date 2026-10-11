from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re, copy
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
def P(n):
    p=Path(n);return p if p.is_absolute()else ROOT/p
def checked(r):
    p=P(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
def ref(p):return {'file':str(p),'sha256':H(p)}
request=Path('/tmp/applied-conditioning-alarm-material25-seven-literals-full-source-review-request-v1.json')
assert H(request)=='3a4f09f8158289f5e972b703e4bea167b528a28d45d966a95b55b5e68e159121'
d=J(request);old=J(checked(d['current_historical_inventory']));page=checked(d['source_page'])
current_path=ROOT/'book/coverage/inventory-after-correction52.json'
assert H(current_path)==H(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
current=J(current_path);old_units={r['key']:r for r in old['material_source_units']};now_units={r['key']:r for r in current['material_source_units']}
for unit in d['material_units']:assert unit['entire_inventory_record']==old_units[unit['source_unit_key']]==now_units[unit['source_unit_key']]
for context in d['complete_source_contexts']:
    p=checked(context);assert ''.join(p.read_text().splitlines(keepends=True)[context['start_line']-1:context['end_line']])==context['exact_lines']
assert len(d['material_units'])==7
names=[]
for source in d['actual_full_proof_sources']:
    p=checked(source);text=p.read_text();assert text==source['entire_source']and not re.search(r'\b(sorry|admit|axiom|unsafe)\b',text)
    assert len(re.findall(r'^theorem\s+',text,re.M))==len(source['public_theorem_names']);names.extend(source['public_theorem_names'])
assert len(names)==len(set(names))==10
hist=d['exact_original_passed_failed_trial_history_sha256'];assert len(hist)==12
for n,h in hist.items():assert H(P(n))==h
records=[]
for n in hist:
    if not n.endswith('.json'):continue
    r=J(P(n));assert r['source_sha256_before']==r['source_sha256_after']==r['source_snapshot_sha256']==H(P(r['source_snapshot']))
    assert r['actual_command']==['lake','env','lean',r['source']]and r['actual_workdir']==str(ROOT/'verification/lean')
    assert H(P(r['log']))==r['log_sha256']and H(P(r['actual_runner']))==r['actual_runner_sha256']
    records.append(r)
assert sorted(r['actual_exit_code']for r in records)==[0,0,1]
for entry in d['actual_TMP_standalone_passes']:
    r=J(checked(entry));assert r==entry['entire_actual_record']and r['actual_exit_code']==0
    assert H(P(r['source']))==r['source_sha256_before']
assert Path('/tmp/applied-conditioning-alarm-material25-trial2.log').read_bytes()==b''
warning=Path('/tmp/applied-three-equal-conditional-outcomes25-trial1.log').read_text();assert warning.count('warning:')==2
primary=checked(d['primary_official_mathlib']);local=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Probability/ConditionalProbability.lean'
assert H(local)==H(primary)
for name in ['def cond','cond_isProbabilityMeasure','ae_cond_mem','theorem cond_apply','theorem cond_mul_eq_inter']:
    assert name in local.read_text()
linked=''.join(page.read_text().splitlines(keepends=True)[1239:1243]);assert 'false alarm'in linked and 'posterior probability'in linked
selection=J(ROOT/'reports/full-coverage/checkpoint-23-selection.json');assert len(selection['proof_files'])==1131
for n,row in selection['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==row['sha256']
reasons={
 '366':'The actual conditioned measure is restriction to the event times its inverse mass, is genuinely a probability measure, and is a.e. concentrated on the conditioning event. The distinct generic three-atom theorem derives the retained mass 3q by measure additivity and proves every retained atom has conditional mass1/3. The instruction about the vertical bar matches the directly read Mathlib notation and claims no extra theorem.',
 '370':'The full body unfolds the real conditional-measure construction, proves positive-event normalization and a.e. membership in B. Thus removed outcomes have zero conditioned mass and retained weights are rescaled to a probability measure under the source positive-event condition.',
 '377':'The arbitrary finite measurable disjoint partition covering the whole space yields total probability by actual measure additivity over A intersections and the product rule. Bayes is then derived by rewriting the real conditional ratio and complete denominator sum. The ordinary positive-conditioning interpretation of the source is retained; the native formulas also extend to zero-weight cells using Mathlib zero-measure convention.',
 '378':'A genuine normalized four-atom PMF represents fault/alarm, fault/quiet, healthy/alarm and healthy/quiet. Its derived event masses and actual conditioned measures give exactly1% prior, .95 fault detection and .05 healthy false-alarm rate. These quantities are not merely algebraic inputs declared to be conditionals.',
 '380':'The actual alarm-conditioned law gives posterior19/118 and alarm mass59/1000. It equals the printed .95*.01/(.95*.01+.05*.99), with the derived joint mass19/2000=.0095 and alarm mass.059 giving the second exact fraction. The absolute error from.161 is strictly less than.0005, proving the stated rounding.',
 '381':'The actual healthy-given-alarm posterior is99/118, within.01 of5/6; the healthy-alarm mass.0495 exceeds fault-alarm.0095 despite the .05 healthy false-alarm rate. Fault-given-alarm differs from alarm-given-healthy. A distinct genuine normalized experiment retains both monitor rates while changing prior to.1 and posterior to19/28, proving dependence on the prior. Section10\'s directly read definition treats false alarms as rejection under a true null and explicitly distinguishes posterior probability; this is a cross-reference, without promoting its other test guarantees.'}
hyp={
 '366':['Measurable event B in a probability space with positive probability; for the equal-outcome clause, three measurable retained atoms with equal positive original mass.'],
 '370':['Measurable positive-probability event B and an actual probability measure.'],
 '377':['Arbitrary finite measurable pairwise-disjoint partition of the whole probability space; measurable event A. Positive observed-event mass for the ordinary Bayes interpretation.'],
 '378':['The explicitly normalized four-atom source-matched law; fault and alarm are the displayed measurable finite events.'],
 '380':['The same actual source-matched law, whose alarm probability is59/1000>0.'],
 '381':['The same source-matched law and the explicitly normalized distinct higher-prior law with the same monitor conditional rates.']}
units=[]
for requested in d['material_units']:
    key=requested['source_unit_key'];node=key.rsplit('-',1)[1]
    if node!='371':
        units.append({'key':key,'entire_inventory_record':now_units[key],'disposition':'whole_mathematical_source_unit_approved','whole_source_unit_approved':True,'lean_declarations':requested['lean_declarations'],'hypotheses':hyp[node],'per_component_reason':reasons[node],'missing_clauses':[]})
    else:
        components=[]
        for declaration,component,reason in zip(requested['lean_declarations'],['conditional_event_ratio','conditional_event_product','finite_partition_total_probability','finite_partition_Bayes'],['Derived from the genuine restricted/rescaled measure and the real conversion of its measured intersection.','Derived actual conditional mass times original event mass equals measured intersection, with finite probability mass ensuring valid conversion.','Actual finite measurable disjoint covering partition gives the full sum by finite measure additivity.','The actual conditional ratio and complete total-probability denominator derive the displayed Bayes rule.']):
            components.append({'component_id':component,'lean_declarations':[declaration],'hypotheses':['Measurable conditioning/event sets in a probability space; finite measurable disjoint covering partition where relevant. Positive conditioning mass for the literal probability interpretation.'],'per_component_reason':reason,'missing_clauses':[]})
        units.append({'key':key,'entire_inventory_record':now_units[key],'whole_source_unit_approved':False,'components':components,'remaining_gaps':['Generic joint-density conditional/marginal integration clause remains pending; event formulas do not close it.']})
report={'status':'independent_conditioning_alarm25_ten_full_bodies_six_whole_literals_and_event_components_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','original_request':ref(request),'entire_original_request_body_and_time':d,'all_ten_full_public_and_private_alarm_event_bodies_read':True,'whole_material_unit_count':6,'partial_material_unit_count':1,'material_units':units,'source51_to_current52_entire_literal_identity':{'historical_inventory':d['current_historical_inventory'],'current_inventory':ref(current_path),'all_seven_entire_inventory_records_unchanged':True,'entire_probability_source_page_unchanged':d['source_page']},'complete_context_and_direct_Section10_false_alarm_definition_read':{'context':d['complete_source_contexts'],'linked_source_page':d['source_page'],'linked_start_line':1240,'linked_end_line':1243,'exact_linked_lines':linked},'primary_complete_conditional_probability_API_read':{'requested_primary':d['primary_official_mathlib'],'actual_imported_local_module':ref(local),'equal_bytes_confirmed':True},'original_unique_trial_records_and_times_retained':records,'genuine_standalone_zero_count':2,'genuine_failure_count':1,'main_pass_log_empty':True,'three_outcome_pass_two_warnings_retained':True,'all1131_selected23_sources_and_frozen_copies_exact':True,'coverage_complete':False,'scope':'Fresh TMP-only semantic peer. Six complete source units and four precise event components in371 approved with genuine hypotheses. Its generic joint-density clause and all neighboring posterior/conditional-expectation/transition/test guarantees remain pending. No new Lean compilation, canonical/named pairing, parent exercise/whole section promotion, owner24 offer amendment, live source, inventory, ledger or publication write.'}
out=Path('/tmp/applied-conditioning-alarm25-independent-foundations-full-source-review-v1.json')
with out.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':ref(out),'whole_material_units':6,'partial_material_units':1}))
