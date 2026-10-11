"""TMP-only independent semantic proposal review; execute no Lean or mutation."""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import html
import json
from pathlib import Path
import re
import shutil
import sys
import importlib.util

ROOT=Path("/home/oxrexkevin/SafetyBased")
PROPOSAL=Path("/tmp/applied-monitoring-modes-source49-qualification-proposal23-v2.json")
PROPOSAL_SHA="125ae48247af82a507ff66309aa51291936efeef72c4f24af4add5461d10f85e"
OUT=Path("/tmp/monitoring-modes-source49-proposal23-independent-foundations-semantic-review-v2.json")
PRIMARY=ROOT/"sources/text/2102.11941.txt"
PEER=Path("/tmp/monitoring-deterministic-path23-independent-applied-components-review-v1.json")
PEER_SHA="e7a00164cc0a409f1d65d71764c570a7d50d1862613ed33bf4662a7b9ed3a532"

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
assert not OUT.exists()
assert sha(PROPOSAL)==PROPOSAL_SHA and sha(PEER)==PEER_SHA
proposal=read(PROPOSAL)
assert sha(PRIMARY)==proposal["independently_justified_source_note"]["local_primary_text_sha256"]=="180117f09dc72abf54e33f69a59ac3ced92d52500612d11f1176fe36ae9c4d51"
source_path=ROOT/proposal["source"]
assert sha(source_path)==proposal["source_sha256_before"]
inventory_path=ROOT/"book/coverage/inventory-after-correction48.json"
assert sha(inventory_path)==proposal["inventory_source48_sha256"]=="2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"
assert sha(ROOT/"book/coverage/inventory.json")==sha(inventory_path)
inventory=read(inventory_path)
simulation_path=Path(proposal["exact_readonly_simulation"]["proposed_inventory"])
assert sha(simulation_path)==proposal["exact_readonly_simulation"]["proposed_inventory_sha256"]
simulation=read(simulation_path)
assert inventory["counts"]==simulation["counts"]
original=source_path.read_text();simulated=original
replacements=proposal["replacements"]
assert [r["source_unit_key"] for r in replacements]==["cmdp.html::node-1138","cmdp.html::node-1141"]
for replacement in replacements:
    assert original.count(replacement["before"])==replacement["count"]==1
    assert replacement["before"].count("\n")==replacement["after"].count("\n")
    simulated=simulated.replace(replacement["before"],replacement["after"],1)
assert hashlib.sha256(simulated.encode()).hexdigest()==proposal["proposed_source_sha256_after"]
reverse=simulated
for replacement in reversed(replacements):
    assert reverse.count(replacement["after"])==1
    reverse=reverse.replace(replacement["after"],replacement["before"],1)
assert reverse==original
changed={}
full_records={}
for group in ["exercises","material_source_units"]:
    previous={r["key"]:r for r in inventory[group]}
    future={r["key"]:r for r in simulation[group]}
    assert set(previous)==set(future)
    differences=[]
    for key,before in previous.items():
        after=future[key]
        assert set(before)==set(after)
        for field in before:
            if field=="source_sha256" and before["source"]==proposal["source"]:
                assert before[field]==proposal["source_sha256_before"] and after[field]==proposal["proposed_source_sha256_after"]
            elif field in ["source_text","text_sha256"]:
                continue
            else:assert before[field]==after[field],(key,field)
        if before["source_text"]!=after["source_text"]:
            differences.append(key)
            full_records[key]={"original":before,"proposed":after}
            assert hashlib.sha256(before["source_text"].encode()).hexdigest()==before["text_sha256"]
            assert hashlib.sha256(after["source_text"].encode()).hexdigest()==after["text_sha256"]
        else:assert before["text_sha256"]==after["text_sha256"]
    changed[group]=differences
assert changed==proposal["expected_changed_text_keys"]
for r in replacements:
    rows=full_records[r["source_unit_key"]]
    assert rows["original"]["source_text"]==html.unescape(r["before"][3:-4])
    assert rows["proposed"]["source_text"]==html.unescape(r["after"][3:-4])
exercise=full_records["cmdp.html::exercise-21"]
expected=exercise["original"]["source_text"]
for r in replacements:
    before=html.unescape(r["before"][3:-4]);after=html.unescape(r["after"][3:-4])
    assert expected.count(before)==1
    expected=expected.replace(before,after,1)
assert expected==exercise["proposed"]["source_text"]
peer=read(PEER)
assert peer["status"]=="passed_independent_actual_controlled_path_components_review_future23" and peer["errors"]==[]
proof=Path(peer["proof_source"]["file"])
assert sha(proof)==peer["proof_source"]["sha256"]=="c85bafe8e12f10392efee43cbfcb00983b91155ca2cba9819065eacef5e54814"
assert len(re.findall(r"^theorem ",proof.read_text(),re.M))==9
actual=peer["actual_standalone_evidence"]
record=read(Path(actual["record"]))
assert sha(Path(actual["record"]))==actual["record_sha256"]
assert record["exit_code"]==actual["actual_exit_code"]==0
assert record["source_sha256"]==sha(proof)
assert sha(Path(actual["raw_log"]))==record["log_sha256"]==actual["raw_log_sha256"]
assert record["command"]==["lake","env","lean",str(proof)]
assert "source_sha256_before" not in record
assert sha(Path(actual["runner"]))==actual["runner_sha256"]
for path,digest in proposal["preserved_current22_component_reviews_sha256"].items():assert sha(ROOT/path)==digest
bindings=read(ROOT/"book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json")
old=read(ROOT/"reports/full-coverage/checkpoint-21-manifest.json")
protected={**bindings["exact_current48_safelearning_assets_sha256"],**bindings["new_immutable_proof_sources_sha256"],**{name:r["sha256"] for name,r in old["proof_files"].items()}}
for name,digest in protected.items():assert sha(ROOT/name)==digest
# Retain the exact previous rejection, checker and genuine execution.
prior_paths={
 "/tmp/applied-monitoring-modes-source49-qualification-proposal23-v1.json":"0aa5af831cd555487955470b8e3e00a0b9f43351ccb7efd1c1c591709196ba69",
 "/tmp/monitoring-modes-source49-proposal23-independent-foundations-semantic-review-v1.json":"bc18238de0cbbc23b1da5515d7055a3018a3a3b1bee996a6392355a082cc6c3e",
 "/tmp/review-monitoring-modes-source49-proposal23-independent-foundations-v1.py":"71e307124913172eec9f4142e39e5d8e3de86e9633585a3f2ac42e726349177b",
 "/tmp/monitoring-modes-source49-proposal23-independent-foundations-execution-v1.json":"c1737384a36b0ef6ada626fcd7fb0fbc08654128a1beb98bfee7be1fbe0a8f44",
 "/tmp/monitoring-modes-source49-proposal23-independent-foundations-execution-v1.log":"07536dbe64a614cb91af5ae94a7670f2f46c8190c22506488e7ab973e9961237",
}
for name,digest in prior_paths.items():assert sha(Path(name))==digest
prior=read(Path('/tmp/monitoring-modes-source49-proposal23-independent-foundations-semantic-review-v1.json'))
old_proposal=read(Path(proposal['preserved_prior_proposal']['file']))
assert proposal['preserved_prior_proposal']['prepared_at_utc']==old_proposal['prepared_at_utc']
assert proposal['replacements'][0]==old_proposal['replacements'][0]
assert proposal['replacements'][1]['before']==old_proposal['replacements'][1]['before']
assert prior['semantic_proposal_approved'] is False

# Fresh full parser run in a new independent TMP tree, with original DOM identities.
SIM=Path('/tmp/foundations-independent-source49-proposal23-simulation-v2')
assert not SIM.exists()
(SIM/'SafeLearning').mkdir(parents=True)
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
pages=sorted((ROOT/'SafeLearning').glob('*.html'))
assert len(pages)==29
for page in pages:
    old_text=page.read_text()
    new_text=simulated if page==source_path else old_text
    old_doc,new_doc=Document(old_text),Document(new_text)
    assert len(old_doc.nodes)==len(new_doc.nodes)
    assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(old_doc.nodes,new_doc.nodes))
    (SIM/'SafeLearning'/page.name).write_text(new_text)
spec=importlib.util.spec_from_file_location('foundation_independent_inventory49',ROOT/'book/inventory_claims.py')
generator=importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)
generator.ROOT=SIM
generator.OUT=SIM/'book/coverage'
generator.inventory()
fresh_path=generator.OUT/'inventory.json'
fresh=read(fresh_path)
assert set(fresh)==set(simulation)
assert all(fresh[k]==simulation[k] for k in fresh if k!='generated_at_utc')

# Genuine trial8 evidence is standalone only. Inspect the original runner's cwd.
dual_peer_path=Path('/tmp/monitoring-dual-trajectory23-independent-applied-components-review-v1.json')
assert sha(dual_peer_path)=='bd5dc5db2c197c5484231381b8de4f64c8227546b5076af5fa8c7015edece4bd'
dual_peer=read(dual_peer_path)
assert dual_peer['errors']==[] and 'passed' in dual_peer['status']
dual_source=Path(dual_peer['proof_source']['file'])
assert sha(dual_source)==dual_peer['proof_source']['sha256']=='5bda63b3a3c585ba3180a4c6f65fc5a146a629e85f1404337a1c3ab18b922957'
dual_text=dual_source.read_text()
names=re.findall(r'^theorem (\w+)',dual_text,re.M)
assert len(names)==28
new_names=['SafeLearning.CompleteMonitoringDualTrajectory23.'+n for n in names[9:]]
assert len(new_names)==19
assert [n for group in dual_peer['approved_new_components'] for n in group['lean_declarations']]==new_names
prefix=dual_text.split('\nnamespace SafeLearning.CompleteMonitoringDualTrajectory23\n')[0]
assert prefix.replace('import SafeLearning.CompleteMonitoringDeficit22\n','',1).rstrip()==proof.read_text().rstrip()
dual_actual=dual_peer['actual_standalone_evidence']
dual_record=read(Path(dual_actual['record']))
assert sha(Path(dual_actual['record']))==dual_actual['record_sha256']
assert type(dual_record['exit_code']) is int and dual_record['exit_code']==dual_actual['actual_exit_code']==0
assert dual_record['source_sha256']==sha(dual_source)
assert dual_record['command']==['lake','env','lean',str(dual_source)]
assert 'source_sha256_before' not in dual_record
assert sha(Path(dual_actual['raw_log']))==dual_record['log_sha256']==dual_actual['raw_log_sha256']
assert Path(dual_actual['raw_log']).read_text().count('warning:')==5
assert sha(Path(dual_actual['runner']))==dual_actual['runner_sha256']
assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in Path(dual_actual['runner']).read_text()
for name,digest in proposal['new_actual_future23_proof_and_review_evidence_sha256'].items():assert sha(Path(name))==digest
owner_execution_path=Path('/tmp/applied-monitoring-modes-source49-proposal23-execution-v2.json')
owner_execution=read(owner_execution_path)
assert owner_execution['actual_command']==['python3',proposal['actual_checker']]
assert owner_execution['actual_workdir']==str(ROOT) and owner_execution['actual_exit_code']==0
assert sha(Path(proposal['actual_checker']))==proposal['actual_checker_sha256']==owner_execution['checker_sha256']
assert sha(Path(owner_execution['log']))==owner_execution['log_sha256']

# Independent exact rational witnesses to each price regime and the orbit.
def action(state,l1,l2):
    if state==0:return l1<l2
    own,other=(l1,l2) if state==1 else (l2,l1)
    return own>1 and own>=other
def physical_step(state,l1,l2):
    choice=action(state,l1,l2)
    return (2 if choice else 1) if state==0 else (state if choice else 0)
fixture_results=[]
price_values=[Fraction(0),Fraction(1,2),Fraction(1),Fraction(3,2),Fraction(2)]
for l1 in price_values:
    for l2 in price_values:
        for start in range(3):
            path=[];seen={};state=start
            while state not in seen:
                seen[state]=len(path);path.append(state)
                state=physical_step(state,l1,l2)
            cycle_states=path[seen[state]:]
            vector=[Fraction(cycle_states.count(i),len(cycle_states)) for i in range(3)]
            score=vector[0]+l1*vector[1]+l2*vector[2]
            bound=max(l1,l2,(1+l1)/2,(1+l2)/2)
            assert score==bound
            fixture_results.append({'prices':[str(l1),str(l2)],'initial_state':start,'cycle':cycle_states,'fraction_vector':[str(x) for x in vector],'score':str(score),'vertex_max':str(bound)})
assert action(1,Fraction(2),Fraction(2)) and action(2,Fraction(2),Fraction(2))
assert not action(1,Fraction(1),Fraction(1)) and not action(2,Fraction(1),Fraction(1))
orbit=[(0,Fraction(0),Fraction(0))]
for n in range(23):
    state,l1,l2=orbit[-1]
    orbit.append((physical_step(state,l1,l2),max(0,l1+Fraction(1,3)-(state==1)),max(0,l2+Fraction(1,3)-(state==2))))
expected_cycle=[(1,Fraction(1),Fraction(2,3)),(0,Fraction(1,3),Fraction(1)),(2,Fraction(2,3),Fraction(4,3)),(2,Fraction(1),Fraction(2,3)),(0,Fraction(4,3),Fraction(0)),(1,Fraction(5,3),Fraction(1,3))]
assert orbit[5:11]==expected_cycle
assert all(orbit[n]==expected_cycle[(n-5)%6] for n in range(5,len(orbit)))
assert [sum(z[0]==i for z in expected_cycle) for i in range(3)]==[2,2,2]

reasons_b=prior['per_unit_decisions'][0]['clauses']
reasons_c=[
 {'clause':'canonical maximizing modes including every tie','decision':'semantically_approved','reason':'For unequal prices, the larger-price region is chosen from R0. If that price exceeds1 it stays there, giving the correct absorbing maximum vertex; if it is at most1 it alternates there, giving the correct alternating vertex, including the unit-threshold tied-face endpoint. At equal prices above1 each current region stays, giving an endpoint of the maximizing absorbing edge. At equal prices below1 each returns and R0 chooses R1, giving an endpoint of the maximizing alternating edge. At(1,1) returning is permitted because the affine objective is constant. The total equality cases resolve the exact preserved V1 counterexample. Realizing a face here means selecting one representative on that maximizing face, not realizing every point of the face with a single deterministic mode.'},
 {'clause':'projected epoch update and changing modes','decision':'semantically_approved','reason':'For positive fixed step eta, the epoch update is max(0,lambda_i+eta*(1/3-epoch_fraction_i)). Below-target fractions raise the multiplier, above-target fractions lower it with projection at zero, and a changing multiplier can change the specified deterministic mode. No particular switching schedule is inferred for general initialization or epoch duration.'},
 {'clause':'concrete zero-initial per-step controller and its limits','decision':'semantically_approved_with_exact_future23_standalone_scope','reason':'All19 new trial8 theorem bodies have been read. The exact physical/price trajectory from(R0,0,0) reaches cycle0 at time5 and has a six-periodic tail. Natural price counters divided by3 are proved equal to the real projectedStep with step1 and source recursive multiplier sequences. The qualified selector matches every action on the complete orbit. The admitted path is realized by a genuine controlled history law, its true expected visit fractions equal deterministic counts, the finite-prefix/tail identity and bounded telescope yield full-horizon expected limits1/3, and simultaneous a.s. realization gives all sample visit limits1/3. This direct instance does not use A3; it does not prove general-initialization convergence or a universal stochastic epoch theorem.'},
 *prior['per_unit_decisions'][1]['clauses'][2:]
]
report={
 'status':'passed_independent_source49_qualification_proposal_semantic_review_future23',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'proposal':{'file':str(PROPOSAL),'sha256':PROPOSAL_SHA},
 'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),
 'mechanical_check_errors':[],'semantic_proposal_approved':True,
 'html_inventory_or_canonical_written':False,
 'exact_readonly_forward_reverse_and_inventory_binding_verified':True,
 'changed_inventory_text_keys':changed,'complete_original_and_proposed_records':full_records,
 'per_unit_decisions':[
  {'source_unit_key':'cmdp.html::node-1138','whole_proposal_semantics_approved':True,'formal_whole_unit_coverage_approved':False,'clauses':reasons_b,'missing_semantic_clauses':[]},
  {'source_unit_key':'cmdp.html::node-1141','whole_proposal_semantics_approved':True,'formal_whole_unit_coverage_approved':False,'clauses':reasons_c,'missing_semantic_clauses':[]}
 ],
 'preserved_original_blocked_proposal_and_review_sha256':prior_paths,
 'original_blocked_reviewed_at_utc':prior['reviewed_at_utc'],
 'v1_blocking_counterexample_exact':prior['blocking_counterexample'],
 'corrected_total_selector':{'R0':'Choose larger multiplier region, tieR1.','Ri':'Stay iff lambda_i>1 and lambda_i>=lambda_j; otherwise return throughR0.','equal_above_one':'Stay in current region.','threshold_one':'Return, selecting a maximizing alternating endpoint.','all_real_price_regime_argument':reasons_c[0]['reason'],'exact_rational_fixtures':fixture_results,'fixture_scope':'75 exact checks independently confirm the analytical case reading; they are not a new Lean proof for all real prices.'},
 'independent_exact_per_step_orbit_check':{'step_size':1,'initial_state':'R0','initial_multipliers':['0','0'],'cycle_entry_time':5,'cycle_states_and_prices':[[z[0],str(z[1]),str(z[2])] for z in expected_cycle],'cycle_visit_counts':[2,2,2],'scope':'Independent rational consistency check of the source definitions. Formal all-time and limit evidence is the actual trial8 source and original standalone execution.'},
 'fresh_independent_full29_page_parser':{'inventory':str(fresh_path),'sha256':sha(fresh_path),'generator':'book/inventory_claims.py','generator_sha256':sha(ROOT/'book/inventory_claims.py'),'validator_sha256':sha(ROOT/'book/validate.py'),'pages':29,'counts':fresh['counts'],'exact_match_to_author_simulation_except_generated_at_utc':True,'all_keys_lines_attributes_locators_and_DOM_signatures_preserved':True,'only_three_text_records_changed':True},
 'primary_source':prior['primary_source'],
 'Root_trial6_and_original_component_peer':prior['Root_trial6_and_original_component_peer'],
 'Root_trial8_and_new_component_peer':{'peer_file':str(dual_peer_path),'peer_sha256':sha(dual_peer_path),'original_reviewed_at_utc':dual_peer['reviewed_at_utc'],'all28_full_theorem_bodies_read':True,'new19_full_declarations':new_names,'source_file':str(dual_source),'source_sha256':sha(dual_source),'actual_original_standalone':dual_actual,'all_six_original_component_decisions_exact':dual_peer['approved_new_components'],'scope':'Independent source/proposal comparison approves this zero-initial deterministic realization only. Original Applied decision/time and all nonempty warning logs are retained; no named or aggregate23 execution is inferred.'},
 'author_proposal_actual_preparation_execution':{'file':str(owner_execution_path),'sha256':sha(owner_execution_path),'body':owner_execution},
 'preserved_current22_component_reviews_sha256':proposal['preserved_current22_component_reviews_sha256'],
 'all31_current48_assets_and1089_old_plus24_reviewed22_proof_sources_checked_exact':True,
 'new_dual_trajectory_pack_reviewed':True,'new_dual_trajectory_pack_selected':False,
 'whole_corrected_exercise_approved':False,'coverage_complete':False,
 'limits':['Only the two literal proposed replacement paragraphs are semantically approved. No source49 release, source correction, working inventory update, canonical proof binding or formal whole-exercise promotion is made.','Both future23 proof sources have genuine TMP standalone0 records only. No named build, aggregate audit or checkpoint22 selection is claimed.','The direct six-cycle instance does not validate A3 for general finite epochs. External Theorem1 remains conditional and distinguishes a.s. feasibility from expected reward.']
}
assert sha(PROPOSAL)==PROPOSAL_SHA and sha(PEER)==PEER_SHA
assert sha(source_path)==proposal['source_sha256_before'] and sha(inventory_path)==proposal['inventory_source48_sha256']
for name,digest in protected.items():assert sha(ROOT/name)==digest
for name,digest in prior_paths.items():assert sha(Path(name))==digest
for name,digest in proposal['preserved_current22_component_reviews_sha256'].items():assert sha(ROOT/name)==digest
with OUT.open('x') as output:output.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'review':str(OUT),'review_sha256':sha(OUT),'node1138_semantic_approved':True,'node1141_semantic_approved':True,'fresh_parser_pages':29,'new_public_theorem_bodies':19,'formal_whole_exercise_approved':False}))
