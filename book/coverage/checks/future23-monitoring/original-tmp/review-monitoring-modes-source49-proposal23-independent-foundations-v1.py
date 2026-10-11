"""TMP-only independent semantic proposal review; execute no Lean or mutation."""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import html
import json
from pathlib import Path
import re

ROOT=Path("/home/oxrexkevin/SafetyBased")
PROPOSAL=Path("/tmp/applied-monitoring-modes-source49-qualification-proposal23-v1.json")
PROPOSAL_SHA="0aa5af831cd555487955470b8e3e00a0b9f43351ccb7efd1c1c591709196ba69"
OUT=Path("/tmp/monitoring-modes-source49-proposal23-independent-foundations-semantic-review-v1.json")
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
# Exact rational counterexample to the literal otherwise-return default at (2,2).
l1=l2=Fraction(2)
v3=(Fraction(1,2),Fraction(1,2),Fraction(0))
v1=(Fraction(0),Fraction(1),Fraction(0))
score=lambda v:v[0]+l1*v[1]+l2*v[2]
lagrangian=lambda v:score(v)-(l1+l2)/3
assert not (l1>max(1,l2)) and not (l2>max(1,l1))
assert score(v3)==Fraction(3,2)<score(v1)==2
assert lagrangian(v3)==Fraction(1,6)<lagrangian(v1)==Fraction(2,3)
reasons_b=[
 {"clause":"expected achievable fractions and four vertices","decision":"semantically_approved_under_existing_expected_value_and_limit_exists_conventions","reason":"For any controlled policy with existing expected fractions, no R0 self-loop gives V0<=1/2 and normalization. The complete controlled Markov realization covers every simplex point with this bound. The vertex descriptions are representative modes, rather than restrictions on all transients."},
 {"clause":"linear objective, interior optimum and price faces","decision":"semantically_approved","reason":"The objective is affine on the two-dimensional simplex plane. The four scores are l1,l2,(1+l1)/2,(1+l2)/2. The strict-case vertices, l_i=1 unequal-price edge, equal-price below-one edge and equal-price above-one edge are all exact; constrained-optimal fractions are uniquely (1/3,1/3,1/3), requiring constant weights l1=l2=1. Interior means relative interior in the simplex plane."},
 {"clause":"stationary mixed staying example","decision":"semantically_approved","reason":"The explicitly representative no-return policy has expected fractions (0,q,1-q), feasible exactly for q between1/3 and2/3. Its individual sample paths select one absorbing region, so expected feasibility does not imply single-trajectory feasibility."},
 {"clause":"finite prefixes and growing history-policy realization","decision":"semantically_approved_with_unselected_future23_formal_scope_retained","reason":"A fixed finite prefix contributes at most its finite length divided by T to bounded reward averages. The actual TMP trial6 realizes admitted scheduled paths by a genuine controlled history law, and realizes the growing-block path almost surely. Region counts have quadratic completed-cycle size and at-most-linear partial-cycle discrepancy, yielding all-horizon fractions (0,1/2,1/2) and O(sqrt T) R0 visits. These nine new bodies currently have only genuine TMP standalone evidence; no named or aggregate23 pass is asserted."},
 {"clause":"zero return on the above-one maximizing edge and nonoptimal recovery","decision":"semantically_approved","reason":"The v1-v2 edge has V0=0, below the constrained optimum1/3. Other non-unit price maximizing faces violate at least one region constraint. The concluding restriction to lambda!=(1,1) is required and correct."}
]
reasons_c=[
 {"clause":"canonical fixed-price mode and ties","decision":"revision_required","reason":"The unconditional otherwise-return rule overlaps the equality cases. At l1=l2=2 it returns from both regions; any R0 tie route then has V0=1/2 and gives score3/2, below the staying face score2. If the following tie instruction is intended to override otherwise-return, it must say so explicitly and restrict tie choices to genuinely maximizing modes."},
 {"clause":"projected epoch update and changing modes","decision":"semantically_approved_subject_to_corrected_total_maximizing_selector","reason":"For positive fixed step eta, the epoch update is max(0,lambda_i+eta*(1/3-epoch_fraction_i)). A below-target fraction strictly raises the multiplier; an above-target fraction lowers it subject to clipping, and changing multipliers can change the selected mode. No necessary switching frequency or unconditional concrete-trajectory convergence is inferred."},
 {"clause":"Theorem1 and A1-A3","decision":"semantically_approved_as_explicitly_conditional_external_primary_attribution","reason":"Primary Theorem1 uses exact Lagrangian-maximizing policies, positive fixed step/epoch setting, strict feasibility, bounded violations and conditional unbiased epoch estimates. Section7 correctly records the vector-norm interpretation of B and objective-estimate qualification. Its guarantee is a.s. constraint liminf feasibility and expected near-optimal reward; it is not a pathwise near-optimal reward guarantee, and no actual satisfaction of A3 for this selector is claimed."},
 {"clause":"finite epoch bias and AppendixII","decision":"semantically_approved","reason":"EpochBias22 gives a true exact-maximizing initial epoch with long-run region1 fraction1 and finite-N fraction1-1/N. Long-run maximization therefore cannot establish conditional unbiasedness. The primary AppendixII uses uniform small-bias and additional dual-growth/tightness hypotheses and loses an extra reward term; merely making an arbitrary epoch long is not declared sufficient here."},
 {"clause":"state-only execution rule versus representability","decision":"semantically_approved_in_the_conditional_history-conflict_scope","reason":"If two histories with the same physical state require incompatible deterministic selector actions because their multipliers differ, one fixed state-only action distribution cannot equal both deterministic choices. This says nothing against an optimal stationary state-only policy attaining fair-coin fractions, which the last sentence correctly preserves."}
]
report={"status":"independent_source49_qualification_proposal_semantic_review_completed_revision_required","reviewer":"/root/config21_next","reviewed_at_utc":datetime.now(timezone.utc).isoformat(),"proposal":{"file":str(PROPOSAL),"sha256":PROPOSAL_SHA},"actual_checker":str(Path(__file__)),"actual_checker_sha256":sha(Path(__file__)),"mechanical_check_errors":[],"semantic_proposal_approved":False,"html_inventory_or_canonical_written":False,"exact_readonly_forward_reverse_and_inventory_binding_verified":True,"changed_inventory_text_keys":changed,"complete_original_and_proposed_records":full_records,"per_unit_decisions":[{"source_unit_key":"cmdp.html::node-1138","whole_proposal_semantics_approved":True,"formal_whole_unit_coverage_approved":False,"clauses":reasons_b,"missing_semantic_clauses":[]},{"source_unit_key":"cmdp.html::node-1141","whole_proposal_semantics_approved":False,"formal_whole_unit_coverage_approved":False,"clauses":reasons_c,"missing_semantic_clauses":["A total maximizing tie selector whose equality cases explicitly override the otherwise-return default."]}],"blocking_counterexample":{"prices":[2,2],"literal_default":"Both strict stay inequalities are false, so both regions return toR0.","R0_tie_rule_example":"Always route toR1; after the initial state this is R0,R1,R0,R1,... .","default_fraction_vector":["1/2","1/2","0"],"default_uncentered_score":"3/2","maximizing_stay_vertex":[0,1,0],"maximizing_uncentered_score":"2","default_lagrangian":"1/6","maximizing_lagrangian":"2/3","scope":"Exact mathematical counterexample to the literal default, not a new Lean compilation or a claim that the later unspecified tie clause cannot be repaired."},"concrete_valid_total_selector_suggestion":{"at_R0":"Route toward larger multiplier; when equal route toR1.","at_Ri":"Stay iff lambda_i>=max(1,lambda_j), otherwise return toR0.","tie_scope":"Equal prices above1 stay in either current region, selecting an absorbing maximizing edge representative. Unequal larger price exactly1 chooses staying in that region, a valid endpoint of its tied maximizing edge. Equal prices below1 alternate viaR0 with the fixed chosen region. At(1,1) this is one of the tied maximizing policies.","theorem1_scope":"The total fixed-price selector being maximizing does not verify finite-epoch A3; the explicit primary-theorem assumptions must remain."},"primary_source":{"file":"sources/text/2102.11941.txt","sha256":sha(PRIMARY),"version":"arXiv2102.11941v2","fully_read_scopes":["SectionII expected average definitions1,3,4, exact projected epoch update6 and Theorem1 A1-A3/equations7-9","SectionII-A Algorithms1-2 and fixed-policy-versus-trajectory caveat","AppendixII finite-rollout bias, Assumptions1-2 and Theorem3"],"source_section7_HTML_read":True},"Root_trial6_and_original_component_peer":{"peer_file":str(PEER),"peer_sha256":PEER_SHA,"original_peer_reviewed_at_utc":peer["reviewed_at_utc"],"source_file":str(proof),"source_sha256":sha(proof),"all_nine_full_theorem_bodies_read":True,"actual_original_standalone":actual,"scope":"Only the actual controlled-law/growing-path/finite-prefix components are compared. Original e7a00164 semantic decisions/time and nonempty warning log remain exact. No named or aggregate execution is inferred."},"preserved_current22_component_reviews_sha256":proposal["preserved_current22_component_reviews_sha256"],"all31_current48_assets_and1089_old_plus24_reviewed22_proof_sources_checked_exact":True,"new_dual_trajectory_pack_reviewed_or_selected":False,"whole_corrected_exercise_approved":False,"coverage_complete":False,"limits":["This is semantic approval of proposed paragraph(b) in its stated expected-value and existing-limit scopes, and a revision request for paragraph(c). It is not a source49 release, source correction, inventory update, canonical proof binding or formal whole-exercise promotion.","The new Root dual-trajectory source is still separate, in progress and outside this proposal decision. Its bodies/builds cannot be claimed from the retained standalone-only deterministic-path trial6."]}
assert sha(PROPOSAL)==PROPOSAL_SHA and sha(PEER)==PEER_SHA
assert sha(source_path)==proposal["source_sha256_before"] and sha(inventory_path)==proposal["inventory_source48_sha256"]
for name,digest in protected.items():assert sha(ROOT/name)==digest
with OUT.open("x") as output:output.write(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({"status":report["status"],"review":str(OUT),"review_sha256":sha(OUT),"node1138_semantic_approved":True,"node1141_semantic_approved":False,"exact_tie_counterexample":"lambda=(2,2), otherwise-return score3/2<stay score2"}))
