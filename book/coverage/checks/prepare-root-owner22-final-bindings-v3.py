"""Create exact all-four owner release bindings; never install owner bytes."""
import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
DRAFT="book/coverage/checks/root-owner22-reviewed-candidate-bindings-draft-v2.json"
DRAFT_SHA="7c601e9dd0e420d8ddac650b36fa4270497ebb4701a26d4f84bf3401b9288f50"
DEST="book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json"
HELPER="book/coverage/checks/root_integrate_owner22_candidates_v2.py"
HELPER_SHA="e7ccbb0dcdf10903cc4c028d52b303874a3e281fde20fe95e68779ec441fdd57"
FOUNDATION="book/coverage/foundations-audit22-source48-additions-v3.json"
FOUNDATION_SHA="c08b048a3ec9cb9fbf06fa45e68f6503c3f4daaeab561140dbe6c13fe5b17638"
MODULE="book/coverage/checks/modules-future22/source48/modules-audit22-candidate-source48-additions-v4-reviewed.json"
MODULE_SHA="2a8b3a66b5c3112f53b18b89f294474c87b97070f7e514374d9b06280e0fb644"

def sha(name):
    return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT/name).read_text())

def ref(name):
    return {"file":name,"sha256":sha(name)}

def checked(row):
    assert sha(row["file"])==row["sha256"],row["file"]
    return read(row["file"])

def get(data,keys):
    for k in keys:data=data[k]
    return data

parser=argparse.ArgumentParser()
parser.add_argument("helper_peer")
parser.add_argument("selector_schema_peer")
args=parser.parse_args()
assert sha(DRAFT)==DRAFT_SHA and sha(HELPER)==HELPER_SHA
assert sha(FOUNDATION)==FOUNDATION_SHA and sha(MODULE)==MODULE_SHA
assert not (ROOT/DEST).exists()
d=read(DRAFT)
d["created_at_utc"]=datetime.now(timezone.utc).isoformat()
d["status"]="all_four_reviewed_current48_owner_candidates_bound_ready_for_root_execution"
d["previous_exact_draft_v2"]=ref(DRAFT)
d["independent_helper_review"]=ref(args.helper_peer)
helper_peer=checked(d["independent_helper_review"])
assert "passed" in helper_peer["status"] and helper_peer.get("errors",[])==[]
assert helper_peer["helper_sha256"]==HELPER_SHA
d["independent_selector_paired_evidence_schema_review"]=ref(args.selector_schema_peer)
selector_peer=checked(d["independent_selector_paired_evidence_schema_review"])
assert "passed" in selector_peer["status"] and selector_peer.get("errors",[])==[]
f=d["owners"]["foundations"]
f["reviewed_final_offer"]=ref(FOUNDATION)
foundation=read(FOUNDATION)
assert foundation["mapped_ledger_sha256"]==f["candidate_ledger"]["sha256"]
f["additional_exact_provenance"].extend([foundation["previous_exact_owner_offer"],foundation["paired_raw_log_and_source_snapshot_evidence_supplement"],ref("book/coverage/checks/foundations-future22/foundation22-paired-log-evidence-supplement-execution-v1.json"),ref("book/coverage/checks/foundations-future22/foundation22-paired-log-evidence-supplement-execution-v1.log")])
m=d["owners"]["modules"]
module=read(MODULE)
m["ready"]=True
m.pop("pending_new_module_combined_candidate_version",None)
m["reviewed_final_offer"]=ref(MODULE)
m["candidate_ledger"]={"file":module["module_ledger"],"sha256":module["module_ledger_sha256"]}
m["independent_candidate_mapping_peer"]={k:v for k,v in module["independent_final_candidate_mapping_peer"].items() if k in ["file","sha256"]}
m["peer_candidate_path_pointer"]=["candidate_ledger","file"]
m["peer_candidate_sha256_pointer"]=["candidate_ledger","sha256"]
m["actual_candidate_builder"]={k:v for k,v in module["actual_builder"].items() if k in ["file","sha256"]}
m["original_full_source_semantic_reviews"]=[]
for original in module["original_full_source_reviews"]:
    semantic=checked(original)
    time=semantic.get("reviewed_at_utc",semantic.get("checked_at_utc"))
    assert time==original["original_review_time"]
    m["original_full_source_semantic_reviews"].append({"file":original["file"],"sha256":original["sha256"],"original_review_time":time,"original_review_status":semantic["status"]})
m["new_immutable_proof_sources"]={name:{"sha256":row["sha256"],"actual_pair":[]} for name,row in module["proof_files"].items()}
for key in ["actual_new_standalone_evidence","actual_new_named_evidence"]:
    for actual in module[key]:
        record={k:actual["record"][k] for k in ["file","sha256"]}
        execution=checked(record)
        name=execution["source"]
        assert name in m["new_immutable_proof_sources"]
        log=actual["raw_log"]
        record.update(canonical_raw_log={"file":log.get("file",log.get("path")),"sha256":log["sha256"]},actual_source=name,actual_command=execution["command"],actual_workdir=execution["actual_workdir"])
        m["new_immutable_proof_sources"][name]["actual_pair"].append(record)
m["additional_exact_provenance"].extend([{k:v for k,v in r.items() if k in ["file","sha256"]} for r in module["canonical_path_alias_manifests"]]+[module["current_identity_binding_validation"],module["previous_candidate_offer"],ref("book/coverage/checks/modules-future22/source48/modules-audit22-candidate-source48-additions-v3.json")])
new_sources={}
for owner,row in d["owners"].items():
    assert row["ready"] is True
    assert sha(row["held21_ledger"])==row["held21_ledger_sha256"]
    candidate=checked(row["candidate_ledger"])
    offer=checked(row["reviewed_final_offer"])
    peer=checked(row["independent_candidate_mapping_peer"])
    assert "passed" in peer["status"] and peer.get("errors",[])==[]
    assert get(offer,row["offer_candidate_path_pointer"])==get(peer,row["peer_candidate_path_pointer"])==row["candidate_ledger"]["file"]
    assert get(offer,row["offer_candidate_sha256_pointer"])==get(peer,row["peer_candidate_sha256_pointer"])==row["candidate_ledger"]["sha256"]
    assert set(row["new_immutable_proof_sources"])==set(offer["proof_files"])
    for name,proof in row["new_immutable_proof_sources"].items():
        assert sha(name)==proof["sha256"]==offer["proof_files"][name]["sha256"]
        assert name not in new_sources
        new_sources[name]=proof["sha256"]
        assert len(proof["actual_pair"])==2
        for r in proof["actual_pair"]:
            ex=checked(r)
            exits=[ex[k] for k in ["exit_code","actual_exit_code"] if k in ex]
            assert exits and all(type(code) is int and code==0 for code in exits)
            assert ex["source"]==r["actual_source"]==name
            assert ex["command"]==r["actual_command"] and ex["actual_workdir"]==r["actual_workdir"]
            assert ex["source_sha256_before"]==ex["source_sha256_after"]==proof["sha256"]
            assert sha(r["canonical_raw_log"]["file"])==r["canonical_raw_log"]["sha256"]==ex["log_sha256"]
    for r in row["additional_exact_provenance"]:assert sha(r["file"])==r["sha256"]
assert len(new_sources)==24
assert d["owners"]["core"]["reviewed_final_offer"]["sha256"]=="50db7080053e3bdb596cd92a440dfaf5ac800d656719c247856904811435d491"
d["release_requirements"][0]="Complete exact final bindings are ready for Root's actual default read-only preflight and explicit --apply. Root must preserve actual execution JSON/raw log and produce NEW live owner interfaces; candidate builder provenance remains historical."
d["new_immutable_proof_sources_sha256"]=new_sources
d["expected_selected_proof_file_count_after_release"]=1113
d["final_binding_preparation_helper"]=ref(str(Path(__file__).relative_to(ROOT)))
d["owner_ledgers_mutated_by_binding_preparation"]=False
with (ROOT/DEST).open("x") as output:output.write(json.dumps(d,ensure_ascii=False,indent=2)+"\n")
assert sha(DRAFT)==DRAFT_SHA and sha(HELPER)==HELPER_SHA
print(json.dumps({"status":"all_four_final_bindings_prepared_no_owner_mutation","binding":{"file":DEST,"sha256":sha(DEST)},"new_immutable_sources":len(new_sources),"expected_selected_proofs":1113}))
