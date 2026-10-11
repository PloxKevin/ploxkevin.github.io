"""Add exact paired logs/snapshots to a NEW Foundation offer; execute no Lean."""
from datetime import datetime, timezone
import copy
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
PREVIOUS = "book/coverage/foundations-audit22-source48-additions-v2.json"
PREVIOUS_SHA = "1819751f01d42987ed868c60716e279e28d7690e64a23adcef834f9a68420eb0"
OFFER = "book/coverage/foundations-audit22-source48-additions-v3.json"
SUPPLEMENT = "book/coverage/checks/foundations-future22/foundation22-paired-log-and-source-snapshot-evidence-supplement-v1.json"
BINDING = "book/coverage/checks/root-owner22-reviewed-candidate-bindings-draft-v2.json"
BINDING_SHA = "7c601e9dd0e420d8ddac650b36fa4270497ebb4701a26d4f84bf3401b9288f50"

def sha(name):
    return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT/name).read_text())

def write_new(name,data):
    with (ROOT/name).open("x") as output:
        output.write(json.dumps(data,ensure_ascii=False,indent=2)+"\n")

assert sha(PREVIOUS)==PREVIOUS_SHA and sha(BINDING)==BINDING_SHA
old=read(PREVIOUS)
new=copy.deepcopy(old)
assert not (ROOT/OFFER).exists() and not (ROOT/SUPPLEMENT).exists()
assert old["mapped_ledger_sha256"]==sha(old["mapped_ledger"])=="305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88"
proofs=read(BINDING)["owners"]["foundations"]["new_immutable_proof_sources"]
assert set(proofs)==set(old["proof_files"]) and len(proofs)==5
closures={}
for name,pair in proofs.items():
    digest=pair["sha256"]
    assert sha(name)==new["proof_files"][name]["sha256"]==digest
    assert len(pair["actual_pair"])==2
    additions={}
    original_records={}
    for ref in pair["actual_pair"]:
        assert sha(ref["file"])==ref["sha256"]==old["proof_files"][name]["evidence_sha256"][ref["file"]]
        execution=read(ref["file"])
        exits=[execution[field] for field in ["exit_code","actual_exit_code"] if field in execution]
        assert exits and all(type(code) is int and code==0 for code in exits)
        assert execution["source"]==name and execution["source_sha256_before"]==execution["source_sha256_after"]==digest
        log=ref["canonical_raw_log"]
        assert sha(log["file"])==log["sha256"]==execution["log_sha256"]
        additions[log["file"]]=log["sha256"]
        preserved=execution.get("preserved_source",execution.get("source_snapshot"))
        preserved_sha=execution.get("preserved_source_sha256",execution.get("source_snapshot_sha256"))
        if preserved is not None:
            assert preserved_sha==digest==sha(preserved)
            additions[preserved]=digest
        original_records[ref["file"]]=ref["sha256"]
    assert len([p for p in additions if p.endswith(".log")])==2
    assert len([p for p in additions if p.endswith(".lean")])==1
    new["proof_files"][name]["evidence_sha256"].update(additions)
    closures[name]={"canonical_source_sha256":digest,"unchanged_actual_paired_record_sha256":original_records,"added_raw_log_and_snapshot_sha256":additions}
    restored=copy.deepcopy(new["proof_files"][name])
    for p in additions:
        del restored["evidence_sha256"][p]
    assert restored==old["proof_files"][name]
restored=copy.deepcopy(new)
restored["proof_files"]=copy.deepcopy(old["proof_files"])
assert restored==old
supplement={"status":"exact_existing_foundation22_paired_log_and_source_snapshot_evidence_closure_passed","prepared_at_utc":datetime.now(timezone.utc).isoformat(),"actual_helper":str(Path(__file__).relative_to(ROOT)),"actual_helper_sha256":sha(str(Path(__file__).relative_to(ROOT))),"previous_exact_offer":{"file":PREVIOUS,"sha256":PREVIOUS_SHA},"unchanged_candidate_ledger":{"file":old["mapped_ledger"],"sha256":old["mapped_ledger_sha256"]},"original_proof_and_semantic_fields_retained":True,"original_offer_prepared_time_retained":old["prepared_at_utc"],"new_lean_execution":False,"proof_evidence_closures":closures,"added_raw_logs":10,"added_source_snapshots":5,"scope":"Only exact existing raw log and source snapshot aliases are added to a new offer. All reviewed candidate bytes, original offer fields/times, original mathematical reviews, compiler records/logs and proof sources remain unchanged."}
write_new(SUPPLEMENT,supplement)
new["previous_exact_owner_offer"]={"file":PREVIOUS,"sha256":PREVIOUS_SHA}
new["paired_raw_log_and_source_snapshot_evidence_supplement"]={"file":SUPPLEMENT,"sha256":sha(SUPPLEMENT)}
new["evidence_closure_added_at_utc"]=datetime.now(timezone.utc).isoformat()
write_new(OFFER,new)
assert sha(PREVIOUS)==PREVIOUS_SHA and sha(BINDING)==BINDING_SHA
print(json.dumps({"status":"passed_exact_existing_evidence_closure_only","offer":{"file":OFFER,"sha256":sha(OFFER)},"supplement":{"file":SUPPLEMENT,"sha256":sha(SUPPLEMENT)},"candidate_ledger_sha256":old["mapped_ledger_sha256"],"new_lean_execution":False}))
