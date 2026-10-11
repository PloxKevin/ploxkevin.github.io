"""Read-only independent review of the prepared literal Pages 22 config.

Only this review's JSON (or an original failure JSON) is written. No build or
deployment is inferred from this source selection and byte-budget check.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
import traceback

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / "reports/book/publication-repo"
REPORTS = ROOT / "reports/full-coverage"
OUT = ROOT / "book/coverage/checks/pages22-config-independent-foundations-review-v2.json"
FAIL = ROOT / "book/coverage/checks/pages22-config-independent-foundations-failure-v2.json"
PREVIOUS_SHA = "410746b5dbe55b9f760aeabd0939dfc791bfcf59a598b4e7f3d84e1381999bc2"
START = datetime.now(timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def parse_literal_config(path):
    """Accept just comments, one exclude map key, and plain literal paths."""
    lines = path.read_text(encoding="utf-8").splitlines()
    significant = [line for line in lines if line and not line.startswith("#")]
    assert significant and significant[0] == "exclude:", significant[:1]
    entries = []
    for line in significant[1:]:
        match = re.fullmatch(r"  - ([A-Za-z0-9][A-Za-z0-9/_.-]*)", line)
        assert match, (str(path), line)
        name = match.group(1)
        parts = PurePosixPath(name).parts
        assert name == PurePosixPath(name).as_posix()
        assert not name.startswith("/") and ".." not in parts and "." not in parts
        assert not any(char in name for char in "*?[]{}\\!&:#'\"`%")
        entries.append(name)
    assert len(set(entries)) == len(entries)
    assert entries == sorted(entries)
    return entries


def main():
    assert not OUT.exists() and not FAIL.exists(), "Preserve prior review/failure files"
    preparation_path=REPORTS/"pages22-config-preparation-v2.json"
    preparation=read(preparation_path)
    execution_path=REPORTS/"pages22-config-execution-v2.json"
    execution=read(execution_path)
    log_path=REPORTS/"pages22-config-execution-v2.log"
    helper_name="book/coverage/checks/root_prepare_pages22_config_v2.py"
    helper=ROOT/helper_name
    helper_sha="c79e18cd7a3f724f04003b3d7ce3793d13cbb141475f693f9a5c61a3527e9867"
    assert execution["status"]=="passed" and execution["actual_exit_code"]==0
    assert execution.get("actual_command",execution.get("command"))==["python3",helper_name]
    assert execution["actual_workdir"]==str(ROOT)
    assert sha(helper)==helper_sha==preparation["actual_helper_sha256"]
    assert execution["helper_sha256_before"]==execution["helper_sha256_after"]=={helper_name:helper_sha}
    assert sha(log_path)==execution["log_sha256"]
    config=PUB/"_config.yml"
    config_sha=sha(config)
    excludes=parse_literal_config(config)
    previous_path=REPORTS/"pages22-config-previous-original-v2.yml"
    assert sha(previous_path)==PREVIOUS_SHA
    previous_excludes=parse_literal_config(previous_path)
    previous_review=read(ROOT/"book/coverage/checks/pages21-config-independent-foundations-review-v1.json")
    assert "passed" in previous_review["status"] and previous_review["config_sha256"]==PREVIOUS_SHA
    assert preparation["previous_config"]==previous_path.relative_to(ROOT).as_posix()
    assert preparation["previous_config_sha256"]==PREVIOUS_SHA
    assert preparation["config_sha256"]==config_sha
    assert preparation["exclusions"]==excludes and preparation["excluded_count"]==len(excludes)
    inventory_archives={path.relative_to(PUB).as_posix() for path in (PUB/"book/coverage").iterdir() if path.is_file() and re.fullmatch(r"inventory.*\.json",path.name) and path.name!="inventory.json"}
    expected=set(previous_excludes)|inventory_archives|{"reports/full-coverage/checkpoint-22","reports/full-coverage/owner21-originals-before-owner22-integration-v1"}
    assert set(excludes)==expected

    def excluded(name):
        parts=PurePosixPath(name).parts
        return any(PurePosixPath(entry).parts==parts[:len(PurePosixPath(entry).parts)] for entry in excludes)

    manifest_path=REPORTS/"checkpoint-22-manifest.json"
    selection_path=REPORTS/"checkpoint-22-selection.json"
    manifest=read(manifest_path)
    selection=read(selection_path)
    old_manifest_path=REPORTS/"checkpoint-21-manifest.json"
    assert sha(old_manifest_path)=="f5d27edc32eb5d952b1cfc92424f3ab6399dd37586885b59e15fee6028184010"
    old_manifest=read(old_manifest_path)
    assert manifest["status"]=="formal_verification_passed_partial_coverage" and manifest["coverage_complete"] is False
    assert len(manifest["proof_files"])==selection["proof_file_count"]==1113
    assert set(manifest["proof_files"])==set(selection["proof_files"])
    assert sha(selection_path)==manifest["selection_sha256"]
    assert len(old_manifest["proof_files"])==1089 and len(old_manifest["frozen_inputs_sha256"])==32040
    bindings_path=ROOT/"book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json"
    assert sha(bindings_path)=="8b39f77d1f8ead44b6b20d6a759434173b61c852a871a0b6805923c0d4c29b7f"
    bindings=read(bindings_path)
    new_sources=bindings["new_immutable_proof_sources_sha256"]
    assert len(new_sources)==24
    assert set(manifest["proof_files"])==set(old_manifest["proof_files"])|set(new_sources)
    for name,row in old_manifest["proof_files"].items():
        assert sha(ROOT/name)==row["sha256"]==manifest["proof_files"][name]["sha256"]
    for name,digest in new_sources.items():
        assert sha(ROOT/name)==digest==manifest["proof_files"][name]["sha256"]
    assets={name:digest for name,digest in manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
    old_assets={name:digest for name,digest in old_manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")}
    assert len(assets)==31 and assets==old_assets==preparation["exact_current48_assets"]
    exact_current=dict(assets)
    inventory="book/coverage/inventory.json"
    exact_current[inventory]="2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108"
    assert sha(ROOT/"book/coverage/inventory-after-correction48.json")==exact_current[inventory]
    ledger_scopes=[]
    ledger_paths=set()
    expected_removed=["verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean", "verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean", "verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean"]
    for owner in ("foundations","applied","modules","core"):
        name="book/coverage/"+owner+".json"
        ledger_paths.add(name)
        working_digest=manifest["working_inputs_sha256"][name]
        frozen_digest=manifest["frozen_inputs_sha256"][name]
        assert sha(ROOT/name)==working_digest==bindings["owners"][owner]["candidate_ledger"]["sha256"]
        assert sha(PUB/name)==sha(REPORTS/"checkpoint-22"/name)==frozen_digest
        working=read(ROOT/name)
        published=read(PUB/name)
        removed=manifest["excluded_unreferenced_ledger_metadata"][owner]
        assert removed==(expected_removed if owner=="applied" else [])
        assert set(working["proof_files"])-set(manifest["proof_files"])==set(removed)
        listed=working["proof_files"]
        working["proof_files"]=([n for n in listed if n not in removed] if isinstance(listed,list) else {n:v for n,v in listed.items() if n not in removed})
        if "proof_sha256" in working:
            assert set(working["proof_sha256"])-set(manifest["proof_files"])==set(removed)
            working["proof_sha256"]={n:v for n,v in working["proof_sha256"].items() if n not in removed}
        assert working==published==read(REPORTS/"checkpoint-22"/name),name
        exact_current[name]=frozen_digest
        ledger_scopes.append({"path":name,"working_sha256":working_digest,"published_frozen_sha256":frozen_digest,"only_removed_metadata_proof_rows":removed,"all_other_full_json_fields_exact":True})
    assert preparation["working_owner_ledger_sha256"]=={r["path"]:r["working_sha256"] for r in ledger_scopes}
    assert preparation["excluded_unreferenced_ledger_metadata"]==manifest["excluded_unreferenced_ledger_metadata"]
    original_checker=ROOT/"book/coverage/checks/pages22-config-independent-foundations-check-v1.py"
    assert sha(original_checker)=="9fd7db0638c002cd8b4a3e2fe39883233f40046f3403e339f4d668c16141dd8e"
    original_helper=ROOT/"book/coverage/checks/root_prepare_pages22_config_v1.py"
    assert sha(original_helper)=="8d0eaf460c1ad7e12941d8747ad68898a5b5708007a80b7974934aa35512f6d8"
    original_execution_path=REPORTS/"pages22-config-execution-v1.json"
    original_execution=read(original_execution_path)
    original_log=REPORTS/"pages22-config-execution-v1.log"
    assert original_execution["status"]=="failed" and original_execution["actual_exit_code"]==1
    assert sha(original_log)==original_execution["log_sha256"]=="761e3957f68301de90b19e61e7a5cca9161deac2f782846a9b7508bb0b9cd5f2"
    original_history={"unexecuted_original_checker":original_checker.relative_to(ROOT).as_posix(),"unexecuted_original_checker_sha256":sha(original_checker),"failed_preparation_helper":original_helper.relative_to(ROOT).as_posix(),"failed_preparation_helper_sha256":sha(original_helper),"actual_failed_preparation_execution":original_execution_path.relative_to(ROOT).as_posix(),"actual_failed_preparation_execution_sha256":sha(original_execution_path),"actual_failed_preparation_log":original_log.relative_to(ROOT).as_posix(),"actual_failed_preparation_log_sha256":sha(original_log),"actual_failed_preparation_exit_code":1}
    current_rows=[]
    for name,digest in sorted(exact_current.items()):
        assert not excluded(name)
        assert (PUB/name).is_file() and not (PUB/name).is_symlink()
        assert sha(PUB/name)==digest
        if name not in ledger_paths:assert sha(ROOT/name)==digest
        current_rows.append({"path":name,"sha256":digest,"excluded":False})
    actual_paths=["reports/full-coverage/README.md","reports/full-coverage/integration-22.json","reports/full-coverage/browser-checkpoint-22.json","reports/full-coverage/checkpoint-22-manifest.json","reports/full-coverage/checkpoint-22-selection.json","reports/full-coverage/lean-checkpoint-22/verification-original.json","reports/full-coverage/lean-checkpoint-22/verification.json","reports/full-coverage/lean-checkpoint-22/ledger-audit.json","reports/full-coverage/owner22-reviewed-candidate-integration-v1.json"]
    actual_rows=[]
    for name in actual_paths:
        assert not excluded(name) and (PUB/name).is_file() and not (PUB/name).is_symlink()
        if name!="reports/full-coverage/README.md":assert sha(PUB/name)==sha(ROOT/name),name
        assert sha(PUB/name)==preparation["required_published_sha256"][name],name
        actual_rows.append({"path":name,"sha256":sha(PUB/name),"excluded":False})
    assert set(preparation["required_published_paths"])==set(exact_current)|set(actual_paths)
    assert {row["path"]:row["sha256"] for row in current_rows+actual_rows}==preparation["required_published_sha256"]
    assert not excluded("book/coverage/progress.json")
    audit=read(ROOT/actual_paths[5])
    assert audit["status"]=="passed" and audit["proof_file_count"]==1113
    assert audit["checks"] and all(check["exit_code"]==0 for check in audit["checks"])
    integration=read(ROOT/actual_paths[-1])
    assert integration["applied"] is True
    assert integration["binding_manifest_sha256"]==sha(bindings_path)
    assert len(integration["exact_replacements"])==5
    assert integration["all32040_frozen21_inputs_exact"] and integration["all1089_selected21_root_source_hashes_exact"] and integration["all31_current48_safelearning_assets_exact"]
    archive={name:digest for name,digest in old_manifest["frozen_inputs_sha256"].items() if name.startswith("book/coverage/checks/future22-monitoring/")}
    assert len(archive)==32
    trial_rows=[]
    for name,digest in sorted(archive.items()):
        assert name not in manifest["proof_files"] and name not in selection["proof_files"] and excluded(name)
        for base in (ROOT,PUB,REPORTS/"checkpoint-21"):
            assert (base/name).is_file() and not (base/name).is_symlink()
            assert sha(base/name)==digest
        trial_rows.append({"path":name,"sha256":digest,"selected_proof":False,"excluded":True})
    working_proofs={p.relative_to(ROOT).as_posix() for p in (ROOT/"verification/lean/SafeLearning").glob("*.lean")}
    working_unselected=sorted(working_proofs-set(manifest["proof_files"]))
    assert all(excluded(name) for name in working_unselected)
    included_bytes=excluded_bytes=included_count=excluded_count=0
    for dirname,directories,filenames in os.walk(PUB,followlinks=False):
        directories[:]=[name for name in directories if name!=".git"]
        for name in directories:
            path=Path(dirname)/name
            if not excluded(path.relative_to(PUB).as_posix()):assert not path.is_symlink()
        for name in filenames:
            path=Path(dirname)/name
            if not path.is_file():continue
            relative=path.relative_to(PUB).as_posix()
            if excluded(relative):
                excluded_bytes+=path.stat().st_size;excluded_count+=1
            else:
                assert not path.is_symlink()
                included_bytes+=path.stat().st_size;included_count+=1
    assert included_bytes<900_000_000
    assert audit["theorem_count"]==9002
    assert len(excludes)==52
    assert config_sha=="443a2c117d1caf7d3d0236235b15af1cafc48cfd60ab8f9b60ef5a9c7909e41a"
    assert sha(config)==config_sha
    report={"status":"independent_literal_pages22_config_exact_reviewed_owner_content_and_budget_review_passed","reviewed_by":"/root/config21_next","started_at_utc":START,"reviewed_at_utc":datetime.now(timezone.utc).isoformat(),"actual_checker":Path(__file__).relative_to(ROOT).as_posix(),"actual_checker_sha256":sha(Path(__file__)),"actual_check_exit_code":0,"config_sha256":config_sha,"previous_config_sha256":PREVIOUS_SHA,"config":config.relative_to(ROOT).as_posix(),"previous_config":previous_path.relative_to(ROOT).as_posix(),"preparation_record":preparation_path.relative_to(ROOT).as_posix(),"preparation_record_sha256":sha(preparation_path),"actual_preparation_execution_record":execution_path.relative_to(ROOT).as_posix(),"actual_preparation_execution_record_sha256":sha(execution_path),"actual_preparation_raw_log":log_path.relative_to(ROOT).as_posix(),"actual_preparation_raw_log_sha256":sha(log_path),"actual_preparation_helper_sha256":helper_sha,"four_ledger_working_and_published_frozen_scopes":ledger_scopes,"original_failure_and_unexecuted_checker_history":original_history,"exclusions":excludes,"new_exclusions":sorted(set(excludes)-set(previous_excludes)),"current31_assets_inventory_and_four_reviewed22_ledgers":current_rows,"actual22_published_audit_paths":actual_rows,"actual22_audit":{"status":audit["status"],"proof_files":audit["proof_file_count"],"theorems":audit["theorem_count"],"all_actual_check_exit_codes_zero":True},"archival32_frozen21_future22_trial_files":trial_rows,"all1089_inherited21_source_hashes_exact":True,"new24_reviewed_source_hashes_exact":True,"working_unselected_proofs_at_review":working_unselected,"included_source_file_count":included_count,"included_source_bytes":included_bytes,"preparation_included_source_bytes":preparation["included_file_bytes"],"measurement_difference_bytes":included_bytes-preparation["included_file_bytes"],"excluded_file_count":excluded_count,"excluded_source_bytes":excluded_bytes,"budget_limit_bytes":900_000_000,"coverage_complete":False,"limits":["This reviews exact current config, included source assets and actual22 report bytes, and independently measured source-file budget. Actual generated Pages artifact, workflow and deployment require separate checks.","All32 frozen21 archival monitoring trial files remain exact and unselected as canonical proof paths. New24 canonical reviewed sources are distinct paths; historical15 unselected21 names are freeze-time provenance.","No Lean/build/deployment is executed by this checker. The checker writes only its unique review or original failure output; original helpers, configs, proofs, peer times and actual logs stay unchanged."]}
    with OUT.open("x") as output:output.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":report["status"],"config_sha256":config_sha,"included_source_bytes":included_bytes,"current_assets":len(assets),"archival_files":len(archive),"proof_count":1113}))

if __name__ == "__main__":
    try:
        main()
    except Exception:
        failure = traceback.format_exc()
        if not FAIL.exists():
            FAIL.write_text(json.dumps({"status": "failed", "started_at_utc": START, "failed_at_utc": datetime.now(timezone.utc).isoformat(), "actual_checker": Path(__file__).relative_to(ROOT).as_posix(), "actual_checker_sha256": sha(Path(__file__)), "failure": failure}, indent=2) + "\n")
        sys.stderr.write(failure)
        sys.exit(1)
