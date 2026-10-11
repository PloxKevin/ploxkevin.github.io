"""Read-only independent review of the prepared literal Pages 21 config.

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
OUT = ROOT / "book/coverage/checks/pages21-config-independent-foundations-review-v1.json"
FAIL = ROOT / "book/coverage/checks/pages21-config-independent-foundations-failure-v1.json"
PREVIOUS_SHA = "5240887696b71ede4f92468c459116dcd874de7ba3e870ef300bd4ad1d30ae82"
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
    preparation_path = REPORTS / "pages21-config-preparation-v1.json"
    preparation = read(preparation_path)
    preparation_execution_path = REPORTS / "pages21-config-execution-v1.json"
    preparation_execution = read(preparation_execution_path)
    preparation_log_path = REPORTS / "pages21-config-execution-v1.log"
    preparation_helper_path = ROOT / "book/coverage/checks/root_prepare_pages21_config_v1.py"
    assert preparation_execution["status"] == "passed"
    assert preparation_execution["actual_exit_code"] == 0
    assert preparation_execution["actual_command"] == ["python3", "book/coverage/checks/root_prepare_pages21_config_v1.py"]
    assert preparation_log_path.is_file()
    assert sha(preparation_helper_path) == "ff2b1babc4720c4d3a8a3744d85742f32fe2719f48d9510d4438fbd1a41f7145"
    config = PUB / "_config.yml"
    config_sha = sha(config)
    excludes = parse_literal_config(config)
    previous_path = REPORTS / "pages21-config-previous-original-v1.yml"
    assert sha(previous_path) == PREVIOUS_SHA
    previous_excludes = parse_literal_config(previous_path)
    assert preparation["previous_config"] == previous_path.relative_to(ROOT).as_posix()
    assert preparation["previous_config_sha256"] == PREVIOUS_SHA
    assert preparation["config_sha256"] == config_sha
    assert preparation["exclusions"] == excludes
    assert preparation["excluded_count"] == len(excludes)
    inventory_archives = {
        path.relative_to(PUB).as_posix()
        for path in (PUB / "book/coverage").iterdir()
        if path.is_file() and re.fullmatch(r"inventory.*\.json", path.name)
        and path.name != "inventory.json"
    }
    expected_excludes = set(previous_excludes) | inventory_archives | {
        "reports/full-coverage/checkpoint-21"
    }
    assert set(excludes) == expected_excludes

    def excluded(name):
        parts = PurePosixPath(name).parts
        return any(PurePosixPath(entry).parts == parts[:len(PurePosixPath(entry).parts)]
                   for entry in excludes)

    manifest_path = REPORTS / "checkpoint-21-manifest.json"
    selection_path = REPORTS / "checkpoint-21-selection.json"
    manifest = read(manifest_path)
    selection = read(selection_path)
    assert manifest["status"] == "formal_verification_passed_partial_coverage"
    assert manifest["coverage_complete"] is False
    assert len(manifest["proof_files"]) == selection["proof_file_count"] == 1089
    assert set(manifest["proof_files"]) == set(selection["proof_files"])
    assert sha(selection_path) == manifest["selection_sha256"]
    frozen = manifest["frozen_inputs_sha256"]
    assets = {name: digest for name, digest in frozen.items() if name.startswith("SafeLearning/")}
    assert len(assets) == 31
    assert preparation["exact_frozen_assets"] == assets
    exact_current = dict(assets)
    for name in ["book/coverage/inventory.json"] + [
        "book/coverage/" + owner + ".json" for owner in ("foundations", "applied", "modules", "core")
    ]:
        exact_current[name] = frozen[name]
    current_rows = []
    for name, expected in sorted(exact_current.items()):
        assert not excluded(name), name
        published = PUB / name
        snapshot = REPORTS / "checkpoint-21" / name
        assert published.is_file() and not published.is_symlink(), name
        assert sha(published) == sha(snapshot) == expected, name
        current_rows.append({"path": name, "sha256": expected, "excluded": False})

    actual_paths = [
        "reports/full-coverage/README.md",
        "reports/full-coverage/integration-21.json",
        "reports/full-coverage/browser-checkpoint-21.json",
        "reports/full-coverage/checkpoint-21-manifest.json",
        "reports/full-coverage/checkpoint-21-selection.json",
        "reports/full-coverage/lean-checkpoint-21/verification-original.json",
        "reports/full-coverage/lean-checkpoint-21/verification.json",
        "reports/full-coverage/lean-checkpoint-21/ledger-audit.json",
    ]
    actual_rows = []
    for name in actual_paths:
        assert not excluded(name), name
        assert (PUB / name).is_file() and not (PUB / name).is_symlink(), name
        assert sha(PUB / name) == sha(ROOT / name), name
        actual_rows.append({"path": name, "sha256": sha(PUB / name), "excluded": False})
    assert set(preparation["required_published_paths"]) == set(exact_current) | set(actual_paths)
    assert not excluded("book/coverage/progress.json")
    audit = read(ROOT / actual_paths[5])
    assert audit["status"] == "passed" and audit["proof_file_count"] == 1089
    assert audit["theorem_count"] >= 8821
    assert audit["checks"] and all(check["exit_code"] == 0 for check in audit["checks"])

    archive = {
        name: digest for name, digest in frozen.items()
        if name.startswith("book/coverage/checks/future22-monitoring/")
    }
    assert len(archive) == 32
    assert not any("Monitoring" in name or "future22" in name for name in manifest["proof_files"])
    trial_rows = []
    for name, expected in sorted(archive.items()):
        assert name not in manifest["proof_files"] and name not in selection["proof_files"]
        assert excluded(name), name
        for base in (ROOT, PUB, REPORTS / "checkpoint-21"):
            assert (base / name).is_file() and not (base / name).is_symlink(), (str(base), name)
            assert sha(base / name) == expected, (str(base), name)
        trial_rows.append({"path": name, "sha256": expected, "selected_proof": False, "excluded": True})
    historical_unselected = manifest["excluded_working_proof_files"]
    assert len(historical_unselected) == 15
    assert not set(historical_unselected) & set(manifest["proof_files"])
    working_proofs = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "verification/lean/SafeLearning").glob("*.lean")
    }
    working_unselected = sorted(working_proofs - set(manifest["proof_files"]))
    assert all(excluded(name) for name in working_unselected)
    for suffix in ("CompleteMonitoringAchievable22.lean", "CompleteMonitoringFaces22.lean"):
        name = "verification/lean/SafeLearning/" + suffix
        assert name not in frozen and name not in manifest["proof_files"]

    included_bytes = excluded_bytes = included_count = excluded_count = 0
    for dirname, directories, filenames in os.walk(PUB, followlinks=False):
        directories[:] = [name for name in directories if name != ".git"]
        for name in directories:
            path = Path(dirname) / name
            relative = path.relative_to(PUB).as_posix()
            if not excluded(relative):
                assert not path.is_symlink(), relative
        for filename in filenames:
            path = Path(dirname) / filename
            if not path.is_file():
                continue
            relative = path.relative_to(PUB).as_posix()
            if excluded(relative):
                excluded_bytes += path.stat().st_size
                excluded_count += 1
            else:
                assert not path.is_symlink(), relative
                included_bytes += path.stat().st_size
                included_count += 1
    assert included_bytes < 900_000_000
    assert sha(config) == config_sha, "Config changed during review"
    report = {
        "status": "independent_literal_pages21_exclusions_exact_frozen_content_and_budget_review_passed",
        "reviewed_by": "/root/config21_next",
        "started_at_utc": START,
        "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
        "actual_checker": Path(__file__).relative_to(ROOT).as_posix(),
        "actual_checker_sha256": sha(Path(__file__)),
        "actual_check_exit_code": 0,
        "preparation_record": preparation_path.relative_to(ROOT).as_posix(),
        "preparation_record_sha256": sha(preparation_path),
        "actual_preparation_execution_record": preparation_execution_path.relative_to(ROOT).as_posix(),
        "actual_preparation_execution_record_sha256": sha(preparation_execution_path),
        "actual_preparation_log": preparation_log_path.relative_to(ROOT).as_posix(),
        "actual_preparation_log_sha256": sha(preparation_log_path),
        "actual_preparation_helper_sha256": sha(preparation_helper_path),
        "config": config.relative_to(ROOT).as_posix(),
        "config_sha256": config_sha,
        "previous_config": previous_path.relative_to(ROOT).as_posix(),
        "previous_config_sha256": PREVIOUS_SHA,
        "parse_scope": "Only comments, the single exclude key and unique sorted plain relative literal paths are accepted; no wildcards, include override or other YAML directives.",
        "exclusions": excludes,
        "new_exclusions": sorted(set(excludes) - set(previous_excludes)),
        "frozen31_assets_and_inventory_and_four_ledgers": current_rows,
        "actual21_published_audit_paths": actual_rows,
        "actual21_audit": {"status": audit["status"], "proof_files": audit["proof_file_count"], "theorems": audit["theorem_count"], "all_actual_check_exit_codes_zero": True},
        "archival32_future22_trials": trial_rows,
        "historical15_unselected_proofs": historical_unselected,
        "working_unselected_canonical_proofs_at_review": working_unselected,
        "included_source_file_count": included_count,
        "included_source_bytes": included_bytes,
        "preparation_included_source_bytes": preparation["included_file_bytes"],
        "measurement_difference_bytes": included_bytes - preparation["included_file_bytes"],
        "excluded_file_count": excluded_count,
        "excluded_file_bytes": excluded_bytes,
        "budget_limit_bytes": 900_000_000,
        "coverage_complete": False,
        "limits": [
            "This approves the current exact config and an independently measured source-file budget. The generated Pages artifact and actual deployment require their own checks.",
            "The 32 archived monitoring trial files are retained byte exactly in the working tree, frozen snapshot and publication repository; none is selected as one of the 1089 audited proofs.",
            "The 15 frozen excluded_working_proof_files entries are the historical freeze-time list. Later canonical future22 work remains outside the held checkpoint21 selected and frozen inputs.",
            "This checker changed only its own review output, and did not execute Lean, change held assets or replace any original execution log or failure.",
        ],
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "config_sha256": config_sha, "included_source_bytes": included_bytes, "exact_frozen_assets": len(assets), "archival_future22_files": len(archive)}))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        failure = traceback.format_exc()
        if not FAIL.exists():
            FAIL.write_text(json.dumps({"status": "failed", "started_at_utc": START, "failed_at_utc": datetime.now(timezone.utc).isoformat(), "actual_checker": Path(__file__).relative_to(ROOT).as_posix(), "actual_checker_sha256": sha(Path(__file__)), "failure": failure}, indent=2) + "\n")
        sys.stderr.write(failure)
        sys.exit(1)
