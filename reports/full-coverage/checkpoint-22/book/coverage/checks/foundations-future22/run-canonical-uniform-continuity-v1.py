"""Record genuine canonical pairs for the unchanged, recovered literal source."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = ROOT / "book/coverage/checks/foundations-future22"
EXT = HERE / "uniform-continuity-extension"
NAME = "CompleteFoundationsUniformContinuity22"
DIGEST = "ca8ba22fe9cb9287de6cb9fc8e6f2edf797908be0deb7acd00aacc5586bef31a"
SOURCE = ROOT / "verification/lean/SafeLearning" / (NAME + ".lean")
ORIGINAL = HERE / "original-tmp" / (NAME + ".lean")
SNAPSHOT = EXT / (NAME + "-source-v1.lean")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def rel(path):
    return path.relative_to(ROOT).as_posix()


def write_new(path, data):
    with path.open("x") as output:
        output.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


assert sha(ORIGINAL) == DIGEST
assert not SOURCE.exists()
assert not EXT.exists()
selection = read(ROOT / "reports/full-coverage/checkpoint-21-selection.json")
assert selection["proof_file_count"] == 1089
protected = {name: row["sha256"] for name, row in selection["proof_files"].items()}
held = read(HERE / "original-tmp/foundations-future22-tmp-proof-index-v1.json")
protected.update(held["held_checkpoint21_assets_exact"])
protected.update(read(ROOT / "book/coverage/foundations.json")["source_sha256"])
for name in ["foundations-source48-candidate-ledger22-v1.json", "foundations-source48-material22-interface-binding-v1.json", "foundations-source48-integration-offer22-draft-v1.json"]:
    protected[rel(HERE / name)] = sha(HERE / name)


def check_protected():
    for name, digest in protected.items():
        assert sha(ROOT / name) == digest, name


check_protected()
EXT.mkdir()
for path in [SOURCE, SNAPSHOT]:
    with path.open("xb") as output:
        output.write(ORIGINAL.read_bytes())
    assert sha(path) == DIGEST
records = []
for mode, command in [
    ("standalone", ["lake", "env", "lean", "SafeLearning/" + NAME + ".lean"]),
    ("named-build", ["lake", "build", "SafeLearning." + NAME]),
]:
    check_protected()
    record_path = EXT / (NAME + "-" + mode + "-v1.json")
    log_path = record_path.with_suffix(".log")
    before = sha(SOURCE)
    started = datetime.now(timezone.utc).isoformat()
    clock = time.monotonic()
    with log_path.open("xb") as output:
        actual = subprocess.run(command, cwd=ROOT / "verification/lean", stdout=output, stderr=subprocess.STDOUT)
    finished = datetime.now(timezone.utc).isoformat()
    elapsed = time.monotonic() - clock
    after = sha(SOURCE)
    record = {
        "source": rel(SOURCE), "source_sha256_before": before, "source_sha256_after": after,
        "preserved_source": rel(SNAPSHOT), "preserved_source_sha256": sha(SNAPSHOT),
        "command": command, "actual_workdir": str(ROOT / "verification/lean"),
        "exit_code": actual.returncode, "started_at_utc": started, "finished_at_utc": finished,
        "elapsed_seconds": elapsed, "log": rel(log_path), "log_sha256": sha(log_path),
        "original_TMP_passing_record": rel(HERE / "original-tmp/foundations-uniform-continuity22-trial2.json"),
        "original_TMP_passing_record_sha256": sha(HERE / "original-tmp/foundations-uniform-continuity22-trial2.json"),
        "scope": "Genuine new canonical execution of the unchanged recovered uniform-continuity source. No selected21, current four-source candidate, or aggregate22 claim."
    }
    write_new(record_path, record)
    print(json.dumps({"actual_record": rel(record_path), "exit_code": actual.returncode, "elapsed_seconds": elapsed}), flush=True)
    check_protected()
    assert actual.returncode == 0 and before == after == DIGEST
    records.append({"record": rel(record_path), "sha256": sha(record_path), "actual_exit_code": actual.returncode})
write_new(EXT / "canonical-paired-readiness-v1.json", {
    "status": "actual_canonical_standalone_and_named_exit_zero_ready_for_whole_literal_review",
    "checked_at_utc": datetime.now(timezone.utc).isoformat(), "source": rel(SOURCE), "source_sha256": DIGEST,
    "preserved_source": rel(SNAPSHOT), "preserved_source_sha256": DIGEST,
    "actual_checker": rel(Path(__file__)), "actual_checker_sha256": sha(Path(__file__)),
    "actual_records": records, "protected_paths_rechecked": len(protected),
    "material_unit": "primer-basics.html::node-1167", "selected_checkpoint21": False,
    "current_four_source_candidate_unchanged": True, "independent_whole_literal_peer_pending": True,
    "coverage_complete": False
})
