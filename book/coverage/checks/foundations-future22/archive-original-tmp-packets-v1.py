"""Preserve exact original Foundation 22 TMP history without rewriting claims."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
CHECKS = ROOT / "book/coverage/checks/foundations-future22"
TMP = Path("/tmp")
ARCHIVE = CHECKS / "original-tmp"
OUT = CHECKS / "original-tmp-packet-byte-copies-v1.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


names = {
    "CompleteFoundations" + suffix + ".lean"
    for suffix in ("RKHSBounds22", "WorkedSafety22", "ContinuousLevels22", "MetricDefinitions22", "UniformContinuity22")
}
names.update({
    "foundations-copy-and-standalone-four-future22-v1.py",
    "foundations-future22-prepare-tmp-proof-index-v1.py",
    "foundations-future22-tmp-proof-index-v1.json",
    "linalg-rkhs-bounds-two-units-independent-applied-source-review22-v1.json",
    "review-rkhs-bounds22-independent-applied-v1.py",
    "foundations-worked-safety-nine-literals-independent-modules-source-review22-v1.json",
    "modules-worked-safety22-source-review-v1.py",
    "modules-worked-safety22-source-review-v2.py",
    "modules-worked-safety22-source-review-failed-reader-v1.json",
    "basics-continuous-levels-three-units-independent-applied-source-review22-v1.json",
    "review-continuous-levels22-independent-applied-v1.py",
    "basics-metric-definitions-two-units-independent-applied-source-review22-v1.json",
    "review-metric-definitions22-independent-applied-v1.py",
})
prefixes = tuple("foundations-" + slug + "22-" for slug in (
    "rkhs-bounds", "worked-safety", "continuous-levels", "metric-definitions", "uniform-continuity", "rkhs-dependencies"
))
names.update(path.name for path in TMP.iterdir() if path.is_file() and path.name.startswith(prefixes)
             and path.suffix in {".py", ".json", ".log", ".lean"})
assert not OUT.exists()
ARCHIVE.mkdir(exist_ok=True)
copies = []
for name in sorted(names):
    original = TMP / name
    assert original.is_file() and not original.is_symlink(), name
    target = ARCHIVE / name
    expected = sha(original)
    assert not target.exists(), str(target)
    with target.open("xb") as output:
        output.write(original.read_bytes())
    assert sha(target) == expected
    copies.append({"original": str(original), "original_sha256": expected,
                   "canonical_byte_copy": target.relative_to(ROOT).as_posix(),
                   "canonical_byte_copy_sha256": expected})

actual_trials = []
for name in sorted(names):
    if "-trial" not in name or not name.endswith(".json"):
        continue
    original = TMP / name
    record = json.loads(original.read_text())
    assert sha(Path(record["preserved_source"])) == record["preserved_source_sha256"]
    assert sha(Path(record["log"])) == record["log_sha256"]
    assert record["source_sha256_before"] == record["source_sha256_after"] == record["preserved_source_sha256"]
    actual_trials.append({"original_record": str(original), "original_record_sha256": sha(original),
                          "actual_original_exit_code": record["exit_code"],
                          "preserved_source_sha256": record["preserved_source_sha256"],
                          "original_log_sha256": record["log_sha256"]})
data = {"status": "exact_original_tmp_foundation22_sources_trials_reviews_and_failures_preserved",
        "copied_at_utc": datetime.now(timezone.utc).isoformat(),
        "actual_copy_helper": Path(__file__).relative_to(ROOT).as_posix(),
        "actual_copy_helper_sha256": sha(Path(__file__)),
        "copies": copies, "actual_original_trial_records": actual_trials,
        "coverage_complete": False,
        "limits": ["All original bytes and original review/execution times are unchanged; no copied TMP run is claimed as a new canonical execution.",
                   "The pending UniformContinuity22 TMP source and failed/passed trials are archived for recovery only; they are not included in the four-source integration offer.",
                   "Held21 inputs, current48 HTML/inventory and existing selected proofs are untouched."]}
with OUT.open("x") as output:
    output.write(json.dumps(data, indent=2) + "\n")
print(json.dumps({"status": data["status"], "copies": len(copies), "original_trials": len(actual_trials), "failed_trials": sum(row["actual_original_exit_code"] != 0 for row in actual_trials), "manifest": OUT.relative_to(ROOT).as_posix(), "sha256": sha(OUT)}))
