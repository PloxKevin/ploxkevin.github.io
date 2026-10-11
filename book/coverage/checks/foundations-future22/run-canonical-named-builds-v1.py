"""Run only four immutable new Foundation 22 named targets, preserving originals."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
CHECKS = ROOT / "book/coverage/checks/foundations-future22"
PROJECT = ROOT / "verification/lean"
ROWS = [
    ("RKHSBounds22", "f6846424356377b77321fd1f31a9e81a804bc29d016164edd512f177e4a8f3d4"),
    ("WorkedSafety22", "66d1291d9dc23f5018758aad668cfa0e4f74bf111bce27e1e1f238c060173fb3"),
    ("ContinuousLevels22", "dfef4b0192b537d014b50e0e57a1fac5c72b79c5fa527aea4292fcc02a19c775"),
    ("MetricDefinitions22", "6812f3f764ef170a7b3e62ad9e08b4591526161416113baa407cb67e7e14dc7a"),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write_new(path, data):
    with path.open("x") as output:
        output.write(json.dumps(data, indent=2) + "\n")


manifest = read(ROOT / "reports/full-coverage/checkpoint-21-manifest.json")
assert manifest["status"] == "formal_verification_passed_partial_coverage"
assert len(manifest["proof_files"]) == 1089
held = dict(read(Path("/tmp/foundations-future22-tmp-proof-index-v1.json"))["held_checkpoint21_assets_exact"])
held.update({name: row["sha256"] for name, row in manifest["proof_files"].items()})
held.update({name: digest for name, digest in manifest["frozen_inputs_sha256"].items() if name.startswith("SafeLearning/")})


def check_held():
    for name, digest in held.items():
        assert sha(ROOT / name) == digest, name


check_held()
result = []
for suffix, expected in ROWS:
    name = "CompleteFoundations" + suffix
    source = PROJECT / "SafeLearning" / (name + ".lean")
    standalone_path = CHECKS / (name + "-standalone-v1.json")
    standalone = read(standalone_path)
    assert standalone["exit_code"] == 0
    assert standalone["source_sha256_before"] == standalone["source_sha256_after"] == expected
    assert sha(ROOT / standalone["log"]) == standalone["log_sha256"]
    assert sha(source) == sha(Path("/tmp") / source.name) == expected
    assert source.relative_to(ROOT).as_posix() not in manifest["proof_files"]
    preserved = CHECKS / "sources" / (name + "-source-v1.lean")
    preserved.parent.mkdir(exist_ok=True)
    if preserved.exists():
        assert sha(preserved) == expected
    else:
        with preserved.open("xb") as output:
            output.write(source.read_bytes())
    record = CHECKS / (name + "-named-build-v1.json")
    log = record.with_suffix(".log")
    command = ["lake", "build", "SafeLearning." + name]
    if record.exists():
        data = read(record)
        assert data["exit_code"] == 0 and data["command"] == command
        assert data["source_sha256_before"] == data["source_sha256_after"] == expected
        assert sha(ROOT / data["log"]) == data["log_sha256"]
    else:
        assert not log.exists(), str(log)
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        with log.open("x") as output:
            actual = subprocess.run(command, cwd=PROJECT, stdout=output, stderr=subprocess.STDOUT)
        data = {
            "source": source.relative_to(ROOT).as_posix(),
            "source_sha256_before": expected,
            "source_sha256_after": sha(source),
            "command": command,
            "actual_workdir": str(PROJECT),
            "exit_code": actual.returncode,
            "started_at_utc": started,
            "finished_at_utc": datetime.now(timezone.utc).isoformat(),
            "elapsed_seconds": time.monotonic() - tick,
            "log": log.relative_to(ROOT).as_posix(),
            "log_sha256": sha(log),
            "preserved_source": preserved.relative_to(ROOT).as_posix(),
            "preserved_source_sha256": sha(preserved),
            "paired_actual_standalone_record": standalone_path.relative_to(ROOT).as_posix(),
            "paired_actual_standalone_record_sha256": sha(standalone_path),
            "scope": "Actual execution of this one new immutable future22 named target; no aggregate audit or checkpoint22 selection is asserted.",
        }
        write_new(record, data)
    assert data["exit_code"] == 0 and sha(source) == expected, str(log)
    check_held()
    summary = {"source": data["source"], "source_sha256": expected, "actual_named_record": record.relative_to(ROOT).as_posix(), "actual_named_record_sha256": sha(record), "actual_exit_code": data["exit_code"], "log_sha256": data["log_sha256"]}
    result.append(summary)
    print(json.dumps(summary), flush=True)
out = CHECKS / "four-canonical-paired-build-readiness-v1.json"
write_new(out, {"status": "four_new_future22_immutable_sources_actual_standalone_and_named_exit_zero", "checked_at_utc": datetime.now(timezone.utc).isoformat(), "actual_checker": Path(__file__).relative_to(ROOT).as_posix(), "actual_checker_sha256": sha(Path(__file__)), "held21_paths_rechecked": len(held), "records": result, "coverage_complete": False, "selected_checkpoint21": False, "limits": ["Only actual recorded standalone and four named target builds are asserted.", "These sources remain outside the selected checkpoint21 snapshot. Independent whole literal approvals and canonical evidence bindings are required before any future22 ledger integration."]})
print(json.dumps({"status": "passed", "readiness": out.relative_to(ROOT).as_posix(), "readiness_sha256": sha(out)}), flush=True)
