#!/usr/bin/env python3
"""Retain actual browser evidence only after exact page/shared/QA byte checks."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import copy
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("checkpoint", type=int)
args = parser.parse_args()
n = args.checkpoint
out = ROOT / "reports/full-coverage"
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
prior_path = out / f"browser-checkpoint-{n - 1}.json"
prior = json.loads(prior_path.read_text())
fresh_path = out / f"browser-corrections-{n}.json"
fresh = json.loads(fresh_path.read_text())
inputs = out / f"browser-corrections-{n}-inputs.json"
inp = json.loads(inputs.read_text())
assert inp["status"] == "passed" and inp["exit_code"] == 0
assert len(inp["source_sha256"]) == 31
assert sha(fresh_path) == inp["report_sha256"]
assert sha(ROOT / inp["log"]) == inp["log_sha256"]
for name, digest in inp["source_sha256"].items():
    assert sha(ROOT / name) == digest
    assert sha(out / f"browser-input-{n}" / name) == digest
assert all(r["status"] == "passed" and len(r["viewports"]) == 5
           and not r["errors"] for r in fresh)
for name, digest in prior["qa_source_sha256"].items():
    source = ROOT / name if "/" in name else ROOT / "qa" / name
    assert sha(source) == digest
for row in fresh:
    assert row["qa_source_sha256"] == prior["qa_source_sha256"]
for name, digest in prior["unchanged_shared_asset_sha256"].items():
    source = name if name.startswith("SafeLearning/") else "SafeLearning/" + name
    assert inp["source_sha256"][source] == digest
rows = []
by_file = {r["file"]: r for r in fresh}
for old in prior["pages"]:
    name = old["file"]
    expected = inp["source_sha256"][name]
    if Path(name).name in by_file:
        row = by_file[Path(name).name]
        assert all(s["source_sha256"] == expected for s in row["screenshots"])
        rows.append({
            "file": name, "source_sha256": expected,
            "evidence": str(fresh_path.relative_to(ROOT)),
            "evidence_sha256": sha(fresh_path), "status": "passed",
            "viewport_count": 5,
            "provenance": f"Fresh actual two-page browser run on frozen31asset input{n}."})
    else:
        assert old["source_sha256"] == expected
        assert sha(ROOT / old["evidence"]) == old["evidence_sha256"]
        row = copy.deepcopy(old)
        previous = row.pop("byte_equality_rebase", None)
        if previous is not None:
            row["prior_byte_equality_provenance"] = previous
        row["byte_equality_rebase"] = {
            "prior_composite": str(prior_path.relative_to(ROOT)),
            "prior_composite_sha256": sha(prior_path),
            "page_shared_assets_and_qa_sources_identical": True}
        rows.append(row)
assert len(rows) == 29
result = copy.deepcopy(prior)
result.update(
    created_at_utc=datetime.now(timezone.utc).isoformat(),
    snapshot=f"reports/full-coverage/checkpoint-{n}", pages=rows,
    fresh_run_inputs=str(inputs.relative_to(ROOT)),
    fresh_run_inputs_sha256=sha(inputs),
    limits=[
        "Two corrected pages have fresh actual five-width checks;27 pages retain "
        "actual prior evidence after exact page/shared/QA SHA equality.",
        "No new manual screenshot inspection is asserted. Mathematical "
        "correspondence is reviewed independently."])
destination = out / f"browser-checkpoint-{n}.json"
assert not destination.exists()
destination.write_text(json.dumps(result, indent=2) + "\n")
print(f"Composite29pages145viewports passed: {sha(destination)}")
