"""Capture actual standalone Lean exits and proof fingerprints for foundations.

This is scoped compilation evidence, not aggregate kernel replay or coverage.
Use filenames as arguments to check a batch. Every run replaces only its own
named check records and never modifies the frozen historical checkpoints.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "verification/lean"
OUT = ROOT / "book/coverage/checks/foundations-next"
OUT.mkdir(parents=True, exist_ok=True)
names = sys.argv[1:] or [p.stem for p in (LEAN / "SafeLearning").glob("CompleteFoundations*.lean")]
env = dict(os.environ)
env["PATH"] = "/home/oxrexkevin/.elan/bin:" + env["PATH"]
failed = False
for name in names:
    if not name.startswith("CompleteFoundations") or "/" in name:
        raise ValueError(name)
    source = LEAN / "SafeLearning" / (name + ".lean")
    before = hashlib.sha256(source.read_bytes()).hexdigest()
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    log = OUT / (name + ".log")
    with log.open("w") as stream:
        result = subprocess.run(["lake", "env", "lean", "SafeLearning/" + source.name],
                                cwd=LEAN, env=env, stdout=stream, stderr=subprocess.STDOUT)
    after = hashlib.sha256(source.read_bytes()).hexdigest()
    record = dict(scope="standalone_compile_only", command=["lake", "env", "lean", "SafeLearning/" + source.name],
                  workdir="verification/lean", started_at=started,
                  finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  exit_code=result.returncode, source=str(source.relative_to(ROOT)),
                  source_sha256_before=before, source_sha256_after=after,
                  log=str(log.relative_to(ROOT)), log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                  unchanged=before == after)
    (OUT / (name + ".json")).write_text(json.dumps(record, indent=2) + "\n")
    print(name, result.returncode, "unchanged" if before == after else "CHANGED", flush=True)
    failed |= result.returncode != 0 or before != after
sys.exit(1 if failed else 0)
