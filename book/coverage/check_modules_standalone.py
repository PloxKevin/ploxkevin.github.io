#!/usr/bin/env python3
"""Compile each new module file; aggregate kernel/axiom audit remains separate."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "verification/lean"
OUT = ROOT / "book/coverage/checks"
OUT.mkdir(exist_ok=True)
LAKE = Path.home() / ".elan/bin/lake"


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


files = sorted((LEAN/"SafeLearning").glob("CompleteModules*.lean"))
frozen = {str(p.relative_to(ROOT)): digest(p) for p in files}
records = []
for p in files:
    log = OUT/(p.stem+".log")
    with log.open("w") as stream:
        result = subprocess.run([str(LAKE),"env","lean",str(p.relative_to(LEAN))],
                                cwd=LEAN,stdout=stream,stderr=subprocess.STDOUT,
                                timeout=180)
    record = {"file":str(p.relative_to(ROOT)),"sha256":digest(p),
              "exit_code":result.returncode,"log":str(log.relative_to(ROOT)),
              "log_sha256":digest(log),"source_unchanged":digest(p)==frozen[str(p.relative_to(ROOT))]}
    records.append(record)
    print(json.dumps(record),flush=True)
    if result.returncode:
        print(log.read_text(),flush=True)

report = {"generated_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "kind":"standalone_compilation_only",
          "status":"passed" if all(r['exit_code']==0 and r['source_unchanged'] for r in records) else "failed",
          "files":records,
          "all_sources_still_match":all(digest(ROOT/p)==sha for p,sha in frozen.items()),
          "lean_toolchain":(LEAN/"lean-toolchain").read_text().strip(),
          "limits":["Root must run the fresh aggregate build, kernel replay and transitive-axiom audit.",
                    "Standalone imports use the existing compiled dependency cache; this report is not a complete source-correspondence audit."]}
(OUT/"modules-standalone.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"status":report['status'],"files":len(records)}),flush=True)
sys.exit(0 if report['status']=='passed' and report['all_sources_still_match'] else 1)
