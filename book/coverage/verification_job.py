#!/usr/bin/env python3
"""Run a fixed verification command with persistent actual-exit evidence.

Start detached only through the --start option. Poll the recorded PID and log;
an absent exit record is never success and never authorizes restarting a live job.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import subprocess
import sys

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-root',type=Path,required=True)
    parser.add_argument('--record',type=Path,required=True)
    parser.add_argument('--log',type=Path,required=True)
    parser.add_argument('--start',action='store_true')
    args=parser.parse_args()
    project=args.project_root.resolve()
    record=args.record.resolve()
    log=args.log.resolve()
    command=[sys.executable,str(project/'verification/lean/verify.py')]
    record.parent.mkdir(parents=True,exist_ok=True)
    log.parent.mkdir(parents=True,exist_ok=True)
    if args.start:
        if record.exists():
            raise RuntimeError('Use a new record path for a new attempt; do not overwrite previous job evidence.')
        worker=[sys.executable,str(Path(__file__).resolve()),'--project-root',str(project),
                '--record',str(record),'--log',str(log)]
        with log.open('w') as output:
            child=subprocess.Popen(worker,cwd=project,stdin=subprocess.DEVNULL,
                stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        print(json.dumps(dict(pid=child.pid,record=str(record),log=str(log))))
        return 0
    evidence=dict(status='running',pid=os.getpid(),command=command,cwd=str(project),
        started_at_utc=datetime.now(timezone.utc).isoformat(),
        verifier_sha256=hashlib.sha256((project/'verification/lean/verify.py').read_bytes()).hexdigest())
    record.write_text(json.dumps(evidence,indent=2)+'\n')
    result=subprocess.run(command,cwd=project,check=False)
    evidence.update(status='passed' if result.returncode==0 else 'failed',
        exit_code=result.returncode,finished_at_utc=datetime.now(timezone.utc).isoformat())
    record.write_text(json.dumps(evidence,indent=2)+'\n')
    return result.returncode

if __name__=='__main__':
    sys.exit(main())
