#!/usr/bin/env python3
"""Recompute worked examples; requires NumPy/SciPy. This is not formal proof."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'reports/lean-verification'
OUT.mkdir(exist_ok=True, parents=True)
(ROOT / 'reports/learning-review').mkdir(exist_ok=True, parents=True)
SCRIPTS = [
    'reports/learning-review/primers-foundations-math.py',
    'qa/applied_primer_math.py',
    'qa/learning_module_examples.py',
    'reports/learning-review/modules-foundations-math.py',
    'reports/learning-review/modules-certified-math.py',
    'qa/foundations_examples.py',
    'qa/open_problems_examples.py',
]
records = []
for i, script in enumerate(SCRIPTS, 1):
    start = time.monotonic()
    result = subprocess.run([sys.executable, script], text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, cwd=ROOT)
    log = OUT / f'numerical-{i}.log'
    log.write_text(result.stdout)
    records.append(dict(script=script, sha256=hashlib.sha256((ROOT / script).read_bytes()).hexdigest(),
                        exit_code=result.returncode,
                        elapsed_seconds=round(time.monotonic() - start, 3),
                        log=str(log.relative_to(ROOT))))
    print(script, result.returncode, flush=True)
    if result.returncode:
        raise RuntimeError(result.stdout)

report = dict(status='passed', python=sys.version, checks=records,
              limits='Numerical recomputation and finite examples do not establish universal claims. '
                     'Lean proofs and semantic review are separate evidence.')
(OUT / 'numerical-verification.json').write_text(json.dumps(report, indent=2) + '\n')
