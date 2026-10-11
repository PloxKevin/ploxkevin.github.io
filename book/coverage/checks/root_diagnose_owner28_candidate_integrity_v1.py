"""Preserve the real isolated candidate validation report; never install owners."""
from pathlib import Path
import hashlib,importlib.util,json,sys,tempfile
ROOT=Path(__file__).resolve().parents[3]
BINDING='book/coverage/checks/future28-core/current60-owner28-binding-v1.json'
OUT='reports/full-coverage/owner28-isolated-candidate-integrity-diagnostic-v1.json'
binding=json.loads((ROOT/BINDING).read_bytes());assert not (ROOT/OUT).exists()
with tempfile.TemporaryDirectory(prefix='root-owner28-diagnostic-') as tmp:
 ctx=Path(tmp);(ctx/'book/coverage').mkdir(parents=True);(ctx/'verification').mkdir()
 (ctx/'SafeLearning').symlink_to(ROOT/'SafeLearning',target_is_directory=True)
 (ctx/'verification/lean').symlink_to(ROOT/'verification/lean',target_is_directory=True)
 (ctx/'book/coverage/inventory.json').symlink_to(ROOT/'book/coverage/inventory.json')
 for owner,row in binding['owners'].items():(ctx/row['destination']).symlink_to(ROOT/row['candidate']['file'])
 sys.path.insert(0,str(ROOT/'book/coverage'))
 spec=importlib.util.spec_from_file_location('candidate28_integrity_diagnostic',ROOT/'book/coverage/validate.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.ROOT=ctx
 report=module.validate()
 with (ROOT/OUT).open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ['integrity_status','mathematical_coverage_complete','counts','errors']},indent=2))
 raise SystemExit(0 if report['integrity_status']=='passed' else 1)
