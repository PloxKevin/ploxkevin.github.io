from pathlib import Path
import importlib.util,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');p=R/'book/coverage/checks/root_retain_browser25_exact24_v1.py'
spec=importlib.util.spec_from_file_location('retention',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
r=json.loads((R/m.ORIGINAL).read_text());assets=r['source_sha256'];qa=r['qa_source_sha256'];shots={s['path']:hashlib.sha256((R/s['path']).read_bytes()).hexdigest() for page in r['pages'] for s in page['screenshots'] if s['status']=='passed'}
assert m.validate(r,assets,qa,shots)==(48,10)
