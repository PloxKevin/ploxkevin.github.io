from pathlib import Path
import hashlib, importlib.util, json, sys
sys.dont_write_bytecode = True
p=Path('/home/oxrexkevin/SafetyBased/book/coverage/checks/root_close_foundations27_reviewed_offer_v1.py')
spec=importlib.util.spec_from_file_location('foundation27_reviewed_offer_closure',p)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
old,new,copies=m.prepare()
assert old['proof_files']==new['proof_files'] and old['candidate']==new['candidate']
assert not m.ARCHIVE.exists() and not m.DEST.exists()
print(json.dumps({'status':'passed_read_only_author_native_offer_closure_preflight', 'helper_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'new_alias_copies_pending':len(copies),'sources':3,'exports':43,'commands':6,'producer_executed':False,'live_owner_write':False}))
