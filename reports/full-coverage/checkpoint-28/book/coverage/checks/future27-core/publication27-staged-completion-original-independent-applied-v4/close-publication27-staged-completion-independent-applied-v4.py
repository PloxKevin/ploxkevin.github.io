from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
actual=Path('/tmp/publication27-staged-completion-independent-applied-actual-v4.json');obs=Path('/tmp/publication27-staged-completion-independent-applied-observations-v4.json');d=json.loads(actual.read_bytes());o=json.loads(obs.read_bytes())
assert type(d['actual_exit_code'])is int and d['actual_exit_code']==0 and d['protection_errors']==[] and d['protected_sha256_before']==d['protected_sha256_after']
assert o['status']=='passed_independent_full_checkpoint27_staged_completion_code_and_read_only_prefix_review' and o['errors']==[]
assert sha(Path(d['log']))==d['log_sha256']
helper='book/coverage/checks/root_finish_staged_publication27_v4.py';h=sha(ROOT/helper);assert h=='1dd2fb895b1776eed921145db20b16053e6a67105fba18981545e49fa8da4951'
folder=ROOT/'book/coverage/checks/future27-core/publication27-staged-completion-original-independent-applied-v4';assert not folder.exists();folder.mkdir(parents=True)
originals=[Path('/tmp/check-publication27-staged-completion-independent-applied-v4.py'),Path('/tmp/run-publication27-staged-completion-independent-applied-v4.py'),actual,Path(d['log']),obs,Path('/tmp/publication27-completion-v2-index-frozen-guard-observation-v1.json'),Path('/tmp/check-publication27-staged-completion-independent-applied-v3.py'),Path('/tmp/run-publication27-staged-completion-independent-applied-v3.py'),Path('/tmp/publication27-staged-completion-independent-applied-actual-v3.json'),Path('/tmp/publication27-staged-completion-independent-applied-actual-v3.log'),Path(__file__)]
aliases={};closed={}
for p in originals:
 q=folder/p.name;data=p.read_bytes();q.write_bytes(data);assert sha(q)==sha(p);n=q.relative_to(ROOT).as_posix();aliases[str(p)]={'file':n,'sha256':sha(q)};closed[n]=sha(q)
cat={'status':'exact_original_closed_independent_completion_code_review_byte_aliases','original_body_time_and_bytes_unchanged':True,'original_closed_byte_aliases':aliases}
catalog=folder/'original-closed-byte-aliases-v1.json';catalog.write_text(json.dumps(cat,ensure_ascii=False,indent=2)+'\n');closed[catalog.relative_to(ROOT).as_posix()]=sha(catalog)
for n in ['book/coverage/checks/root_finish_staged_publication27_v1.py','book/coverage/checks/root_finish_staged_publication27_v2.py','book/coverage/checks/root_finish_staged_publication27_v3.py']:
 closed[n]=sha(ROOT/n)
out=ROOT/'book/coverage/checks/future27-core/publication27-staged-completion-independent-applied-review-v4.json';assert not out.exists()
ref=lambda p:{'file':str(p),'sha256':sha(p)}
b={'status':'passed_independent_full_checkpoint27_staged_completion_code_review','errors':[],'reviewer':'Applied independent reviewer','reviewed_at_utc':d['finished_at_utc'],'helper':{'file':helper,'sha256':h},'helper_sha256':h,'full_source_and_delta_read':True,'exact_v4_to_v3_reverse':o['exact_v4_to_v3_reverse'],'prior_v3_requires_changes_actual':o['prior_v3_actual_parser_failure'],'fixture_count':o['fixture_count'],'actual_read_only_main_prefix':o['actual_read_only_main_prefix'],'prior_v2_requires_changes_observation':o['prior_v2_finding'],'original_v1_helper':o['original_v1_helper'],'original_v2_helper':o['original_v2_helper'],'original_v3_helper':o['original_v3_helper'],'actual_independent_reader':ref(actual),'raw_log':ref(Path(d['log'])),'observations':ref(obs),'original_closed_byte_aliases':aliases,'closed_evidence_sha256':closed,'publication_evidence_sha256':closed,'original_closed_byte_alias_catalog':{'file':catalog.relative_to(ROOT).as_posix(),'sha256':sha(catalog)},'scope':'Conditional full code/delta review with exact-function isolated negative fixtures and genuine read-only main prefix through original99 archival lint. All already-prepared/frozen/current bytes and staged blob hashes checked read-only. Existing failed stage3 remains actual1; final100th exception is only its exact raw log. No completion producer execution, copies, Git staging/commit/push, Pages or delivery success claimed.'}
out.write_text(json.dumps(b,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'peer':str(out),'sha256':sha(out),'fixture_count':o['fixture_count'],'catalog':str(catalog),'catalog_sha256':sha(catalog),'actual_sha256':sha(actual),'log_sha256':d['log_sha256']}))
