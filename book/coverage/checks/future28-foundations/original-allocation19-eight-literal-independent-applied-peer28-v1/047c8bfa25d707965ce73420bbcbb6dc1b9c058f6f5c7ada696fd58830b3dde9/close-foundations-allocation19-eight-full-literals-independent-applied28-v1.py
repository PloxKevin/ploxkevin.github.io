from pathlib import Path
import hashlib,json
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
obs=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-observations28-v2.json');actual=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-actual28-v2.json');body=json.loads(obs.read_bytes());native=json.loads(actual.read_bytes());failed=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-actual28-v1.json');failure=json.loads(failed.read_bytes())
assert native['actual_exit_code']==0 and type(native['actual_exit_code']) is int and native['protection_errors']==[] and failure['actual_exit_code']==1 and failure['protection_errors']==[]
files=[obs,actual,actual.with_suffix('.log'),Path('/tmp/check-foundations-allocation19-eight-full-literals-independent-applied28-v2.py'),Path('/tmp/run-foundations-allocation19-eight-full-literals-independent-applied28-v2.py'),failed,failed.with_suffix('.log'),Path('/tmp/check-foundations-allocation19-eight-full-literals-independent-applied28-v1.py'),Path('/tmp/run-foundations-allocation19-eight-full-literals-independent-applied28-v1.py'),Path(__file__)]
body['actual_independent_review']={'file':str(actual),'sha256':sha(actual)}
body['entire_original_independent_failure_body_and_time']=failure
body['independent_failure_reason']='Reader1 required splitlines() equality, which drops the final blank line after joining the exact1417–1486 context. Packet text equals the original exact newline-joined source slice. Reader2 changes only that representation check; no mathematical/source/compiler record was changed.'
body['closed_evidence_sha256']={str(p):sha(p) for p in files}
body['inherited_original_closed_byte_aliases']=body['entire_original_author_packet_body_and_time']['original_closed_byte_aliases']
for original,r in body['inherited_original_closed_byte_aliases'].items():assert sha(Path(original))==sha(Path(r['file']))==r['sha256'];body['closed_evidence_sha256'][original]=r['sha256']
out=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-review28-v1.json')
with out.open('x') as f:f.write(json.dumps(body,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'peer':str(out),'sha256':sha(out),'actual_sha256':sha(actual),'raw_log_sha256':sha(actual.with_suffix('.log')),'whole_units':len(body['material_units']),'closed_refs':len(body['closed_evidence_sha256'])}))
