from pathlib import Path
import json,hashlib,re,copy
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
Q=D/'modules-scalar-lipsdp42-full-scope-independent-review-request29-v1.json';q=json.loads(Q.read_bytes());p=Path('/tmp/modules-scalar-sdp-source65-proposal29-v1/modules-scalar-sdp-source65-proposal29-v1.json');v=json.loads(p.read_bytes());native=json.loads(Path('/tmp/modules-scalar-lipsdp-optimum29-owner28-trial7.json').read_bytes());count=len(re.findall(r'^.*?:\d+:\d+: warning:',Path(native['raw_log']).read_text(),re.M));assert count==6
v['actual_emitted_warning_count']=count;v['original_proposal_v1_counted_diagnostic_hint_occurrences_too']={'file':q['source65_narrow_proposal_historical_current60']['file'],'sha256':q['source65_narrow_proposal_historical_current60']['sha256']};v['actual_emitted_warning_diagnostic_regex']='^.*?:[0-9]+:[0-9]+: warning:'
P=D/'modules-scalar-sdp-source65-proposal29-v2-diagnostic-count-only.json';assert not P.exists();P.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n');pr={'file':str(P.relative_to(R)),'sha256':sha(P),'bytes':P.stat().st_size}
q['source65_narrow_proposal_historical_current60']=pr;q['required_evidence_artifacts_sha256'][pr['file']]=pr['sha256'];counts=[]
for t in q['seven_genuine_native_trials_all_bodies_times_preserved']:
 raw=(R/t['raw_log']['file']).read_text();n=len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M));counts.append(n);t['actual_emitted_warning_count']=n
assert counts==[0,6,4,6,5,5,6];q['actual_final_warning_count']=count;q['original_request_v1_preserved_warning_hint_count_normalized_only']={'file':str(Q.relative_to(R)),'sha256':sha(Q)};q['required_evidence_artifacts_sha256'][str(Q.relative_to(R))]=sha(Q)
q['actual_warning_diagnostic_regex']='^.*?:[0-9]+:[0-9]+: warning:';Q2=D/'modules-scalar-lipsdp42-full-scope-independent-review-request29-v2.json';assert not Q2.exists();Q2.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':str(Q2.relative_to(R)),'sha256':sha(Q2),'bytes':Q2.stat().st_size,'counts':counts,'proposal':pr}))
