from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,copy
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future28-foundations/source62-actual-countermodels4-v1/source62-four-actual-countermodels-full-component-request29-v2.json';O=Path('/tmp/source62-four-components-independent-modules29-peer-original-v1.json');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists() and sha(Q)=='18a86c6240f56993569318b866b2550380d4c78186a9e3ea723c3a0884ee4da2'
start=datetime.now(timezone.utc).isoformat();q=json.loads(Q.read_bytes())
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h
p=R/q['full_source']['file'];s=p.read_text();assert s==q['entire_four_proof_bodies_and_definitions']
names=re.findall(r'^theorem (\w+)',s,re.M);assert names==[v['name']for v in q['requested_component_scopes']] and len(names)==4
native=json.loads((R/q['actual_native']['file']).read_bytes());raw=(R/q['raw_log']['file']).read_text()
assert native['actual_exit_code']==native['actual_runner_exit_code']==0 and native['protection_errors']==[]
assert native['source_sha256_before']==native['source_sha256_after']==native['source_snapshot_sha256']==q['full_source']['sha256']==sha(R/q['source_snapshot']['file'])
assert native['raw_log_sha256']==q['raw_log']['sha256'] and raw.count('warning:')==q['actual_emitted_warning_diagnostic_count']==1
for a,b in [('started_at_utc','actual_started_at_utc'),('finished_at_utc','actual_finished_at_utc'),('elapsed_seconds','elapsed_seconds')]:assert native[a]==q[b]
assert native['actual_command']==['lake','env','lean',native['source']] and native['actual_workdir']==str(R/'verification/lean')
peer=json.loads((R/q['original_prospective_source62_full_literal_parser_peer']['file']).read_bytes());assert peer['status'].startswith('passed') and peer['countermodel_draft_compiled']is False
proposal=json.loads((R/q['original_author_proposal_reference']['file']).read_bytes())
source=R/proposal['source']['file'];assert sha(source)==proposal['source']['sha256']
ls=source.read_text().splitlines();assert '\n'.join(ls[164:189])==proposal['full_current_context_lines165_to189']
reasons=[
'Actual derivative of constant zero is zero at every point, so nonnegative. It does not imply strict progress.',
'Image of constant timing on the genuine closed interval is {0}, whereas the identity path image contains1. The witness contradicts full image equality despite the first theorem; no timing-domain premise or conclusion is assumed.',
'The exact two-neuron ReLU output max(t,0)-max(t,0) simplifies identically to zero, with differentiability at every real input including0. It is a genuine switching cancellation countermodel; it does not assert every switching network is smooth.',
'For arbitrary codomain E and path q, MapsTo timing on T gives one image inclusion; SurjOn timing onto Icc0 1 gives the reverse by an actual preimage. Thus full image equality is genuinely derived from explicit complete parameter coverage, independently of speed monotonicity.'
]
decisions=[{'public_theorem_name':'SafeLearning.FoundationTimingReLUCancellation28.'+n,'entire_component_approved':True,'missing_clauses':[],'full_body_reason':r}for n,r in zip(names,reasons)]
out={'status':'passed_independent_source62_four_actual_countermodel_and_full_image_components_review','errors':[],'reviewer':'/root/modules_finish28','request':{'file':str(Q.relative_to(R)),'sha256':sha(Q)},'reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'individual_full_component_decisions':decisions,'full_source':q['full_source'],'actual_native':q['actual_native'],'raw_log':q['raw_log'],'original_full_native_body_command_time_and_one_warning_preserved':True,'original_source62_full_narrow_peer':q['original_prospective_source62_full_literal_parser_peer'],'original_author_uncompiled_draft_body_time_kept_historical':True,'new_genuine_kernel_pass_supplements_original_without_relabeling':True,'entire_current_and_proposed_contexts_from_original_proposal_read':True,'source62_applied':False,'whole200_202_promoted':False,'coverage_complete':False,'compiler_or_live_owner_source_selection_publication_changes':False,'required_evidence_artifacts_sha256':q['required_evidence_artifacts_sha256']}
O.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'four_components':len(decisions),'peer':str(O),'sha256':sha(O)}))
