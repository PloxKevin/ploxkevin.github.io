from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future30-foundations/current79-completed90-association-v1'
OLD=D/'foundations30-completed90-current79-pair-bound-offer-v4.json';OUT=D/'foundations30-completed90-current79-pair-bound-closed-offer-v5.json';A=Path('/tmp/foundations30-completed90-readiness-association-actual-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(OLD)=='d44438868ae88477e1fd5f62248454121db1b795fae1e3ff852b431c1525b522'
d=json.loads(OLD.read_bytes());a=json.loads(A.read_bytes());assert a['status']=='passed' and a['actual_exit_code']==0 and a['protection_errors']==[] and a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256']
required=dict(d['required_evidence_artifacts_sha256']);aliases=dict(d['original_closed_byte_aliases'])
def bind(p):
 p=Path(p);q=D/'actual-binding-originals'/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==sha(p)
 else:
  with q.open('xb') as f:f.write(p.read_bytes())
 r=ref(q);aliases[str(p)]=r;required[r['file']]=r['sha256'];return r
native=bind(A);raw=bind(Path(a['log']));helper=bind(Path(a['actual_command'][1]));wrapper=bind(Path('/tmp/run-associate-foundations30-completed90-readiness-v1.py'));bind(Path(__file__));required[ref(OLD)['file']]=sha(OLD)
d.update(status='closed_completed90_current79_Foundation_owner30_27_source54_pair_candidate_pending_independent_full_mapping',closed_at_utc=datetime.now(timezone.utc).isoformat(),original_exact_pair_bound_author_offer=ref(OLD),actual_completed90_association_execution=native,actual_completed90_association_raw_log=raw,actual_completed90_association_helper=helper,actual_completed90_association_wrapper=wrapper,completed90_association_preparation_actual_pending=False,original_pair_binding_native_status_code_body_time_preserved=True,candidate_preparation_actual_pending=False,all_new_actual_canonical_pairs_pending=False,common90_outer_runner_and_final_readiness_pending=False,final_independent_mapping_review_pending=True,original_closed_byte_aliases=aliases,required_evidence_artifacts_sha256=required,additional_frozen_inputs=required,canonical_compiler_invoked_by_binder=False,coverage_complete=False)
d['original_completed90_wrapper_scope_description_observation']={'original_scope':a['scope'],'correct_scope':'The actual distinct associater helper binds true completed90 readiness to unchanged Foundation27/54 source/literal mapping.','reason':'Wrapper descriptive scope was retained from the earlier real54 prefix binder and says common90 is still pending; exact actual command/helper/findings now check completed90. Preserve the native body/time unchanged; this is not a missing semantic read or fabricated failure.'}
for n,h in required.items():assert not Path(n).is_absolute() and (R/n).resolve().is_relative_to(R) and not (R/n).is_symlink() and sha(R/n)==h,n
OUT.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'offer':ref(OUT),'candidate':d['candidate'],'interface':d['exact_interface'],'actual_binder':native,'actual_binder_seconds':a['elapsed_seconds'],'refs':len(required),'actual_pairs':[27,370,54],'full90_pending':False,'errors':[]}))
