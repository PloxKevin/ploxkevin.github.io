from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,difflib
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-core/source64-runner-delta-independent-modules-v2';D.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
old=Path('/tmp/root_tmp_lean_current60_owner28_runner_v1.py');new=Path('/tmp/root_tmp_lean_current64_owner28_runner_v1.py');oc=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json');nc=Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
assert sha(old)=='f9f9f273bfa7c0f22d78f75fed23d32af794f13d51f329ae06747d3dac691c1a'
assert sha(new)=='4c092cb65529bfd8a59b42bf04aae743c09241507e7bad6f732d12204cb437d6'
assert sha(oc)=='35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
assert sha(nc)=='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
a=old.read_text();b=new.read_text();x=json.loads(oc.read_bytes());y=json.loads(nc.read_bytes())
changes=[('Run a genuine TMP Lean trial under the exact actually verified owner28 context.','Run a genuine TMP Lean trial under the actual corrected Source64 and unchanged audited owner28 context.'),('/tmp/root_tmp_lean_current60_owner28_context_v1.json','/tmp/root_tmp_lean_current64_owner28_context_v1.json'),('35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054','442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'),('actual_current60_owner28_verified_context_for_new_tmp_trials_only','actual_current64_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'),('actual_verified_owner28_context','actual_source64_installed28_context'),('unchanged_current60_book_assets','unchanged_current64_book_assets')]
z=a
for before,after in changes:assert z.count(before)==1;z=z.replace(before,after)
assert z==b
assert x['owners_sha256']==y['owners_sha256']and x['selection']==y['selection']and x['actual_audit']==y['actual_audit']
changed_assets={k for k,v in y['held_current_source_sha256'].items()if x['held_current_source_sha256'][k]!=v}
assert changed_assets=={'SafeLearning/lipsdp.html','SafeLearning/primer-basics.html','SafeLearning/primer-linalg.html','SafeLearning/primer-optimization.html'}
assert set(y['held_current_source_sha256'])==set(x['held_current_source_sha256'])and len([n for n in y['held_current_source_sha256']if n.startswith('SafeLearning/')])==31
existing_pin_changes={k for k,v in x['pins_sha256'].items()if y['pins_sha256'][k]!=v}
assert existing_pin_changes=={'book/coverage/inventory.json','book/coverage/material-corrections.json'}
newpins=set(y['pins_sha256'])-set(x['pins_sha256'])
assert newpins=={'book/coverage/inventory-after-correction64.json','reports/full-coverage/source61-64-corrections-application-v1.json','reports/full-coverage/source61-64-corrections-application29-execution-v1.json','reports/full-coverage/source61-64-corrections-application29-execution-v1.log','book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json'}
assert y['original_source60_context']=={'file':str(oc),'sha256':sha(oc)}and y['original_source60_runner']=={'file':str(old),'sha256':sha(old)}
for n,digest in {**y['pins_sha256'],**y['held_current_source_sha256']}.items():
 p=R/n;assert not Path(n).is_absolute()and '..'not in Path(n).parts and not p.is_symlink()and p.resolve().is_relative_to(R)and sha(p)==digest,n
sel=json.loads((R/y['selection']['file'].removeprefix(str(R)+'/')).read_bytes())
assert len(sel['proof_files'])==1186
native=json.loads((R/'reports/full-coverage/source61-64-corrections-application29-execution-v1.json').read_bytes());assert native['actual_exit_code']==0 and native['status']=='passed'
assert y['coverage_complete']is False and 'Audit28 remains immutable evidence for its original Source60 inputs.'in y['scope']
refs={}
for p in [old,new,oc,nc]:
 dst=D/'original-closed-bytes'/sha(p)/p.name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(p.read_bytes());refs[str(dst.relative_to(R))]=sha(dst)
out={'status':'passed_independent_source64_owner28_tmp_runner_exact_delta_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'runner':ref(new),'context':ref(nc),'original_approved_runner':ref(old),'original_approved_context':ref(oc),'six_exact_runner_replacements':changes,'full_original_guard_mask_snapshot_no_o_kernel_invocation_and_native_record_logic_unchanged':True,'context_existing_changed_asset_keys':sorted(changed_assets),'context_existing_changed_pin_keys':sorted(existing_pin_changes),'context_added_pin_keys':sorted(newpins),'all_actual_current64_pins_physically_validated':True,'actual_source61_64_application':y['actual_application_native'],'all1186_and_five_owners_selection_audit_project_pins_unchanged':True,'repetitive_synthetic_fixtures_or_compiler_launches':False,'old_audit_does_not_claim_new_source64_aggregate_audit':True,'live_source_owner_selection_canonical_or_publication_changes':False,'coverage_complete':False,'required_evidence_artifacts_sha256':refs}
q=D/'source64-owner28-tmp-runner-delta-independent-modules29-peer-v1.json';q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(q),'validated_pins':len(set(y['pins_sha256'])|set(y['held_current_source_sha256']))}))
