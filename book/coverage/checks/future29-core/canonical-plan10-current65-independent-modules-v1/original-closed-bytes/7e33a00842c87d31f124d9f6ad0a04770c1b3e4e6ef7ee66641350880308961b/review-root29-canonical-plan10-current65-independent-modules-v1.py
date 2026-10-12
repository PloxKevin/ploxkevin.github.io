from pathlib import Path
from datetime import datetime,timezone
import sys,json,hashlib,importlib.util,re
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-core/canonical-plan10-current65-independent-modules-v1';assert not D.exists();D.mkdir(parents=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def loc(n):
 p=Path(n);p=p if p.is_absolute()else R/p;assert p.is_file()and not p.is_symlink()and (p.resolve().is_relative_to(R)or p.resolve().is_relative_to('/tmp'));return p
def checked(v):p=loc(v['file']);assert sha(p)==v['sha256'];return p
H=R/'book/coverage/checks/run_root29_reviewed_canonical_pairs_v1.py';assert sha(H)=='d1d4358d68e183ad3d4fee48735d2bd99572a5c640c8be5d9ea753abc61af141';body=H.read_text();assert 'base.resolve().is_relative_to(ROOT.resolve())'in body and 'assert p.resolve().is_relative_to(ROOT.resolve())'in body and "all(not q.is_symlink() for q in [p,*p.parents]"in body
P=R/'book/coverage/checks/future29-core/current65-canonical-plan10-v1.json';assert sha(P)=='c52479b0decac7ad29160ec198e4c6ebce8c42948603939c55080ce71bbdb49b';p=json.loads(P.read_bytes());C=checked(p['context']);assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';c=json.loads(C.read_bytes());assert c['status']=='actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'and c['coverage_complete']is False
held={**c['pins_sha256'],**c['held_current_source_sha256']}
for n,h in held.items():assert sha(loc(n))==h,n
assert len(c['owners_sha256'])==5 and all(held[n]==h for n,h in c['owners_sha256'].items());assert sum(n.startswith('SafeLearning/')for n in held)==31
A=checked(c['actual_audit']);audit=json.loads(A.read_bytes());assert audit['status']=='passed'and audit['proof_file_count']==1186 and len(audit['declarations'])==9896;assert len(audit['proof_sha256'])==1186 and all(held[n]==h for n,h in audit['proof_sha256'].items())
S=checked(c['selection']);sel=json.loads(S.read_bytes());assert len(sel['proof_files'])==1186 and {n:r['sha256']for n,r in sel['proof_files'].items()}==audit['proof_sha256']
N=R/'book/coverage/lean_names.py';assert sha(N)==held['book/coverage/lean_names.py'];spec=importlib.util.spec_from_file_location('module29_canonical_plan_full_names_review',N);names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
known={r['name']for n in audit['proof_sha256']for r in names.declarations(loc(n).read_text())};newnames=set();theorems=0;reviewed=[];refs={};aliases={}
def bind(n):
 path=loc(str(n));h=sha(path);dst=D/'original-closed-bytes'/h/path.name;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert sha(dst)==h
 else:dst.write_bytes(path.read_bytes())
 v={'file':str(dst.relative_to(R)),'sha256':h,'bytes':dst.stat().st_size};refs[v['file']]=h;aliases[str(path)]=v;return v
for row in p['sources']:
 source=checked(row['original_tmp_source']);decls=names.declarations(source.read_text());assert decls==row['public_declarations'];assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',names.without_comments(source.read_text()))
 nn={x['name']for x in decls};assert len(nn)==len(decls)and not nn&(known|newnames);newnames|=nn;nt=sum(x['kind']in ['theorem','lemma']for x in decls);assert nt==row['public_theorem_count'];theorems+=nt
 dest=R/row['canonical_source'];assert dest.parent==R/'verification/lean/SafeLearning'and dest.suffix=='.lean'and not dest.exists()and not dest.is_symlink()
 nat=checked(row['original_actual_tmp_trial']);d=json.loads(nat.read_bytes());codes=[d[k]for k in ['actual_exit_code','exit_code','actual_runner_exit_code']if k in d];assert codes and all(type(v)is int and v==0 for v in codes)and d.get('protection_errors',[])==[];assert d['actual_command']==['lake','env','lean',d['source']]and d['actual_workdir']==str(R/'verification/lean')and d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']==sha(source)
 snap=checked({'file':d['source_snapshot'],'sha256':d['source_snapshot_sha256']});log=checked({'file':d['raw_log'],'sha256':d['raw_log_sha256']});assert snap.read_bytes()==source.read_bytes()
 peerrefs=[];peer_source_match=False
 for v in row['independent_source_peers']:
  f=checked(v);peer=json.loads(f.read_bytes());assert peer['errors']==[]and peer['status'].startswith('passed_');peer_source_match|=sha(source)in f.read_text();peerrefs.append(bind(f))
 assert peer_source_match
 for suffix in ['.log','-standalone.json','-named-build.log','-named-build.json']:assert not (R/'book/coverage/checks'/(dest.stem+suffix)).exists()
 reviewed.append({'owner':row['owner'],'canonical_source':row['canonical_source'],'source':bind(source),'original_true_trial':bind(nat),'original_true_snapshot':bind(snap),'original_true_raw_log':bind(log),'independent_full_source_peers':peerrefs,'public_names':len(decls),'theorem_lemma_count':nt,'original_command_cwd_source_codes_body_and_times_unchanged':True})
assert len(reviewed)==p['source_count']==10 and theorems==p['public_theorem_count']==202 and len(newnames)==p['public_name_count']==264
base=R/p['result_directory'];assert not base.exists()and base.resolve().is_relative_to(R)and all(not z.is_symlink()for z in [base,*base.parents]if z.is_relative_to(R))
helpers=[R/'book/coverage/check_core_standalone.py',R/'book/coverage/check_core_named_build.py'];assert sha(helpers[0])=='124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a'and sha(helpers[1])=='605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069'
for q in p['original_scope_plans']:checked(q)
out={'status':'passed_independent_full_root29_current65_canonical_plan10_executor_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':bind(H),'helper_sha256':sha(H),'exact_plan':bind(P),'exact_current65_context':bind(C),'source_count':10,'public_theorem_lemma_count':202,'public_name_count':264,'all10_full_plan_source_names_accurate_and_disjoint_from1186_sources_and_each_other':True,'all_true_original_TMP_codes_command_cwd_source_snapshot_raw_log_peer_refs_exact':True,'all_current65_context_pins_source31_and_five_owners_physically_validated':True,'all_fresh_canonical_source_four_native_evidence_paths_and_result_directory_absent':True,'physical_root_containment_and_symlink_ancestor_issue_fixed_before_apply':True,'exact_native_helpers_fully_read':list(map(bind,helpers)),'namespace_aware_comment_and_string_mask_parser_fully_read':bind(N),'compiler_commands_after_apply_exactly20_standalone_and_named':[['lake','env','lean','SafeLearning/<basename>.lean'],['lake','build','SafeLearning.<basename>']],'native_before_after_source_codes_original_workdir_and_log_fingerprints_checked_against_each_actual_helper_return':True,'guards_hold_preexisting_audited_sources_and_owners_before_after_each_pair_command':True,'compiler_logs_receipts_and_private_kernel_cache_are_real_execution_evidence_not_semantic_or_aggregate_authority':True,'whole_semantic_coverage_and_owner_selection_aggregate_kernel_replay_publication_remain_separate':True,'no_synthetic_mirror_fixtures':True,'reviewer_compiler_or_executor_apply_started':False,'coverage_complete':False,'actual_new_sources':reviewed,'required_evidence_artifacts_sha256':refs,'original_closed_byte_aliases':aliases}
q=D/'root29-canonical-plan10-current65-full-executor-independent-modules29-peer-v1.json';q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(q.relative_to(R)),'sha256':sha(q),'bytes':q.stat().st_size,'sources':10,'public_names':264,'theorems':202}))
