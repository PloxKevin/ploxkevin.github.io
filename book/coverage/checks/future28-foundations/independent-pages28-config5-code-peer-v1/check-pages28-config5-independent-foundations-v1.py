from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,importlib.util,json,subprocess
R=Path('/home/oxrexkevin/SafetyBased');S=R/'book/coverage/checks/root_prepare_pages28_config_v5.py';O=Path('/tmp/pages28-config5-independent-foundations-findings-v1.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':h(p)}
assert h(S)=='563cc55d1203fbb354aa8a0b00cf29c6fb830fae3d6ce95c910bccbc727fd653' and not O.exists()
started=datetime.now(timezone.utc).isoformat();old=(R/'book/coverage/checks/root_prepare_pages28_config_v4.py').read_text();new=S.read_text()
added=" 'reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-26','reports/full-coverage/browser-artifacts-source44-19-v2',\n"
assert new.replace("SELF='book/coverage/checks/root_prepare_pages28_config_v5.py'","SELF='book/coverage/checks/root_prepare_pages28_config_v4.py'").replace(added,'').replace('len(ADDITIONS)==23','len(ADDITIONS)==20').replace("['reports/full-coverage/lean-checkpoint-26','reports/full-coverage/browser-artifacts-25','reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-26','reports/full-coverage/browser-artifacts-source44-19-v2']","['reports/full-coverage/lean-checkpoint-26','reports/full-coverage/browser-artifacts-25']")==old
spec=importlib.util.spec_from_file_location('pages5_no_writer',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert len(m.ADDITIONS)==23
pub=m.PUB;assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=pub,text=True).strip()==m.HEAD
config=(pub/'_config.yml').read_bytes();oldex={line[4:] for line in config.decode().splitlines() if line.startswith('  - ')}
assert len(oldex)==133 and h(pub/'_config.yml')==m.BEFORE and not oldex&m.ADDITIONS and len(oldex|m.ADDITIONS)==156
directories=['reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-26','reports/full-coverage/browser-artifacts-source44-19-v2'];rows=[];retired={}
for n in directories:
 paths={p.relative_to(R).as_posix():h(p) for p in m.safe(R,n).rglob('*') if p.is_file()}
 assert paths
 tracked={p for p in subprocess.check_output(['git','ls-files','-z','--',n],cwd=pub,text=True).split('\0') if p};assert tracked==set(paths)
 cp=subprocess.run(['git','diff','--quiet','HEAD','--',n],cwd=pub);assert cp.returncode==0
 assert all(m.sha(pub,p)==digest for p,digest in paths.items())
 assert not m.kept(n,oldex|m.ADDITIONS) and m.kept(n+'-sibling/file',oldex|m.ADDITIONS)
 rows.append({'directory':n,'file_count':len(paths),'actual_root_pub_git_head_bytes':sum((R/p).stat().st_size for p in paths),'files_sha256':paths,'git_diff_exit_code':cp.returncode});retired.update(paths)
assert all(m.kept(n,oldex|m.ADDITIONS) for n in ['reports/full-coverage/lean-checkpoint-28/verification-original.json','reports/full-coverage/browser-artifacts-28/capture.png','SafeLearning/primer-basics.html','book/coverage/foundations.json'])
assert not m.kept('verification/lean/SafeLearning/BookApplications.lean',oldex|m.ADDITIONS)
tree=ast.parse(new);prep=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='prepare');archive_loop=next(n for n in prep.body if isinstance(n,ast.For) and "browser-artifacts-source44-19-v2" in ast.unparse(n.iter));assert ast.literal_eval(archive_loop.iter)[-3:]==directories
assert all(part in ast.unparse(archive_loop) for part in ['tracked == set(paths)',"['git', 'diff', '--quiet', 'HEAD', '--', n]",'sha(PUB, p) == h'])
# Pure exact archival membership assertions reject changed lists/expected bytes; no archive or Git mutation.
tests=[]
def reject(label,fn):
 try:fn()
 except AssertionError:tests.append({'fixture':label,'rejected':True})
 else:raise AssertionError(label)
for row in rows:
 def check(tracked,paths):assert tracked==set(paths)
 reject('missing_git_tracked_file_'+row['directory'],lambda row=row:check(set(row['files_sha256'])- {next(iter(row['files_sha256']))},row['files_sha256']))
 bad=dict(row['files_sha256']);p=next(iter(bad));bad[p]='0'*64
 def byte_check(bad):assert all(m.sha(pub,p)==d for p,d in bad.items())
 reject('conflicting_expected_archive_sha_'+row['directory'],lambda bad=bad:byte_check(bad))
assert (pub/'_config.yml').read_bytes()==config
out={'status':'passed_full_independent_pages28_config5_exact_delta_and_retired_archival_bytes_review','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':started,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(S),'previous_full_code_peer':ref(R/'book/coverage/checks/future28-foundations/independent-pages28-config4-code-peer-v1/pages28-config4-independent-foundations-closed-v1.json'),'exact_delta_only_self_three_literal_paths_count23_and_retired_validation_list':True,'new_literal_archive_directories':rows,'actual_retired_original_bytes':sum(row['actual_root_pub_git_head_bytes'] for row in rows),'negative_fixture_count':len(tests),'negative_fixture_observations':tests,'current_total_exclusions':156,'current_required_source_audit_ledgers_images_website_membership_unchanged':True,'code_approval_for_root_owned_genuine_runtime_preflight':True,'producer_prepare_writer_or_git_mutation_executed':False,'actual_complete_current5_budget_preflight_or_delivery_claimed':False,'scope':'Only the three exact retired historical scopes join exclusions and unchanged full ROOT/PUB/trackedHEAD validation. All originals remain exact in Git. Prior4 full code and native1186 archive checks remain separate; only genuine Root current5 complete inclusive850MB preflight can approve budget.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'findings':ref(O),'exact_retired_files':len(retired),'bytes':out['actual_retired_original_bytes'],'negative_fixtures':len(tests)}))
