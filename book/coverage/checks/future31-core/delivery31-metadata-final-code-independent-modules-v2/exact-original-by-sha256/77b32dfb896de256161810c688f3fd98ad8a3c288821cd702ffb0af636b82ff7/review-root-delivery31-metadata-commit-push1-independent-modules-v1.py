from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
CODE=ROOT/'book/coverage/checks/root_commit_push_delivery31_metadata_v1.py'
EXPECTED='955cf5805b7883e1aa893994a3cbdf14d6c0fb953c2723bf982a4e553bc3ee9e'
OUT=Path('/tmp/modules-delivery31-metadata-commit-push1-independent-code-review-v1')
REVIEW=OUT/'delivery31-metadata-commit-push1-full-unexecuted-code-independent-modules-v1.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(CODE)==EXPECTED and not OUT.exists();OUT.mkdir()
copy=OUT/'root_commit_push_delivery31_metadata_v1-complete-unexecuted-source.py'
with copy.open('xb') as f:f.write(CODE.read_bytes())
assert sha(copy)==EXPECTED
text=CODE.read_text();assert len(text.splitlines())==91
observations=[]
env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0'
for args in [['rev-parse','HEAD'],['symbolic-ref','--quiet','--short','HEAD'],['diff','--cached','--name-only','-z'],['status','--porcelain=v1','-z','--untracked-files=all'],['remote','get-url','origin'],['config','--get','core.hooksPath']]:
 r=subprocess.run(['git',*args],cwd=PUB,env=env,capture_output=True)
 row={'actual_command':['git',*args],'actual_workdir':str(PUB),'actual_exit_code':r.returncode,'GIT_OPTIONAL_LOCKS':'0','stderr':r.stderr.decode()}
 if '-z' in args:
  records=[s.decode() for s in r.stdout.split(b'\0') if s]
  row.update({'output_sha256':hashlib.sha256(r.stdout).hexdigest(),'record_count':len(records),'first10_records':records[:10]})
 else:row['stdout']=r.stdout.decode()
 observations.append(row)
index=PUB/'.git/index';hooks=PUB/'.git/hooks'
future=['reports/full-coverage/publication31-content-commit-v1.json','reports/full-coverage/publication31-delivery-metadata-preparation-v1.json','reports/full-coverage/prepare-delivery31-metadata-execution-v1.json','reports/full-coverage/publication31-metadata-commit-v1.json','reports/full-coverage/publication31-metadata-push-v1.json']
findings=[
 {'id':'D31M1','severity':'material','lines':[25,36,67,73,81,87],'finding':'Measured actual git subprocess receipt is not durable until after success postchecks. HEAD/HEAD-parent/status or ls-remote failure/mismatch after a real successful commit/push causes exit before the actual native JSON is written, losing actual code0/command/time while the real external effect and log exist.','required_change':'Preserve immutable actual subprocess native receipt before dependent postchecks, or guarantee writing it in finally with actual command exit code retained and separately typed postcheck/runner failures. Do not replace a true git0 with a helper1 or overwrite the receipt.'},
 {'id':'D31M2','severity':'material_gate_gap','lines':[43,78,81],'finding':'No code gate binds refs/heads/main to the recorded commit. HEAD checks permit detached/other-branch HEAD; push origin main acts on local main, which can then differ from HEAD and the intended metadata commit.','required_change':'Before commit/push require symbolic-ref HEAD=refs/heads/main or directly verify refs/heads/main=the exact intended HEAD/commit, and use an explicit intended refspec. Current observed main branch is contextual evidence only.'},
 {'id':'D31M3','severity':'postcommit_association_gap','lines':[65,68,70,72],'finding':'actual_committed_paths_sha256 is derived from the precommit index, with no after-commit tree/hash and changed-path check. HEAD-parent and clean worktree alone do not prove the actual committed tree equals the measured index. Current repository has no non-example hooks, so no actual mismatch is claimed.','required_change':'Bind the committed parent-child path delta and tree blob hashes to exact expected changed paths after real commit, recording failed checks separately from the genuine command receipt.'},
 {'id':'D31M4','severity':'receipt_provenance_improvement','lines':[31,35,80,85],'finding':'Metadata native omits helper SHA and explicit remote_main_before although it checks the remote against CONTENT before push. The companion content helper includes both provenance fields.','required_change':'Record exact executed helper SHA and observed remote_main_before, alongside preparation/native references and the actual command, for a complete typed receipt chain.'}]
positive=[
 {'scope':'git/index gates','lines':[43,44,56,58,63,64],'conclusion':'Commit requires HEAD at CONTENT, initially empty staged diff, only expected modified/untracked paths, then a nonempty staged set contained in expected and no tracked unstaged diff. Expected-but-unchanged paths may be absent from the staged delta; subset rather than equality is intentional metadata behavior.'},
 {'scope':'literal path staging/blob gates','lines':[48,55,61,66],'conclusion':'Uses --literal-pathspecs and NUL pathspec-from-stdin; stages only explicit expected metadata+four extras; checks ROOT/PUB bytes against exact preparation hashes and each staged blob SHA. This avoids colon pathspec interpretation. Safe path/symlink and authentic preparation schema are supplied by the separately reviewed preparation producer, not repeated here.'},
 {'scope':'baseline and remote gates','lines':[71,77,80,85],'conclusion':'Successful metadata commit must have CONTENT parent; push requires passing recorded commit, exact local HEAD, clean PUB, and remote main at CONTENT; it uses non-force push and checks remote after against recorded commit. Explicit main binding and actual receipt preservation still need repair.'},
 {'scope':'native timing and incomplete-coverage fields','lines':[27,35,86,91],'conclusion':'Fresh native/log absence prevents overwrite; timestamps are UTC and elapsed uses monotonic around real subprocess; actual nonzero command returns are preserved on the ordinary failed-command path. coverage_complete remains False, and metadata Pages/live success is explicitly not claimed.'}]
review={'status':'completed_full_independent_code_review_changes_required_unexecuted_helper','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_entire_source':ref(CODE),'entire_source_TMP_copy':ref(copy),'entire_reviewed_code':text,'entire91_lines_read':True,'producer_helper_import_or_execution':False,'fixture_or_PUB_git_index_stage_commit_push_mutation':False,'all_material_findings_immediately_reported_to_parent':True,'findings':findings,'positive_code_gates_and_limits':positive,'actual_readonly_git_observations':observations,'PUB_index_observed_ref':ref(index) if index.exists() else None,'index_observation_is_not_a_freeze_against_Root_disjoint_publication':True,'non_example_executable_hooks_observed':[p.name for p in hooks.iterdir() if p.is_file() and not p.name.endswith('.sample') and bool(p.stat().st_mode&0o111)] if hooks.is_dir() else [],'future_actual_delivery_input_receipts_observed':[{'file':n,'exists':(ROOT/n).exists(),'not_an_actual_delivery_approval':True} for n in future],'previous_readonly_observation_error_preserved':{'actual_workdir':str(ROOT),'actual_exit_code':129,'error':'Initial git observations launched from workspace root, which is not a Git repository. Corrected to PUB with GIT_OPTIONAL_LOCKS=0; no helper, stage, commit, push, index, source or owner mutation occurred.'},'whole_coverage_or_actual_Pages_live_or_future_delivery_approval':False,'code_approved_for_commit_push':False,'required_before_code_close':'Repair D31M1 and D31M2; review complete new exact helper. Final real input/readiness binding remains pending actual content31 receipt/Pages/all31 live evidence.'}
with REVIEW.open('x') as f:f.write(json.dumps(review,indent=2)+'\n')
assert sha(CODE)==EXPECTED
print(json.dumps({'status':review['status'],'review':ref(REVIEW),'reviewed_source':ref(CODE),'findings':len(findings),'code_approved_for_commit_push':False,'producer_helper_execution':False,'PUB_index_mutation':False}))
