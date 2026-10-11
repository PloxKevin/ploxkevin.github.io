from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,ast
R=Path('/home/oxrexkevin/SafetyBased');name='book/coverage/checks/root_stage_checkpoint22_additional_execution_evidence_v1.py';p=R/name;s=p.read_text();digest=hashlib.sha256(p.read_bytes()).hexdigest();t=ast.parse(s)
imports={n.names[0].name for n in t.body if isinstance(n,ast.Import)}
assert 'hashlib' in imports
assert "['git','add','-f','--pathspec-from-file='+str(pathspec),'--pathspec-file-nul']" in s
assert "read(R/'publication-checkpoint22-staging-execution.json')['status']=='passed_explicit_whitelist_staged'" in s
assert "read(R/'lean-checkpoint-22/verification-original.json')['status']=='passed'" in s
assert "source.is_file() and not source.is_symlink() and source.stat().st_size<100_000_000" in s
assert "if target.exists():assert sha(target)==sha(source),name" in s and 'else:shutil.copyfile(source,target)' in s
assert "assert sha(target)==sha(source);copied[name]=sha(source)" in s
assert s.count("<=base|names")==2
assert "glob('pages22-config-independent-foundations-*')" in s
assert "pathspec.write_bytes(b''.join(name.encode()+b'\\0' for name in sorted(names)))" in s
assert "actual_exit_code']==1" in s and "actual_exit_code']==0" in s
assert "assert not pathspec.exists()" in s and "assert not out.exists()" in s
assert all(x not in s for x in ['git push','git commit','lake','subprocess.run(cmd,cwd=ROOT','shutil.rmtree'])
static={'book/coverage/checks/root_stage_checkpoint22_additional_execution_evidence_v1.py','book/coverage/checks/root_check_export22_integrity_v1.py'}
for stem in ['owner22-global-integrity-execution-v1','static-checkpoint22-execution-v1','checkpoint22-live-owner-interface-preparation-execution-v2','checkpoint22-live-owner-interface-preparation-execution-v3','checkpoint22-installed-owner-selection-plan-preparation-execution-v1','export-checkpoint22-output-integrity-execution-v1']:
 static.update('reports/full-coverage/'+stem+x for x in ['.json','.log'])
static.update('reports/full-coverage/'+x for x in ['progress-checkpoint22-before-freeze-update-original-v1.json','progress-checkpoint22-prefreeze-update-v1.json'])
assert len(static)==16
observed={}
for n in sorted(static):
 q=R/n
 if q.exists():observed[n]=hashlib.sha256(q.read_bytes()).hexdigest()
for stem in ['owner22-global-integrity-execution-v1','static-checkpoint22-execution-v1','checkpoint22-live-owner-interface-preparation-execution-v3','checkpoint22-installed-owner-selection-plan-preparation-execution-v1']:
 a=json.loads((R/'reports/full-coverage'/ (stem+'.json')).read_text());assert a['actual_exit_code']==0
assert json.loads((R/'reports/full-coverage/checkpoint22-live-owner-interface-preparation-execution-v2.json').read_text())['actual_exit_code']==1
report={'status':'independent_read_only_additional_checkpoint22_execution_evidence_stager_code_review_passed_pending_actual_stage','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':name,'helper_sha256':digest,'errors':[],'explicit_static_input_paths':sorted(static),'current_observed_input_hashes':observed,'conditional_optional_glob':'book/coverage/checks/pages22-config-independent-foundations-* regular files only','required_execution_order':['Actual original main publication22 stage must already be passed.','Actual frozen22 audit must already be passed.','Five completed success wrappers and the preserved original failed interface preparation must have their exact terminal exit values before copy.'],'assessment':['The helper preserves the independently reviewed main stage and frozen selection. Its only site changes are exact copies of16 literal evidence/helper inputs plus optional Foundation config QA files. Existing publication bytes must already match instead of being overwritten.','It verifies both copied byte hashes and actual wrapper exits, retains the original interface-v2 failure, limits each source file to under100MB, and rejects source symlinks.','It compares all tracked, staged and untracked dirty paths to the original main whitelist plus this bounded extension, then uses a NUL-delimited exact pathspec for force-staging. Staged paths are checked again against that same union.','No commit, push, deployment, Lean build, mathematical mapping or owner/source modification occurs. Its actual copy/stage result still requires a real Root execution.'],'limitations':['This peer reviews helper code and already existing terminal wrapper identities only. The helper was not executed by the peer, and future audit/export/main-stage predicates are not claimed to have passed.','The helper writes its final staging-result JSON locally after its git add. That final result, this peer and their actual execution wrappers need a separate explicit publication copy/staging step if Root wants them included; the reviewed helper does not copy its own newly generated result.'],'actual_checker':str(Path(__file__)),'actual_checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'coverage_complete':False}
out=Path('/tmp/modules-checkpoint22-additional-execution-evidence-stager-independent-code-review-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'file':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'helper_sha256':digest}))
