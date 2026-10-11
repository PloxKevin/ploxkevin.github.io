from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');R=ROOT/'reports/full-coverage';PUB=ROOT/'reports/book/publication-repo'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
assert read(R/'publication-checkpoint22-staging-execution.json')['status']=='passed_explicit_whitelist_staged'
assert read(R/'lean-checkpoint-22/verification-original.json')['status']=='passed'
names={'book/coverage/checks/root_stage_checkpoint22_additional_execution_evidence_v1.py','book/coverage/checks/root_check_export22_integrity_v1.py'}
for stem in ['owner22-global-integrity-execution-v1','static-checkpoint22-execution-v1','checkpoint22-live-owner-interface-preparation-execution-v2','checkpoint22-live-owner-interface-preparation-execution-v3','checkpoint22-installed-owner-selection-plan-preparation-execution-v1','export-checkpoint22-output-integrity-execution-v1']:
 names.update('reports/full-coverage/'+stem+suffix for suffix in ['.json','.log'])
names.update('reports/full-coverage/'+name for name in ['progress-checkpoint22-before-freeze-update-original-v1.json','progress-checkpoint22-prefreeze-update-v1.json'])
for p in (ROOT/'book/coverage/checks').glob('pages22-config-independent-foundations-*'):
 if p.is_file():names.add(str(p.relative_to(ROOT)))
assert read(R/'checkpoint22-live-owner-interface-preparation-execution-v2.json')['actual_exit_code']==1
for stem in ['owner22-global-integrity-execution-v1','static-checkpoint22-execution-v1','checkpoint22-live-owner-interface-preparation-execution-v3','checkpoint22-installed-owner-selection-plan-preparation-execution-v1','export-checkpoint22-output-integrity-execution-v1']:
 assert read(R/(stem+'.json'))['actual_exit_code']==0
base=set(read(R/'publication-checkpoint22-staging-whitelist.json'));copied={}
for name in sorted(names):
 source=ROOT/name;target=PUB/name;assert source.is_file() and not source.is_symlink() and source.stat().st_size<100_000_000
 target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert sha(target)==sha(source),name
 else:shutil.copyfile(source,target)
 assert sha(target)==sha(source);copied[name]=sha(source)
for argv in [['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],['git','ls-files','--others','--exclude-standard','-z']]:
 dirty=subprocess.run(argv,cwd=PUB,capture_output=True,check=True).stdout
 assert {x.decode() for x in dirty.split(b'\0') if x}<=base|names
pathspec=R/'publication-checkpoint22-additional-evidence-pathspec-v1.nul';assert not pathspec.exists();pathspec.write_bytes(b''.join(name.encode()+b'\0' for name in sorted(names)))
cmd=['git','add','-f','--pathspec-from-file='+str(pathspec),'--pathspec-file-nul'];res=subprocess.run(cmd,cwd=PUB,capture_output=True);assert res.returncode==0
staged=subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,capture_output=True,check=True).stdout
assert {x.decode() for x in staged.split(b'\0') if x}<=base|names
out=R/'publication-checkpoint22-additional-execution-evidence-v1.json';assert not out.exists();out.write_text(json.dumps({'status':'passed_exact_additional_actual_execution_evidence_explicitly_staged','checked_at_utc':datetime.now(timezone.utc).isoformat(),'paths_sha256':copied,'actual_git_command':cmd,'actual_git_workdir':str(PUB),'actual_git_exit_code':res.returncode,'scope':'Exact completed execution histories and preserved first failure, with no mathematical coverage or earlier provenance change.','coverage_complete':False},indent=2)+'\n')
print(json.dumps({'status':'passed','additional_evidence_paths':len(names)}))
