"""Run a genuine TMP Lean trial under the actual corrected Source65 and actual audited owner29 context."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re, subprocess, sys, time
ROOT=Path('/home/oxrexkevin/SafetyBased')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
CONTEXT_SHA='ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(CONTEXT)==CONTEXT_SHA
context=json.loads(CONTEXT.read_bytes())
assert context['status']=='actual_current65_owner29_selected29_audited_context_for_new_tmp_trials_only'
assert len(sys.argv)==3
source,record=map(Path,sys.argv[1:])
for p in [source,record]:assert p.is_absolute() and p.resolve().is_relative_to(Path('/tmp')) and not p.is_symlink()
assert source.is_file() and source.suffix=='.lean' and record.suffix=='.json'
log=record.with_suffix('.log');snapshot=record.with_name(record.stem+'-source.lean')
assert all(not p.exists() for p in [record,log,snapshot])
for n,h in {**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}.items():
 p=ROOT/n;assert not Path(n).is_absolute() and '..' not in Path(n).parts and p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p)==h,n
spec=importlib.util.spec_from_file_location('current29_names',ROOT/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
masked=names.without_comments(source.read_text())
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',masked)
runner_before=sha(Path(__file__))
def guard():
 assert sha(Path(__file__))==runner_before and sha(CONTEXT)==CONTEXT_SHA
 for n,h in {**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}.items():
  p=ROOT/n;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p)==h,n
guard();before=sha(source)
with snapshot.open('xb') as f:f.write(source.read_bytes())
assert sha(snapshot)==before
command=['lake','env','lean',str(source)];started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after=sha(source);errors=[]
try:guard()
except Exception as error:errors.append(str(error))
passed=r.returncode==0 and before==after and sha(snapshot)==before and not errors
out={'status':'passed_actual_tmp_lean_only' if passed else 'failed_actual_tmp_lean_or_protection',
 'actual_exit_code':r.returncode,'actual_runner_exit_code':0 if passed else 1,'actual_command':command,'actual_workdir':str(ROOT/'verification/lean'),
 'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,
 'source':str(source),'source_sha256_before':before,'source_sha256_after':after,
 'source_snapshot':str(snapshot),'source_snapshot_sha256':sha(snapshot),'raw_log':str(log),'raw_log_sha256':sha(log),
 'source_unchanged':before==after,'original_actual_runner':{'file':str(Path(__file__)),'sha256':runner_before},
 'actual_source65_installed29_context':{'file':str(CONTEXT),'sha256':CONTEXT_SHA},
 'actual_installed29_selection':context['selection'],'actual_frozen29_original_audit':context['actual_audit'],
 'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,
 'installed29_owner_sha256':context['owners_sha256'],'protection_errors':errors,
 'canonical_installation_or_aggregate_verification_claimed':False,'coverage_complete':False}
with record.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'actual_exit_code':r.returncode,'actual_runner_exit_code':out['actual_runner_exit_code'],'record':str(record),'raw_log':str(log),'protection_errors':errors}))
raise SystemExit(0 if passed else 1)
