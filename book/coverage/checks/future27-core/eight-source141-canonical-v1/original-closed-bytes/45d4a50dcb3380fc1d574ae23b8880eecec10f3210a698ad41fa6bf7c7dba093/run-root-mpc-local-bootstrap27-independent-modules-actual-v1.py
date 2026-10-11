import sys,json,pathlib,hashlib,subprocess,datetime,time
R=pathlib.Path('/home/oxrexkevin/SafetyBased'); C=pathlib.Path('/tmp/review-root-mpc-local-bootstrap27-independent-modules-v1.py'); P=pathlib.Path('/tmp/root-mpc-local-bootstrap27-independent-modules-actual-v1.json'); L=P.with_suffix('.log')
assert not P.exists() and not L.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
command=['python3',str(C)];before=sha(C);start=datetime.datetime.now(datetime.timezone.utc).isoformat();tic=time.monotonic()
with L.open('wb') as raw: result=subprocess.run(command,cwd=R,stdout=raw,stderr=subprocess.STDOUT)
d={'status':'passed_actual_independent_component_reader' if result.returncode==0 else 'failed_actual_independent_component_reader','actual_command':command,'actual_workdir':str(R),'actual_exit_code':result.returncode,'started_at_utc':start,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'duration_seconds':time.monotonic()-tic,'helper_sha256_before':before,'helper_sha256_after':sha(C),'raw_log':str(L),'raw_log_sha256':sha(L),'actual_runner':str(pathlib.Path(__file__)),'actual_runner_sha256':sha(pathlib.Path(__file__)),'scope':'Genuine independent full-body source correspondence reader of three existing MPC bootstrap components; no new compiler/producer execution.'}
P.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));sys.exit(result.returncode)
