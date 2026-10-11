import sys,json,pathlib,hashlib,subprocess,datetime,time
R=pathlib.Path('/home/oxrexkevin/SafetyBased');C=pathlib.Path('/tmp/review-foundations-balanced-sensor27-independent-modules-v1.py');P=pathlib.Path('/tmp/foundations-balanced-sensor27-independent-modules-actual-v1.json');L=P.with_suffix('.log')
assert not P.exists() and not L.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
command=['python3',str(C),*sys.argv[1:]];before=sha(C);start=datetime.datetime.now(datetime.timezone.utc).isoformat();tic=time.monotonic()
with L.open('wb') as raw:result=subprocess.run(command,cwd=R,stdout=raw,stderr=subprocess.STDOUT)
record={'status':'passed_actual_independent_checker'if result.returncode==0 else'failed_actual_independent_checker','actual_command':command,'actual_workdir':str(R),'actual_exit_code':result.returncode,'started_at_utc':start,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'duration_seconds':time.monotonic()-tic,'helper_sha256_before':before,'helper_sha256_after':sha(C),'raw_log':str(L),'raw_log_sha256':sha(L),'actual_runner':str(pathlib.Path(__file__)),'actual_runner_sha256':sha(pathlib.Path(__file__)),'scope':'Actual independent full semantic balanced-sensor three-literal source review, with read-only exact evidence/current input checker; no new compiler or installation.'}
P.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record));sys.exit(result.returncode)
