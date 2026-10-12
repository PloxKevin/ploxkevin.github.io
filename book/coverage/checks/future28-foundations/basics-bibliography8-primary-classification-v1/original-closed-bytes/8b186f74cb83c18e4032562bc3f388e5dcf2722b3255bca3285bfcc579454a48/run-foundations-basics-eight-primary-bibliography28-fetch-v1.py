import datetime,hashlib,json,pathlib,subprocess,time
R=pathlib.Path('/home/oxrexkevin/SafetyBased');H=pathlib.Path('/tmp/fetch-foundations-basics-eight-primary-bibliography28-v1.py')
P=pathlib.Path('/tmp/foundations-basics-eight-primary-bibliography28-fetch-actual-v1.json');L=P.with_suffix('.log')
assert not P.exists() and not L.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
started=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();before=sha(H);cmd=['python3',str(H)]
with L.open('wb') as f:cp=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
d={'status':'passed' if cp.returncode==0 else 'failed','command':cmd,'cwd':str(R),'started_at_utc':started,'ended_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'actual_exit_code':cp.returncode,'helper':{'file':str(H),'sha256_before':before,'sha256_after':sha(H)},'raw_log':{'file':str(L),'sha256':sha(L)},'scope':'Actual retrieval native status does not assert every endpoint succeeded; see individual receipts.'}
P.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d));raise SystemExit(cp.returncode)
