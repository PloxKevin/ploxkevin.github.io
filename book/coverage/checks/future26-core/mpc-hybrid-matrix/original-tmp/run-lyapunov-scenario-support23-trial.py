import sys,subprocess,hashlib,json,datetime,pathlib
trial=sys.argv[1]
source=pathlib.Path('/tmp/CompleteLyapunovScenarioSupport23.lean')
stem=pathlib.Path('/tmp/applied-lyapunov-scenario-support23-trial'+trial)
snapshot=pathlib.Path(str(stem)+'-source.lean')
assert not snapshot.exists()
snapshot.write_bytes(source.read_bytes())
h=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
cmd=['lake','env','lean',str(snapshot)]
cwd='/home/oxrexkevin/SafetyBased/verification/lean'
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
r=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
log=pathlib.Path(str(stem)+'.log');log.write_bytes(r.stdout)
record={'status':'actual_standalone_lean_execution','actual_command':cmd,'cwd':cwd,'started_at':start,'completed_at':end,'actual_exit_code':r.returncode,'source_file':str(snapshot),'source_sha256_before':h(snapshot),'source_sha256_after':h(snapshot),'working_source_file':str(source),'working_source_sha256_after':h(source),'raw_log_file':str(log),'raw_log_sha256':h(log),'runner_file':__file__,'runner_sha256':h(__file__)}
with pathlib.Path(str(stem)+'.json').open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record));print(r.stdout.decode());sys.exit(r.returncode)
