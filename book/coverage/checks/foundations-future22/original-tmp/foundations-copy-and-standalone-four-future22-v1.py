from pathlib import Path
import hashlib,json,subprocess,datetime,time
R=Path('/home/oxrexkevin/SafetyBased');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
C=R/'book/coverage/checks/foundations-future22';C.mkdir(exist_ok=True)
rows=[('RKHSBounds22','f6846424356377b77321fd1f31a9e81a804bc29d016164edd512f177e4a8f3d4','rkhs-bounds22',4),('WorkedSafety22','66d1291d9dc23f5018758aad668cfa0e4f74bf111bce27e1e1f238c060173fb3','worked-safety22',4),('ContinuousLevels22','dfef4b0192b537d014b50e0e57a1fac5c72b79c5fa527aea4292fcc02a19c775','continuous-levels22',2),('MetricDefinitions22','6812f3f764ef170a7b3e62ad9e08b4591526161416113baa407cb67e7e14dc7a','metric-definitions22',2)]
result=[]
for name,sha,slug,trial in rows:
 tmp=Path('/tmp/CompleteFoundations'+name+'.lean');p=R/'verification/lean/SafeLearning'/tmp.name;rec=C/('CompleteFoundations'+name+'-standalone-v1.json');log=rec.with_suffix('.log')
 assert not p.exists() and not rec.exists() and not log.exists(),str(p)
 assert h(tmp)==sha
 tprec=Path('/tmp/foundations-'+slug+'-trial'+str(trial)+'.json');tp=json.loads(tprec.read_text());assert tp['exit_code']==0 and tp['source_sha256_after']==sha
 p.write_bytes(tmp.read_bytes());assert h(p)==sha
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();timer=time.monotonic()
 cmd=['lake','env','lean','SafeLearning/'+tmp.name];proc=subprocess.run(cmd,cwd=R/'verification/lean',capture_output=True,text=True)
 log.write_text(proc.stdout+proc.stderr)
 d={'source':str(p.relative_to(R)),'source_sha256_before':sha,'source_sha256_after':h(p),'command':cmd,'actual_workdir':str(R/'verification/lean'),'exit_code':proc.returncode,'started_at_utc':start,'finished_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-timer,'log':str(log.relative_to(R)),'log_sha256':h(log),'actual_tmp_passing_record':str(tprec),'actual_tmp_passing_record_sha256':h(tprec),'scope':'NEW future22 actual standalone execution; frozen21 and held owner21 source/helper/ledger/offer unchanged; no shared named package build.'}
 rec.write_text(json.dumps(d,indent=2)+'\n')
 summary={'source':d['source'],'sha256':sha,'actual_record':str(rec.relative_to(R)),'actual_record_sha256':h(rec),'exit_code':proc.returncode,'log_sha256':h(log)}
 print(json.dumps(summary),flush=True);result.append(summary)
 assert proc.returncode==0 and h(p)==sha,log.read_text()
print(json.dumps({'status':'four_new_future22_sources_actual_standalone_exit_zero','records':result}),flush=True)
