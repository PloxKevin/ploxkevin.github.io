import importlib.util,pathlib,json,concurrent.futures,urllib.request,time,subprocess
P=pathlib.Path('/tmp/fetch-foundations-basics-eight-primary-bibliography28-v1.py')
s=importlib.util.spec_from_file_location('retrieval',P);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.OUT=pathlib.Path('/tmp/foundations-basics-primary-chapter-checks28-v1');assert not m.OUT.exists();m.OUT.mkdir()
before=m.protected()
row=m.fetch(('arora-full-http','http://theory.cs.princeton.edu/complexity/book.pdf'))
name='sutton-current-full-http';url='http://incompleteideas.net/book/RLbook2020.pdf';started=m.stamp();t=time.monotonic();r={'id':name,'requested_url':url,'started_at_utc':started,'maximum_offline_bytes':90000000}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 (bibliographic-source-verification)'}),timeout=25) as response:
  b=response.read(90000001);assert len(b)<=90000000
  r.update(http_status=response.status,final_url=response.url,content_type=response.headers.get('Content-Type'),bytes=len(b),sha256=m.sha(b))
 assert b.startswith(b'%PDF')
 p=m.OUT/(name+'.pdf');p.write_bytes(b);r['offline_file']=str(p)
 q=m.OUT/(name+'.txt');command=['pdftotext','-layout',str(p),str(q)];cp=subprocess.run(command,capture_output=True)
 r['text_conversion']={'command':command,'exit_code':cp.returncode,'raw_output_sha256':m.sha(cp.stdout+cp.stderr)}
 if cp.returncode==0:r['offline_text']={'file':str(q),'sha256':m.sha(q.read_bytes())}
except Exception as e:r['error']=repr(e)
r.update(ended_at_utc=m.stamp(),elapsed_seconds=time.monotonic()-t)
after=m.protected();errors=[n for n in before if before[n]!=after[n]]
D={'schema_version':1,'scope':'Actual primary chapter reads only; full remote originals retained TMP offline, never website copied. Original failed size-limit attempt preserved separately.','results':[row,r],'protected_before':before,'protected_after':after,'protection_errors':errors}
(m.OUT/'primary-http-receipts-v1.json').write_text(json.dumps(D,ensure_ascii=False,indent=2)+'\n')
for x in [row,r]:print(json.dumps({k:x[k] for k in ['id','http_status','bytes','sha256','error'] if k in x},ensure_ascii=False),flush=True)
assert not errors,errors
