from pathlib import Path
from datetime import datetime,timezone
import urllib.request,hashlib,json
B=Path('/tmp/modules-rohr-primary-eq4-30-v1');assert not B.exists();B.mkdir()
u='https://proceedings.mlr.press/v144/rohr21a/rohr21a.pdf'
t=datetime.now(timezone.utc).isoformat()
req=urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0'})
with urllib.request.urlopen(req,timeout=30) as r:
 data=r.read();status=r.status;headers=dict(r.headers);final=r.url
assert status==200 and data.startswith(b'%PDF-')
p=B/'rohr21a-exact-original.pdf';p.write_bytes(data)
x={'url':u,'final_url':final,'http_status':status,'started_at_utc':t,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'original_pdf':{'file':str(p),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)},'response_headers':headers,'full_original_stays_TMP_offline':True,'read_scope_pending':'Actual visual equation4 and used preceding distribution/assumption context; full paper approval not inferred.'}
q=B/'rohr21a-primary-http-receipt-v1.json';q.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x))
