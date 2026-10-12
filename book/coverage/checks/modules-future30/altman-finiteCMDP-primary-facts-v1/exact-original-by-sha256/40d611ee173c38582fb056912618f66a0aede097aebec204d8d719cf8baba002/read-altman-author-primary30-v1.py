from pathlib import Path
from datetime import datetime,timezone
import urllib.request,hashlib,json,time,subprocess
B=Path('/tmp/modules-duality-Altman-primary30-v1');assert not B.exists();B.mkdir()
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
u='https://www-sop.inria.fr/members/Eitan.Altman/PAPERS/h.pdf';started=datetime.now(timezone.utc).isoformat();t=time.monotonic();d={'url':u,'started_at_utc':started}
try:
 with urllib.request.urlopen(u,timeout=25)as r:
  b=r.read();d.update({'actual_http_status':r.status,'actual_final_url':r.url,'headers':dict(r.headers)});p=B/'altman-author-original.pdf';p.write_bytes(b);d.update({'body_file':str(p),'body_sha256':h(p),'body_bytes':len(b),'actual_download_success':True})
  c=['pdftotext','-layout',str(p),str(B/'altman-author-full-text.txt')];z=subprocess.run(c,capture_output=True);(B/'actual-pdftotext.log').write_bytes(z.stdout+z.stderr);d.update({'actual_text_command':c,'actual_text_exit_code':z.returncode})
except Exception as e:d.update({'actual_download_success':False,'actual_exception':str(e),'actual_exception_type':type(e).__name__})
d.update({'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'full_primary_bytes_TMP_offline_only':True});(B/'actual-primary-download-v1.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
