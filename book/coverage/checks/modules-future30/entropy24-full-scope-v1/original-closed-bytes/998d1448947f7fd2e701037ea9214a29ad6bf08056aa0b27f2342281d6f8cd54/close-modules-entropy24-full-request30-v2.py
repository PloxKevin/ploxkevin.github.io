from pathlib import Path
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/entropy24-full-scope-v1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=B/'modules-entropy24-full-source-literal-independent-review-request30-v1.json';d=json.loads(p.read_bytes());aliases=d['original_closed_byte_aliases'];m=d['required_evidence_artifacts_sha256']
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb') as f:f.write(p.read_bytes())
 assert sha(q)==h
 r={'file':str(q.relative_to(R)),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;m[r['file']]=h;return r
n=Path('/tmp/modules-entropy24-full-request30-preparation-actual-v1.json');a=json.loads(n.read_bytes());assert a['actual_exit_code']==0 and a['protection_errors']==[]
d['original_request_v1']=copy(p);d['actual_author_request_preparation']=copy(n)
for x in [a['raw_log'],'/tmp/run-modules-entropy24-full-request30-preparation-v1.py',__file__]:copy(x)
out=B/'modules-entropy24-full-source-literal-independent-review-request30-v2.json';assert not out.exists();out.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':str(out.relative_to(R)),'sha256':sha(out),'bytes':out.stat().st_size,'refs':len(m),'aliases':len(aliases)}))
