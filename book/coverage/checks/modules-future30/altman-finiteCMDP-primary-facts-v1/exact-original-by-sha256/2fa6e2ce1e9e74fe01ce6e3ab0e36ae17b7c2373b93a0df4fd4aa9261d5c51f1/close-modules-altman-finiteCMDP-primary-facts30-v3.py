from pathlib import Path
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/altman-finiteCMDP-primary-facts-v1';assert not B.exists();B.mkdir(parents=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p);z=B/'exact-original-by-sha256'/h/p.name;z.parent.mkdir(parents=True,exist_ok=True)
 if not z.exists():
  with z.open('xb')as f:f.write(p.read_bytes())
 assert sha(z)==h;r={'file':str(z.relative_to(R)),'sha256':h,'bytes':z.stat().st_size};aliases[str(p)]=r;return r
P=Path('/tmp/modules-altman-finiteCMDP-primary-facts30-v2/modules-altman-finiteCMDP-primary-facts30-v2.json');d=json.loads(P.read_bytes());assert d['errors']==[]
def close(v):
 if isinstance(v,list):return [close(x)for x in v]
 if isinstance(v,dict):
  if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str):
   assert sha(v['file'])==v['sha256'];return {**{k:close(x)for k,x in v.items()if k not in['file','sha256','bytes']},**copy(v['file'])}
  return {k:close(x)for k,x in v.items()}
 return v
d=close(d);d['original_factual_receipt']=copy(P)
N=Path('/tmp/modules-altman-finiteCMDP-primary-facts30-preparation-actual-v2.json');n=json.loads(N.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[];d['actual_factual_preparation']=copy(N)
for p,h in n['helper_sha256_before'].items():assert sha(p)==h==n['helper_sha256_after'][p];copy(p)
assert sha(n['raw_log'])==n['raw_log_sha256'];copy(n['raw_log']);copy('/tmp/run-modules-altman-finiteCMDP-primary-facts30-preparation-v2.py')
F=Path('/tmp/modules-altman-finiteCMDP-primary-facts30-preparation-actual-v1.json');f=json.loads(F.read_bytes());assert f['actual_exit_code']==1 and f['protection_errors']==[]
for p,h in f['helper_sha256_before'].items():assert sha(p)==h==f['helper_sha256_after'][p];copy(p)
assert sha(f['raw_log'])==f['raw_log_sha256'];d['genuine_first_failed_preparation']={'native':copy(F),'raw':copy(f['raw_log']),'reason':'Temporary DNS failure resolving the author homepage before any factual output. Original source/helper/raw/body/time untouched; a distinct version2 genuinely succeeded.'};copy('/tmp/run-modules-altman-finiteCMDP-primary-facts30-preparation-v1.py')
for p in [__file__,'/tmp/run-modules-altman-finiteCMDP-primary-facts30-durable-closure-v3.py']:copy(p)
d['original_byte_aliases']=aliases;d['required_evidence_artifacts_sha256']={r['file']:r['sha256']for r in aliases.values()};d['supplementary_after_frozen29_manifest']=True
O=B/'modules-altman-finiteCMDP-primary-facts30-closed-v3.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'facts':str(O.relative_to(R)),'sha256':sha(O),'bytes':O.stat().st_size,'refs':len(d['required_evidence_artifacts_sha256'])}))
