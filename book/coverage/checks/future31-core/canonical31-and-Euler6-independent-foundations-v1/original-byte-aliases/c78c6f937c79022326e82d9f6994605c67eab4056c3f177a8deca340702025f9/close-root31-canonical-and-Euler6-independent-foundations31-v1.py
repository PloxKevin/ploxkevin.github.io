from pathlib import Path
import json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased')
INPUT=Path('/tmp/root31-canonical-and-Euler6-independent-foundations31-v1')
BASE=ROOT/'book/coverage/checks/future31-core/canonical31-and-Euler6-independent-foundations-v1'
assert not BASE.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
native='/tmp/root31-canonical-and-Euler6-independent-foundations31-actual-v1.json'
n=json.loads(Path(native).read_text());assert n['actual_exit_code']==0 and n['protection_errors']==[]
for stem,filename in [('canonical-code-peer-v1','root31-canonical-runner-full-code-actual81-domain-independent-foundations31-closed-peer-v1.json'),('Euler24-six-increment-math-peer-v1','root-Euler24-six-actual-discrete-increment-full-prefix-independent-foundations31-closed-peer-v1.json')]:
 d=json.loads((INPUT/(stem+'.json')).read_text());refs={r['file']:r for r in d['direct_evidence']}
 for name in [native,n['log'],'/tmp/review-root31-canonical-and-Euler6-independent-foundations31-v1.py','/tmp/run-review-root31-canonical-and-Euler6-independent-foundations31-v1.py','/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json',str(INPUT/(stem+'.json')),str(Path(__file__))]:refs[name]=ref(name)
 aliases={}
 for name,r in refs.items():
  p=path(name);assert sha(p)==r['sha256']
  if 'bytes' in r:assert p.stat().st_size==r['bytes']
  # Retain the already durable full aggregate audit by direct exact reference.
  if name.startswith('reports/full-coverage/lean-checkpoint-30-final-css-v1/'):
   aliases[name]={'original':r,'already_durable_exact_reference':r};continue
  q=BASE/'original-byte-aliases'/r['sha256']/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:q.write_bytes(p.read_bytes())
  aliases[name]={'original':r,'original_byte_copy':ref(q)}
 d['actual_reader']=aliases[native]['original_byte_copy'];d['actual_finalizer']=d['actual_reader']
 d['actual_reader_original_byte_aliases']={name:aliases[name]['original_byte_copy'] for name in [native,n['log'],'/tmp/review-root31-canonical-and-Euler6-independent-foundations31-v1.py','/tmp/run-review-root31-canonical-and-Euler6-independent-foundations31-v1.py','/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json']}
 d['all_original_byte_aliases']=aliases
 d['required_evidence_artifacts_sha256']={r.get('original_byte_copy',r.get('already_durable_exact_reference'))['file']:r['original']['sha256'] for r in aliases.values()}
 d['original_measured_reader_body_time_preserved']=True
 d['scope_of_durable_closure']='Bounded leaf sources/helpers/native/raw and exact existing peer bodies only. No previous snapshot/dependency/cache trees or recursive peer histories copied.'
 out=BASE/filename;out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'peer':ref(out),'actual_reader':d['actual_reader'],'elapsed_seconds':n['elapsed_seconds'],'exact_originals':len(aliases)}))
