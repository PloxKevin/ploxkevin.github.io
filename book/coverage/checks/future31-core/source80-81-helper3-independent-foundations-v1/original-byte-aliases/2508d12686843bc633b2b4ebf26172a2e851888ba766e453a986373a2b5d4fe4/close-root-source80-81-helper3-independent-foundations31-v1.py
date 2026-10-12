from pathlib import Path
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
DEST=ROOT/'book/coverage/checks/future31-core/source80-81-helper3-independent-foundations-v1'
assert not DEST.exists()
def path(n): return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
d=json.loads(Path('/tmp/root-source80-81-helper3-independent-foundations31-semantic-v2.json').read_text())
native='/tmp/root-source80-81-helper3-independent-foundations31-actual-v2.json'
n=json.loads(Path(native).read_text());assert n['actual_exit_code']==0 and n['protection_errors']==[]
allrefs={r['file']:r for r in d['direct_evidence']}
for p in ['/tmp/root-source80-81-helper3-independent-foundations31-semantic-v2.json',native,n['log'],'/tmp/review-root-source80-81-helper3-independent-foundations31-v2.py','/tmp/run-review-root-source80-81-helper3-independent-foundations31-v2.py','/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json',str(Path(__file__))]: allrefs[p]=ref(p)
aliases={}
for name,r in allrefs.items():
 p=path(name);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
 q=DEST/'original-byte-aliases'/r['sha256']/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists(): assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(q)}
d['actual_reader']=aliases[native]['original_byte_copy'];d['actual_finalizer']=d['actual_reader']
d['actual_reader_original_byte_aliases']={name:aliases[name]['original_byte_copy'] for name in [native,n['log'],'/tmp/review-root-source80-81-helper3-independent-foundations31-v2.py','/tmp/run-review-root-source80-81-helper3-independent-foundations31-v2.py','/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json']}
d['all_original_byte_aliases']=aliases
d['retained_genuine_reader1_failure']={'native':aliases['/tmp/root-source80-81-helper3-independent-foundations31-actual-v1.json']['original_byte_copy'],'reason':'Reviewer AST literal extraction omitted the computed PEER_PINS dict; NEW reader2 supplies the exact frozen map. No production helper or mathematical input changed.'}
d['code_approval_scope']='Exact helper3 code and pinned inputs only. Root must execute its own fresh parser preflight/application; this reviewer invoked no producer or fixture and approved no new whole coverage.'
d['durable_closure_scope']='Exact leaf copies only; no snapshot trees, dependency .lake, or recursive peer histories copied. Original measured reader body and times preserved.'
OUT=DEST/'root-source80-81-helper3-full-code-and-actual-inputs-independent-foundations31-closed-peer-v1.json';OUT.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'peer':ref(OUT),'actual_reader':d['actual_reader'],'originals':len(aliases),'actual_exit_code':n['actual_exit_code'],'elapsed_seconds':n['elapsed_seconds']}))
