from pathlib import Path
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future32-applied/conditional28-independent-foundations-v1';assert not D.exists()
B=Path('/tmp/applied-conditional28-independent-foundations32-v3');F=B/'applied-conditional28-full-current-components-prospective387-whole-independent-foundations32-findings-v1.json';P=B/'applied-conditional387-two-qualifiers-full29-independent-foundations32-findings-v1.json';N=Path('/tmp/applied-conditional28-full-math-and-narrow-independent-foundations32-actual-v3.json');Q=R/'book/coverage/checks/future31-applied/conditional28-author-components-v1/conditional28-full-source-current-and-prospective387-independent-review-request31-v1.json'
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
f=json.loads(F.read_bytes());p=json.loads(P.read_bytes());q=json.loads(Q.read_bytes());n=json.loads(N.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]and f['errors']==p['errors']==[]
refs={}
def collect(x):
 if isinstance(x,dict):
  if {'file','sha256'}<=x.keys()and isinstance(x['file'],str):refs[x['file']]=x
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(f);collect(p)
for r in q['full_file_original_byte_aliases'].values():refs[r['file']]=r
paths=[F,P,N,path(n['log']),Path('/tmp/review-applied-conditional28-whole-and-narrow-independent-foundations32-v3.py'),Path('/tmp/run-review-applied-conditional28-whole-and-narrow-independent-foundations32-v3.py'),Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),Path(__file__)]
for x in paths:refs[str(x)]=ref(x)
aliases={}
for name,r in refs.items():
 s=path(name);assert sha(s)==r['sha256']
 if s.is_relative_to(R)and '.lake'not in s.parts:aliases[name]={'original':r,'already_durable_exact_reference':ref(s)};continue
 t=D/'exact-original-by-sha256'/r['sha256']/s.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==s.read_bytes()
 else:t.write_bytes(s.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(t)}
def a(name):return aliases[str(name)].get('original_byte_copy',aliases[str(name)].get('already_durable_exact_reference'))
common={'actual_reader':a(N),'actual_finalizer':a(N),'actual_finalizer_original_byte_aliases':{str(x):a(x)for x in paths[2:]},'bounded_original_ref_aliases':aliases,'required_evidence_artifacts_sha256':{a(name)['file']:r['sha256']for name,r in refs.items()},'allcurrent1248_Source81assets31_installed_raw_owner31five_guarded_unchanged':True,'no_recursive_snapshots_lake_trees_or_old_peer_packages_copied':True,'one_genuine_combined_mathematical_and_fresh_full29_parser_reader_not_two_fabricated_natives':True}
f.update(common);p.update(common)
f['original_full_semantic_findings']=a(F);p['original_full_narrow_findings']=a(P)
for k in ['genuine_original_reader1_prefix_assumption_failure','genuine_original_reader2_historical_code_assumption_failure']:
 for role,r in list(f[k].items()):
  if isinstance(r,dict)and {'file','sha256'}<=r.keys():f[k][role]=a(r['file'])
FM=D/'applied-conditional28-entire-source-current387-components-prospective387-whole-independent-foundations32-closed-peer-v1.json';FM.write_text(json.dumps(f,indent=2)+'\n');p['supporting_closed_independent_full28_math_peer']=ref(FM)
NP=D/'applied-conditional387-two-exact-qualifiers-full-literal-support-fresh29-parser-independent-foundations32-closed-peer-v1.json';NP.write_text(json.dumps(p,indent=2)+'\n')
print(json.dumps({'math_peer':ref(FM),'narrow_peer':ref(NP),'actual_reader_elapsed_seconds':n['elapsed_seconds'],'bounded_refs':len(refs)}))
