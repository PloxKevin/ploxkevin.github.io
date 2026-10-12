from pathlib import Path
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
TMP=Path('/tmp/foundations-source81-four-family-actual8-bound31-v2')
DEST=ROOT/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1'
assert not DEST.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
original=TMP/'foundations31-current81-real8-pair-bound-final-offer-v2.json';d=json.loads(original.read_bytes())
refs={}
def collect(x):
 if isinstance(x,dict):
  if {'file','sha256'}<=x.keys() and isinstance(x['file'],str):
   assert x['file'] not in refs or refs[x['file']]['sha256']==x['sha256'];refs[x['file']]=x
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(d)
NATIVE='/tmp/foundations-source81-four-family-actual8-bound31-preparation-actual-v2.json'
n=json.loads(Path(NATIVE).read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]
for p in [str(original),NATIVE,n['log'],'/tmp/prepare-foundations-source81-four-family-actual8-bound31-v2.py','/tmp/run-prepare-foundations-source81-four-family-actual8-bound31-v2.py','/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json','/tmp/prepare-foundations-source81-four-family-provisional31-v1.py','/tmp/run-prepare-foundations-source81-four-family-provisional31-v1.py','/tmp/foundations-source81-four-family-provisional31-preparation-actual-v1.json','/tmp/foundations-source81-four-family-provisional31-preparation-actual-v1.log',str(Path(__file__))]:refs[p]=ref(p)
aliases={}
for name,r in refs.items():
 p=path(name);assert sha(p)==r['sha256']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 if p.is_relative_to(ROOT) and not name.startswith('book/coverage/inventory.json'):
  aliases[name]={'original':r,'already_durable_original_byte_alias':ref(p)};continue
 q=DEST/'exact-original-by-sha256'/r['sha256']/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(q)}
def alias(name):
 x=aliases[name];return x.get('original_byte_copy',x.get('already_durable_original_byte_alias'))
d['candidate']=alias(d['candidate']['file']);d['exact_inverse']=alias(d['exact_inverse']['file'])
d['original_actual_bound_offer']=alias(str(original))
d['actual_finalizer']=alias(NATIVE)
d['actual_finalizer_original_byte_aliases']={p:alias(p) for p in [NATIVE,n['log'],'/tmp/prepare-foundations-source81-four-family-actual8-bound31-v2.py','/tmp/run-prepare-foundations-source81-four-family-actual8-bound31-v2.py','/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json']}
d['all_original_byte_aliases']=aliases
d['required_evidence_artifacts_sha256']={alias(name)['file']:r['sha256'] for name,r in refs.items()}
d['original_whole_owner30_body_time_and_old_provisional_pending_verdict_preserved']=True
d['exact_original_Growth10_new_closed_whole_peer_bound']=True
d['actual_four_canonical_sources_eight_commands_41_theorems_45_public_declarations_bound']=True
d['current_owner_selection_aggregate_or_publication_installation_claimed']=False
d['final_independent_mapping_review_pending']=True
out=DEST/'foundations31-current81-real8-pair-bound-final-offer-v3.json';out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'offer':ref(out),'candidate':d['candidate'],'exact_inverse':d['exact_inverse'],'actual_finalizer':d['actual_finalizer'],'original_leaf_refs':len(refs)}))
