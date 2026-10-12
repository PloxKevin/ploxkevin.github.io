from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/current79-provisional-owner30-v1';assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
P=Path('/tmp/modules30-current79-provisional-v2/modules30-current79-provisional-offer-v1.json');assert sha(P)=='51117fe3650300a606248f6ecf2cde8372194a21275f157397459db481605951';d=json.loads(P.read_bytes());assert d['actual_canonical_pairs_pending'] is True and d['installation_ready'] is False
N=Path('/tmp/modules30-current79-provisional-preparation-actual-v2.json');n=json.loads(N.read_bytes());assert n['status']=='passed' and type(n['actual_exit_code']) is int and n['actual_exit_code']==0 and n['protection_errors']==[]
I=Path('/tmp/modules-compiled-supply-inventory30-v8.json');assert sha(I)=='1c820840b591f396d50f09966c18ad9e098accf36ca58db18695c393f74bed68';iv=json.loads(I.read_bytes())
C=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');c=json.loads(C.read_bytes());pins={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']};assert all(sha(path(p))==h for p,h in pins.items())
B.mkdir(parents=True);aliases={};bykey={};req={};mutable=set(c['owners_sha256'])
def copy(p):
 p=Path(p);h=sha(p)
 if p.is_relative_to(R) and p.resolve().is_relative_to(R) and p.relative_to(R).as_posix() not in mutable and not p.is_symlink():q=p
 else:
  q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():
   with q.open('xb') as f:f.write(p.read_bytes())
  assert sha(q)==h
 v=ref(q);aliases[str(p)]=v
 if p.is_relative_to(R):aliases[p.relative_to(R).as_posix()]=v
 bykey[str(p)+'::sha256='+h]=v;req[v['file']]=h;return v

def close(v):
 if isinstance(v,list):return [close(x) for x in v]
 if isinstance(v,dict):
  if isinstance(v.get('file'),str) and isinstance(v.get('sha256'),str):
   p=path(v['file']);assert sha(p)==v['sha256'];rr=copy(p);return {**{k:close(x) for k,x in v.items() if k not in ['file','sha256','bytes']},**rr}
  return {k:close(x) for k,x in v.items()}
 return v
# The copied original JSON/native bodies remain untouched; the outer interface only normalizes byte locations.
d=close(d)
for f in iv['families']:
 pp=path(f['full_semantic_peer']['file']);p=json.loads(pp.read_bytes());copy(pp)
 for k,h in p.get('required_evidence_artifacts_sha256',{}).items():
  if isinstance(h,str) and len(h)==64:assert sha(path(k))==h;copy(path(k))
 for row in p.get('closed_original_inputs',[]) if isinstance(p.get('closed_original_inputs',[]),list) else []:
  if 'closed_copy' in row:
   rr=row['closed_copy'];q=path(rr['file']);assert sha(q)==rr['sha256'];v=copy(q)
   if isinstance(row.get('original'),dict):bykey[row['original']['file']+'::sha256='+rr['sha256']]=v
 for field in ['original_closed_byte_aliases','original_byte_aliases','reader_original_byte_aliases']:
  for original,v in p.get(field,{}).items():
   if isinstance(v,dict) and isinstance(v.get('file'),str) and isinstance(v.get('sha256'),str):
    q=path(v['file']);assert sha(q)==v['sha256'];rr=copy(q);bykey[original+'::sha256='+v['sha256']]=rr
for key in ['distinct_exact_Chain49_whole_exercise_review','original_shelf57_intentional_gap_peer','shelf_actual_continuous_control_whole_composition_peer']:
 p=path(iv[key]['file']);dd=json.loads(p.read_bytes());copy(p)
 for k,h in dd.get('required_evidence_artifacts_sha256',{}).items():assert sha(path(k))==h;copy(path(k))
for pp in [P,I,N,path(n['raw_log']),Path('/tmp/prepare-modules30-current79-provisional-v1.py'),Path('/tmp/prepare-modules30-current79-provisional-v2.py'),Path('/tmp/run-modules30-current79-provisional-preparation-v1.py'),Path('/tmp/run-modules30-current79-provisional-preparation-v2.py'),Path('/tmp/modules30-current79-provisional-preparation-actual-v1.json'),Path('/tmp/modules30-current79-provisional-preparation-actual-v1.log'),C,Path(__file__)]:copy(pp)
d['original_TMP_provisional_offer']=copy(P);d['latest_compiled_supply_inventory']=copy(I);d['actual_provisional_candidate_preparation']=copy(N);d['actual_provisional_candidate_preparation_original_byte_aliases']={k:aliases[k] for k in [*n['helper_sha256_before'],n['raw_log']]};d['alias_only_outer_interface_prepared_at_utc']=datetime.now(timezone.utc).isoformat();d['candidate_bytes_and_all_proof_bodies_math_statuses_native_times_unchanged']=True;d['original_closed_byte_aliases']=aliases;d['original_byte_aliases_by_path_and_sha256']=bykey;d['required_evidence_artifacts_sha256']=req;d['not_a_final_pair_bound_offer_or_independent_mapping_approval']=True
O=B/'modules30-current79-provisional-root-relative-offer-v1.json'
with O.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
assert all(sha(path(p))==h for p,h in pins.items());print(json.dumps({'offer':ref(O),'candidate':d['candidate'],'inverse':d['exact_inverse_interface'],'physical_refs':len(req),'aliases':len(aliases),'actual_preparation':d['actual_provisional_candidate_preparation'],'installation_ready':False}))
