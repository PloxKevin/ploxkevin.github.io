from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased');OUT=R/'book/coverage/checks/applied-future29/current65-identity-v1';P=Path('/tmp/applied29-current65-identity-v2/applied29-current65-identity-offer-draft-v2.json');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):p=Path(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def put(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def checked(q):assert {'file','sha256'}<=set(q);p=path(q['file']);assert sha(p)==q['sha256'];return read(p)
def prepare(peername,peerhash):
 assert sha(P)=='b7a493754d8490485066be5b8ae2b8e5548b638da9c10f509928ed8a0d81299a';offer=read(P)
 assert offer['proof_files']=={} and offer['new_material_keys']==[] and offer['new_exercises']==[]
 peer=checked({'file':peername,'sha256':peerhash});assert peer['status']=='passed_independent_exact_applied29_current65_identity_only_candidate_mechanics' and peer['errors']==[]
 for key in ['candidate','candidate_promotions']:assert peer[key]['sha256']==offer[key]['sha256']
 assert peer['offer']['sha256']==sha(P)
 for key,oldname in [('candidate','applied.json'),('candidate_promotions','applied-promotions.json')]:
  data=checked(offer[key]);data.pop('current65_owner_identity');old=checked(checked(offer['original_current64_offer'])[key]);assert data==old
  data.pop('current64_owner_identity');original=R/'book/coverage'/oldname;assert json.dumps(data,indent=2,ensure_ascii=False)+'\n'==original.read_text()
 assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';ctx=read(C);held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
 originals={};pool={}
 def merge(n,h):assert n not in originals or originals[n]==h;originals[n]=h
 def alias(n,q):
  assert {'file','sha256'}<=set(q)<={'file','sha256','bytes'};p=path(q['file']);assert sha(p)==q['sha256']
  if 'bytes' in q:assert type(q['bytes']) is int and q['bytes']==p.stat().st_size
  pool.setdefault((n,q['sha256']),[]).append(p);merge(q['file'],q['sha256'])
 for d in [offer,peer]:
  for field in ['required_evidence_artifacts_sha256','closed_evidence_sha256']:
   for n,h in d.get(field,{}).items():merge(n,h)
  for n,q in d.get('original_closed_byte_aliases',{}).items():alias(n,q)
 for q in [ref(P),{'file':peername,'sha256':peerhash},offer['candidate'],offer['candidate_promotions'],offer['actual_finalizer'],peer['actual_finalizer'],ref(Path(__file__))]:merge(q['file'],q['sha256'])
 for d in [offer,peer]:
  for q in d.values():
   if isinstance(q,dict) and {'file','sha256'}<=set(q)<={'file','sha256','bytes'}:merge(q['file'],q['sha256'])
 mutables=set(ctx['owners_sha256'])|{'book/coverage/inventory.json','book/coverage/material-corrections.json'};targets={}
 for n,h in originals.items():
  p=path(n)
  possibilities=[p]+pool.get((n,h),[])
  valid=[q for q in possibilities if q.is_file() and sha(q)==h];assert valid,n
  physical=[q for q in valid if q.resolve().is_relative_to(R) and not q.is_symlink() and str(q.relative_to(R)) not in mutables]
  targets[(n,h)]=(valid[0],physical[0] if physical else OUT/'original-closed-bytes'/h/p.name)
 def guard():
  for n,h in held.items():assert sha(path(n))==h,n
  for (n,h),(p,_) in targets.items():assert sha(p)==h,n
 guard();return offer,peer,targets,pool,held

def apply(peername,peerhash):
 old,peer,targets,pool,held=prepare(peername,peerhash);assert not OUT.exists();OUT.mkdir(parents=True)
 closure={};aliases={}
 for (n,h),(source,target) in targets.items():
  if not target.exists():
   target.parent.mkdir(parents=True,exist_ok=True)
   with target.open('xb') as f:f.write(source.read_bytes())
  assert sha(target)==h;q=ref(target);assert q['file'] not in closure or closure[q['file']]==h;closure[q['file']]=h
  if q['file']!=n:aliases[n]=q
 for (n,h),options in pool.items():
  rr=ref(targets[(ref(options[0])['file'],h)][1]) if (ref(options[0])['file'],h) in targets else ref(options[0])
  assert rr['file'] in closure and closure[rr['file']]==h
  assert n not in aliases or aliases[n]['sha256']==h;aliases.setdefault(n,rr)
 def resolved(q):return ref(targets[(q['file'],q['sha256'])][1])
 candidate=resolved(old['candidate']);promotions=resolved(old['candidate_promotions']);originalpeer=resolved({'file':peername,'sha256':peerhash});author=resolved(old['actual_finalizer']);reader=resolved(peer['actual_finalizer'])
 # Exact original bytes are the independent decision. This interface changes
 # only retrieval pointers and does not add a semantic decision or review time.
 INTERFACE=OUT/'applied29-current65-original-independent-peer-pointer-alias-interface-v1.json'
 put(INTERFACE,{'status':'exact_original_independent_peer_pointer_alias_interface','errors':[],'candidate':candidate,'candidate_promotions':promotions,'original_peer':originalpeer,'original_peer_status':peer['status'],'original_peer_sha256':peerhash,'original_peer_body_and_review_time_preserved':True,'no_new_semantic_review_or_review_time_claim':True,'actual_finalizer':reader,'actual_author_preparation':author,'new_proof_sources':0,'new_mathematical_or_status_decisions':0,'required_evidence_artifacts_sha256':closure,'original_closed_byte_aliases':aliases});closure[ref(INTERFACE)['file']]=sha(INTERFACE)
 CAT=OUT/'original-closed-byte-aliases-v1.json';put(CAT,{'status':'exact_original_bytes_with_physical_root_aliases','original_closed_byte_aliases':aliases,'closed_evidence_sha256':closure});closure[ref(CAT)['file']]=sha(CAT)
 final=copy.deepcopy(old);final.update(status='applied29_current65_zero_proof_identity_offer_with_exact_original_independent_peer_alias_interface',candidate=candidate,candidate_promotions=promotions,mapped_ledger=candidate['file'],mapped_ledger_sha256=candidate['sha256'],mapped_promotions=promotions['file'],mapped_promotions_sha256=promotions['sha256'],original_tmp_offer=resolved(ref(P)),original_complete_current65_independent_peer=originalpeer,final_independent_candidate_mapping_peer=ref(INTERFACE),final_independent_mapping_actual=reader,actual_finalizer=author,required_evidence_artifacts_sha256=closure,original_closed_byte_aliases=aliases,original_closed_byte_aliases_catalog=ref(CAT),normalized_retrieval_scope='Candidate, promotions and original independent peer byte bodies are unchanged; only top-level retrieval refs/closure are normalized to physical Root aliases.')
 for key,q in list(final.items()):
  if isinstance(q,dict) and {'file','sha256'}<=set(q)<={'file','sha256','bytes'} and (q['file'],q['sha256']) in targets:final[key]=resolved(q)
 FINAL=OUT/'applied29-current65-identity-offer-root-relative-v1.json';put(FINAL,final)
 for n,h in held.items():assert sha(path(n))==h,n
 for n,h in closure.items():assert sha(R/n)==h,n
 print(json.dumps({'status':'passed_exact_applied29_current65_identity_root_relative_finalization','offer':ref(FINAL),'candidate':candidate,'candidate_promotions':promotions,'original_peer':originalpeer,'alias_interface':ref(INTERFACE),'evidence_count':len(closure),'aliases_count':len(aliases),'proof_files':{},'live_owner_written':False}))
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--peer',required=True);a.add_argument('--peer-sha256',required=True);a.add_argument('--apply',action='store_true');args=a.parse_args()
 if args.apply:apply(args.peer,args.peer_sha256)
 else:prepare(args.peer,args.peer_sha256);print(json.dumps({'status':'passed_readonly_applied29_current65_finalizer_preflight','copies_or_offers_written':False}))
