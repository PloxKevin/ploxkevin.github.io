from pathlib import Path
import copy, hashlib, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
DEST=Path('/tmp/foundations-source81-disjoint-inverse31-v3')
BASE=ROOT/'book/coverage/checks/future30-foundations/current79-completed90-association-v1/foundations30-completed90-current79-pair-bound-candidate-v1.json'
CAND=Path('/tmp/foundations-source81-four-family-actual8-bound31-v2/foundations31-current81-real8-pair-bound-candidate-v2.json')
OLDINV=Path('/tmp/foundations-source81-four-family-actual8-bound31-v2/foundations31-current81-real8-pair-bound-exact-inverse-v2.json')
OLDOFFER=ROOT/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/foundations31-current81-real8-pair-bound-final-offer-v3.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def put(p,d):
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
assert not DEST.exists()
assert sha(BASE)=='4e84206199aa241e1e4ee95f59062bcbe78035bb6443281e398a02c1b3f3ae03'
assert sha(CAND)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a'
assert sha(OLDINV)=='19e6b07fa398e98a1e3f5dc6dbbf19deba7323ae0bb34bcda99e01656cde8f54'
assert sha(OLDOFFER)=='3c7a57863672499f3d76033fc6c123d6791f67e33aa4a099815c4a5213fb84c4'
a=json.loads(BASE.read_bytes());b=json.loads(CAND.read_bytes());patches=[]
assert set(b)-set(a)=={'current31_source81_four_family_draft'} and set(a)<=set(b)
for key in a:
 if a[key]==b[key]:continue
 if key in ['exercises','material_claims','surrounding_prose_reviews']:
  assert len(a[key])==len(b[key])
  for i,(x,y) in enumerate(zip(a[key],b[key])):
   if x==y:continue
   if isinstance(x,dict) and isinstance(y,dict) and set(x)==set(y) and {k:v for k,v in x.items() if k!='source_sha256'}=={k:v for k,v in y.items() if k!='source_sha256'}:
    patches.append({'pointer':[key,i,'source_sha256'],'before':copy.deepcopy(x['source_sha256']),'after':copy.deepcopy(y['source_sha256'])})
   else:patches.append({'pointer':[key,i],'before':copy.deepcopy(x),'after':copy.deepcopy(y)})
 else:patches.append({'pointer':[key],'before':copy.deepcopy(a[key]),'after':copy.deepcopy(b[key])})
appended='current31_source81_four_family_draft'
# The appended field has its own explicit add/remove operation; no parent/child overlap.
allp=[tuple(p['pointer']) for p in patches]+[(appended,)]
assert len(set(allp))==len(allp)
assert all(not (len(x)<len(y) and y[:len(x)]==x) for x in allp for y in allp)
def parent(d,p):
 for k in p[:-1]:d=d[k]
 return d
forward=copy.deepcopy(a)
for p in patches:
 q=parent(forward,p['pointer']);k=p['pointer'][-1]
 assert q[k]==p['before'];q[k]=copy.deepcopy(p['after'])
assert appended not in forward;forward[appended]=copy.deepcopy(b[appended])
assert forward==b and (json.dumps(forward,indent=2)+'\n').encode()==CAND.read_bytes()
reverse=copy.deepcopy(b);assert reverse.pop(appended)==b[appended]
for p in reversed(patches):
 q=parent(reverse,p['pointer']);k=p['pointer'][-1]
 assert q[k]==p['after'];q[k]=copy.deepcopy(p['before'])
assert reverse==a and (json.dumps(reverse,indent=2)+'\n').encode()==BASE.read_bytes()
# Ensure validation never mutates the saved patch protocol.
for p in patches:
 q=parent(a,p['pointer']);r=parent(b,p['pointer']);k=p['pointer'][-1]
 assert q[k]==p['before'] and r[k]==p['after']
DEST.mkdir()
interface=DEST/'foundations31-current81-real8-pair-bound-disjoint-exact-inverse-v3.json'
put(interface,{'status':'exact_strict_disjoint_forward_inverse_preserving_original_owner30_bytes','original':ref(BASE),'candidate':ref(CAND),'patches':patches,'appended_field':appended,'appended_field_after':copy.deepcopy(b[appended]),'original_body_sha256':sha(BASE),'candidate_body_sha256':sha(CAND),'original_serialization':{'indent':2,'ensure_ascii':True,'trailing_newline':True},'strict_forward_assertions_passed':True,'strict_reverse_assertions_passed':True,'disjoint_json_pointers_verified':True,'original_overlapping_inverse_preserved':ref(OLDINV),'original_author0_outer_offer_preserved':ref(OLDOFFER),'candidate_changed':False,'whole_candidate_current_installation_claimed':False,'canonical_pairs_pending':False})
o=json.loads(OLDOFFER.read_bytes());o['exact_inverse']=ref(interface)
o['original_preparation2_outer_offer']=ref(OLDOFFER)
o['original_overlapping_inverse_protocol']=ref(OLDINV)
o['inverse_protocol_repair']={'only_inverse_interface_and_outer_offer_changed':True,'candidate_bytes_unchanged':ref(CAND),'reason':'Earlier reverse validation assigned the saved whole-row before dictionary by reference, so later nested identity reversals mutated the persisted intermediate before. New disjoint pointers and deepcopy replay preserve strict before/after identities in both directions. Original actual author0 and reviewer failures remain historical.'}
o['theorem_only_named_correspondence']={k:v['public_theorem_names'] for k,v in b[appended]['proof_files'].items()}
assert sum(map(len,o['theorem_only_named_correspondence'].values()))==41
put(DEST/'foundations31-current81-real8-pair-bound-final-offer-v4-unclosed.json',o)
print(json.dumps({'interface':ref(interface),'candidate':ref(CAND),'patches':len(patches),'strict_forward_reverse':True}))
