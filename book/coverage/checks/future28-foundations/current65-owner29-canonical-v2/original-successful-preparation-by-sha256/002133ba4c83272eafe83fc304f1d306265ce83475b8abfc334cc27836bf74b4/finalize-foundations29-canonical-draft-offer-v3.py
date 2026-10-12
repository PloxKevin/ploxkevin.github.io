from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/current65-owner29-canonical-v2';B=D.relative_to(R).as_posix()
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def ref(n):return {'file':p(n).relative_to(R).as_posix() if p(n).is_relative_to(R) else str(p(n)),'sha256':sha(n)}
def read(n):return json.loads(p(n).read_bytes())
def data(x):return (json.dumps(x,indent=2)+'\n').encode()
offerpath=B+'/foundations29-current65-canonical-offer-draft-v2.json';assert sha(offerpath)=='27ce0d9ab64b49abc13afd156b72627e8bf36b5e9d9487c0405fa0bc118873fb'
o=read(offerpath);native='/tmp/foundations-owner29-current65-canonical-preparation-actual-v2.json';a=read(native)
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0
assert a['helper']['sha256']=='a2997a8672c78d5099441513bfccce6162f7640bcbf26d18de84ad6ee73a8adb' and sha(a['helper']['file'])==a['helper']['sha256']
assert sha(a['log']['file'])==a['log']['sha256'];out=read(a['log']['file']);assert out['candidate']==o['candidate'] and out['exact_interface']==o['exact_interface'] and out['six_sources_public_bodies_actual_commands']==[6,53,12]
context=read('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def guard():
 for f in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in context[f].items():assert sha(n)==h,n
 for n,h in o['required_evidence_artifacts_sha256'].items():assert sha(n)==h,n
 assert sha(o['candidate']['file'])==o['candidate']['sha256'] and sha(o['exact_interface']['file'])==o['exact_interface']['sha256']
guard();planned={};aliases={}
for n in [native,a['helper']['file'],a['log']['file'],str(Path(__file__))]:
 source=p(n);h=sha(n);dest=D/'original-successful-preparation-by-sha256'/h/source.name;assert not dest.exists();planned[dest]=source.read_bytes();aliases[n]={'file':dest.relative_to(R).as_posix(),'sha256':h}
closure=copy.deepcopy(out);closure.update(actual_preparation=aliases[native],original_helper=aliases[a['helper']['file']],raw_log=aliases[a['log']['file']],original_preparation_byte_aliases=aliases,actual_original_command=a['command'],actual_original_cwd=a['cwd'],started_at_utc=a['started_at_utc'],finished_at_utc=a['finished_at_utc'],elapsed_seconds=a['elapsed_seconds'],independent_final_mapping_peer_pending=True)
cp=D/'foundations29-current65-canonical-author-preparation-closure-v2.json';assert not cp.exists();cb=data(closure);planned[cp]=cb;cr={'file':cp.relative_to(R).as_posix(),'sha256':hashlib.sha256(cb).hexdigest()}
offer=copy.deepcopy(o);offer.update(candidate_preparation_actual_pending=False,author_actual_finalizer=aliases[native],author_actual_finalizer_scope='Genuine guarded author candidate/preparation2 execution, explicitly not the separate independent mapping reader.',original_provisional_pair_bound_offer=ref(offerpath),actual_author_preparation_closure=cr,independent_final_candidate_mapping_peer_pending=True,final_mapping_peer=None)
es=dict(o['required_evidence_artifacts_sha256'])
for r in list(aliases.values())+[cr,o['candidate'],o['exact_interface'],ref(offerpath)]:
 assert r['file'] not in es or es[r['file']]==r['sha256'];es[r['file']]=r['sha256']
offer['required_evidence_artifacts_sha256']=es;offer['additional_frozen_inputs']=es.copy()
fp=D/'foundations29-current65-canonical-offer-draft-v3.json';assert not fp.exists();planned[fp]=data(offer)
guard()
for n,b in planned.items():assert not n.exists() and n.is_relative_to(D)
for n,b in planned.items():n.parent.mkdir(parents=True,exist_ok=True);n.write_bytes(b)
guard();assert all(sha(n)==h for n,h in es.items())
print(json.dumps({'candidate':o['candidate'],'new_offer':ref(fp),'actual_author_preparation_closure':cr,'author_finalizer':aliases[native],'required_evidence_count':len(es),'independent_final_mapping_peer_pending':True,'coverage_complete':False}))
