from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/current79-three-fragments-final-v1';assert not B.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def put(p,d):
 with p.open('x') as f:f.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
P=R/'book/coverage/checks/modules-future30/current79-real30-pair-bound-v1/modules30-current79-real30-pair-bound-offer-draft-v2.json';assert sha(P)=='ab47d92dbe12d65d6eb30cd817a0282170aabe8eaeada24d21979776e4977a0f';o=json.loads(P.read_bytes());C=R/o['candidate']['file'];assert sha(C)==o['candidate']['sha256'];before=json.loads(C.read_bytes());c=copy.deepcopy(before)
RP=R/'reports/full-coverage/source79-authoring-fragments-sync-v1.json';NP=R/'reports/full-coverage/source79-authoring-fragments-sync-execution-v1.json';assert sha(RP)=='f911233bb5840e57a2f74ec2f204f8ee7bb972950129a6f241701f0ff689c9db' and sha(NP)=='d61186057f933fec25c71286f67aed00f2329a9dc7a144a24aebbb2ca45e44d4';report=json.loads(RP.read_bytes());native=json.loads(NP.read_bytes());assert native['status']=='passed' and type(native['actual_exit_code']) is int and native['actual_exit_code']==0 and native['actual_command']==['python3','book/coverage/checks/root_sync_reviewed79_application_fragments_v1.py','--apply'] and native['actual_workdir']==str(R);assert sha(R/native['log'])==native['log_sha256'];assert len(report['fragments'])==3 and sum(len(x['replacements']) for x in report['fragments'])==5 and report['integrated31_assets_and_old1197_proofs_and_historical29_raw5_unchanged'] is True
changes=[];originals=[]
for x in report['fragments']:
 p=R/x['source'];old=R/report['original_fragment_directory']/p.name;assert sha(old)==x['before_sha256']==c['chapter_fragment_sha256'][x['source']] and sha(p)==x['after_sha256'];body=old.read_bytes().decode()
 for z in x['replacements']:assert body.count(z['before'])==1;body=body.replace(z['before'],z['after'])
 assert body.encode()==p.read_bytes();back=body
 for z in reversed(x['replacements']):assert back.count(z['after'])==1;back=back.replace(z['after'],z['before'])
 assert back.encode()==old.read_bytes();changes.append({'path':['chapter_fragment_sha256',x['source']],'existed':True,'before':x['before_sha256'],'after':x['after_sha256']});c['chapter_fragment_sha256'][x['source']]=x['after_sha256'];originals.append(ref(old));assert x['source'] not in c['source_sha256']
field='actual_source79_authoring_fragment_sync30';assert field not in c;c[field]={'status':'passed_actual_three_authoring_fragment_identity_overlay_only','report':ref(RP),'actual_execution':ref(NP),'original_pair_bound_candidate':ref(C),'original_three_fragment_bytes':originals,'three_fragment_keys':list(x['source'] for x in report['fragments']),'five_exact_already_reviewed_substitutions':True,'math_source_body_status_declaration_proof_pair_and_count_metadata_unchanged':True,'owner_installation_pending':True,'coverage_complete':False};changes.append({'path':[field],'existed':False,'before':None,'after':copy.deepcopy(c[field])})
assert all(c[k]==before[k] for k in before if k!='chapter_fragment_sha256');B.mkdir(parents=True);CP=B/'modules30-current79-real30-three-fragments-candidate-v1.json';put(CP,c);rev=copy.deepcopy(c)
for x in reversed(changes):
 d=rev
 for k in x['path'][:-1]:d=d[k]
 if x['existed']:d[x['path'][-1]]=copy.deepcopy(x['before'])
 else:del d[x['path'][-1]]
assert rev==before and (json.dumps(rev,indent=2,ensure_ascii=False)+'\n').encode()==C.read_bytes()
IP=B/'modules30-three-fragments-metadata-only-exact-inverse-v1.json';put(IP,{'status':'exact_three_authoring_fragment_SHA_and_fresh_sync_evidence_only_full_inverse_to_original_pair_bound_candidate_verified','original_pair_bound_candidate':ref(C),'candidate':ref(CP),'changes':changes,'original_pair_bound_inverse':o['exact_inverse_interface'],'exact_original_candidate_byte_inverse':True,'every_math_row_status_proof_metadata_name_native_pair_body_time_and_count_unchanged':True,'coverage_complete':False})
req=copy.deepcopy(o['required_evidence_artifacts_sha256']);aliases=copy.deepcopy(o['original_closed_byte_aliases'])
for p in [P,C,CP,IP,RP,NP,R/native['log'],*[R/r['file'] for r in originals]]:req[p.relative_to(R).as_posix()]=sha(p)
for x in report['fragments']:req[x['source']]=x['after_sha256']
o.update({'candidate':ref(CP),'exact_inverse_interface':ref(IP),'original_pair_bound_inverse':json.loads(P.read_bytes())['exact_inverse_interface'],'original_pair_bound_offer_before_fragment_sync':ref(P),'actual_source79_authoring_fragment_sync':ref(RP),'actual_source79_authoring_fragment_sync_execution':ref(NP),'fragment_overlay_scope':'Exactly3 existing chapter_fragment_sha256 entries plus one fresh Root sync-evidence metadata field. Source map contains no chapter-fragment paths; all math/status/counts/15 sources30 pairs remain exact.','required_evidence_artifacts_sha256':req,'original_closed_byte_aliases':aliases})
OP=B/'modules30-current79-real30-three-fragments-offer-draft-v1.json';put(OP,o);print(json.dumps({'offer':ref(OP),'candidate':ref(CP),'inverse':ref(IP),'metadata_changed_paths':len(changes),'counts':c['counts'],'math_rows_and15source30pairs_unchanged':True}))
