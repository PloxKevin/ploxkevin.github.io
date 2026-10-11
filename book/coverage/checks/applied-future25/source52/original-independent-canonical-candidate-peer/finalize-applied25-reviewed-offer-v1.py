from pathlib import Path
import json,hashlib,copy,shutil
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/applied-future25/source52';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
peerpath=Path('/tmp/applied25-seven-source43-canonical-binding-and-candidate-independent-foundations-review-v3.json');assert H(peerpath)=='34efbca1c80755a2aa2a39ce3af30cc9aa176938ee3c2d6ce5bfa91f5d1c409e'
peer=json.loads(peerpath.read_text());assert peer['errors']==[] and 'passed' in peer['status']
draftpath=BASE/'applied-audit25-candidate-source52-additions-v1.json';assert H(draftpath)=='65e1ec899aa568ad7dae18d88bcda3d1914ac317258f9c9c844b4aee00dd34e3';draft=json.loads(draftpath.read_text())
archives=BASE/'original-independent-canonical-candidate-peer';archives.mkdir(exist_ok=True)
paths={str(peerpath)}
def collect(obj):
 if isinstance(obj,dict):
  for k,v in obj.items():
   if isinstance(k,str) and k.startswith('/tmp/') and Path(k).is_file():paths.add(k)
   collect(v)
 elif isinstance(obj,list):
  for v in obj:collect(v)
 elif isinstance(obj,str) and obj.startswith('/tmp/') and Path(obj).is_file():paths.add(obj)
collect(peer)
for version in [1,2,3]:
 for p in [Path('/tmp/check-applied25-canonical-binding-and-candidate-independent-foundations-v'+str(version)+'.py'),Path('/tmp/run-applied25-canonical-binding-and-candidate-independent-foundations-v'+str(version)+'.py'),Path('/tmp/applied25-canonical-binding-and-candidate-independent-foundations-actual-v'+str(version)+'.json'),Path('/tmp/applied25-canonical-binding-and-candidate-independent-foundations-actual-v'+str(version)+'.log')]:
  assert p.is_file();paths.add(str(p))
aliases={}
for n in sorted(paths):
 original=Path(n);dest=archives/original.name;digest=H(original)
 if dest.exists():assert H(dest)==digest
 else:shutil.copyfile(original,dest)
 assert H(dest)==digest;aliases[n]={'file':str(dest.relative_to(ROOT)),'sha256':digest}
assert len({v['file'] for v in aliases.values()})==len(aliases)
actpath=Path('/tmp/applied25-canonical-binding-and-candidate-independent-foundations-actual-v3.json');act=json.loads(actpath.read_text());assert act['actual_exit_code']==0
for v in [1,2]:assert json.loads(Path('/tmp/applied25-canonical-binding-and-candidate-independent-foundations-actual-v'+str(v)+'.json').read_text())['actual_exit_code']==1
originalreview=aliases[str(peerpath)];actualref=aliases[str(actpath)]
ref=lambda p:{'file':str(p.relative_to(ROOT)),'sha256':H(p)}
put=lambda p,o:p.open('x').write(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
candidate={'file':draft['mapped_ledger'],'sha256':draft['mapped_ledger_sha256']};promotions={'file':draft['mapped_promotions'],'sha256':draft['mapped_promotions_sha256']}
for r in [candidate,promotions]:assert H(ROOT/r['file'])==r['sha256']
interface={
 'status':'passed_independent_read_only_applied25_candidate_mechanics_preserved_original_review_interface','errors':[],
 'reviewer':peer['reviewer'],'reviewed_at_utc':peer['reviewed_at_utc'],'candidate':candidate,'candidate_promotions':promotions,
 'original_independent_review':originalreview,'entire_original_independent_review_body_and_time':peer,
 'original_closed_byte_aliases':aliases,'actual_read_only_checker':actualref,'actual_checker_raw_log':aliases[act['raw_log']],
 'interface_prepared_by':'applied_next','interface_prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'normalization_scope':'Only exact canonical pointers and candidate key aliases added. Original independent status, decisions, body, reviewer and review time are preserved entire. This normalization creates no new semantic decision or compiler result.'}
ip=BASE/'applied25-canonical-candidate-independent-foundations-interface-v1.json';put(ip,interface)
cat=BASE/'original-independent-canonical-candidate-peer-byte-aliases-v1.json';put(cat,{'status':'all_original_independent_reader_fail_pass_histories_byte_identically_archived','original_closed_byte_aliases':aliases,'genuine_failed_reader_versions':[1,2],'genuine_passing_reader_version':3,'original_review_body_and_time_unchanged':True})
out=copy.deepcopy(draft)
out['status']='independently_reviewed_isolated_applied25_source52_material_candidate_ready_for_root_selection'
out['errors']=[]
out['original_draft_offer']=ref(draftpath)
out['final_independent_candidate_mapping_peer']=ref(ip)
out['original_final_independent_candidate_mapping_peer']=originalreview
out['actual_isolated_candidate_preparation']=ref(ROOT/'book/coverage/checks/applied-future25/applied25-isolated-material-candidate-actual-v2.json')
out['actual_isolated_candidate_raw_log']=ref(ROOT/'book/coverage/checks/applied-future25/applied25-isolated-material-candidate-actual-v2.log')
out['candidate']=candidate;out['candidate_promotions']=promotions
out['independent_review_original_byte_aliases']=ref(cat)
out['readiness_scope_qualification']=peer['readiness_scope_qualification']
required={draftpath.relative_to(ROOT).as_posix():H(draftpath),ip.relative_to(ROOT).as_posix():H(ip),cat.relative_to(ROOT).as_posix():H(cat)}
for row in aliases.values():required[row['file']]=row['sha256']
for key in ['actual_isolated_candidate_preparation','actual_isolated_candidate_raw_log']:required[out[key]['file']]=out[key]['sha256']
for key in ['original_review_bindings','canonical_path_aliases']:required[draft[key]]=draft[key+'_sha256']
for n,p in draft['proof_files'].items():
 required[n]=p['sha256']
 for k,h in p['evidence_sha256'].items():required[k]=h
for key in ['seven-source43-canonical-source-and-original-history-preparation-v1.json','seven-source43-canonical-paired-build-readiness-v1.json','seven-source43-canonical-pairs-actual-v1.json','seven-source43-canonical-pairs-actual-v1.log','run_seven_source43_canonical_pairs_v1.py','run_seven_source43_canonical_pairs_actual_v1.py','baseline-frozen24-manifest-before-aggregate-original-v1.json','baseline-frozen24-manifest-original-byte-alias-v1.json']:
 p=ROOT/'book/coverage/checks/applied-future25'/key;required[p.relative_to(ROOT).as_posix()]=H(p)
prep=json.loads((ROOT/'book/coverage/checks/applied-future25/seven-source43-canonical-source-and-original-history-preparation-v1.json').read_text())
for row in prep['original_absolute_path_byte_aliases']:required[row['canonical_file']]=row['sha256']
for n,h in required.items():assert H(ROOT/n)==h,n
out['required_evidence_artifacts_sha256']=required;out['additional_frozen_inputs']=sorted(required)
out['finalization_scope']='Independent canonical/body/pair/candidate mechanics and original failure/pass histories added only. Entire draft semantic bodies/times, candidate/promotions, seven43 source rows and fourteen genuine executions unchanged. No live mapping or aggregate25/delivery claim.'
restored=copy.deepcopy(out)
for k in set(out)-set(draft):restored.pop(k)
restored['status']=draft['status'];assert restored==draft
final=BASE/'applied-audit25-candidate-source52-additions-v2-reviewed.json';put(final,out)
print(json.dumps({'offer':ref(final),'peer_interface':ref(ip),'original_peer':originalreview,'archived_originals':len(aliases),'required_closed_artifacts':len(required),'counts':out['counts']}))
