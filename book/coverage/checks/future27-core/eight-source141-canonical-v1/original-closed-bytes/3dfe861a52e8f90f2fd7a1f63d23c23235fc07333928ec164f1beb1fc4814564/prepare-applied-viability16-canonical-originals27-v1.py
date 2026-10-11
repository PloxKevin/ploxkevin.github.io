from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,re
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
requestpath=Path('/tmp/applied-viability16-future27-actual42-full-source-review-request-v2.json');peerpath=Path('/tmp/applied-viability16-actual42-independent-foundations-full-source-review27-v1.json')
assert H(requestpath)=='cd809c27baaeaa4dcf6d7eb27216ba96b997452016d4dc1fb4e983ec61f7da15';assert H(peerpath)=='7248d63a4dd8948d614cd567002b84db955c65af703fb3f55ce658ece9b121f5'
request=json.loads(requestpath.read_text());peer=json.loads(peerpath.read_text());assert peer['errors']==[] and peer['exercise']['whole_exercise_approved']is True
assert len(peer['material_units'])==3 and all(m['whole_unit_approved']is True and not m['missing_clauses']for m in peer['material_units'])
source=Path(request['proof_source']['file']);assert H(source)==peer['proof_source']['sha256']==request['proof_source']['sha256']=='5fb7914b547f74b4bdb5c1e8c64fd21c4e1e088781f75a3981c1561667c1e51a'
assert len(re.findall(r'^theorem\s+',source.read_text(),re.M))==42
standalone=Path(request['actual_standalone']['file']);native=json.loads(standalone.read_text());assert type(native['actual_exit_code'])is int and native['actual_exit_code']==0 and native['protection_errors']==[]
assert H(native['raw_log'])==native['raw_log_sha256'] and H(native['source_snapshot'])==H(source)
base=Path('/tmp/applied-viability16-canonical-preparation27-v1');base.mkdir(exist_ok=False);archive=base/'original-tmp';archive.mkdir();candidate=base/'prospective-canonical';candidate.mkdir();copied=candidate/'CompleteAppliedExplorerSlope27.lean';shutil.copyfile(source,copied);assert copied.read_bytes()==source.read_bytes()
closed=dict(peer['closed_evidence_sha256']);closed[str(peerpath)]=H(peerpath)
for name in ['/tmp/applied-viability16-independent-foundations-full-review27-actual-v3.json','/tmp/applied-viability16-independent-foundations-full-review27-actual-v3.log','/tmp/run-applied-viability16-independent-foundations-full-review27-v3.py']:
 closed[name]=H(name)
reader=json.loads(Path('/tmp/applied-viability16-independent-foundations-full-review27-actual-v3.json').read_text());assert type(reader['actual_exit_code'])is int and reader['actual_exit_code']==0
aliases={}
for name,digest in closed.items():
 p=Path(name);assert H(p)==digest
 if p.is_absolute():
  target=archive/p.name;assert not target.exists();shutil.copyfile(p,target);assert H(target)==digest and target.read_bytes()==p.read_bytes();aliases[name]={'file':str(target),'sha256':digest}
 else:assert H(R/p)==digest
# Archive the two selected full dependency bodies separately without editing them.
deps={}
for name in ['verification/lean/SafeLearning/CompleteModulesValues.lean','verification/lean/SafeLearning/CompleteFoundationsGraphViability.lean']:
 sourcepath=R/name;target=base/sourcepath.name;shutil.copyfile(sourcepath,target);assert sourcepath.read_bytes()==target.read_bytes();deps[name]={'file':str(target),'sha256':H(target)}
packet={'status':'tmp_only_exact_source_and_original_whole_review_canonical_preparation_no_canonical_execution','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/applied_next','current_inventory_at_original_decision':request['current_inventory'],'original_request':{'file':str(requestpath),'sha256':H(requestpath)},'entire_original_request_body_and_time':request,'original_whole_source_peer':{'file':str(peerpath),'sha256':H(peerpath)},'entire_original_whole_source_peer_body_and_time':peer,'prospective_canonical_source':{'file':str(copied),'sha256':H(copied),'intended_root_destination':'verification/lean/SafeLearning/CompleteAppliedExplorerSlope27.lean','intended_named_target':'SafeLearning.CompleteAppliedExplorerSlope27'},'actual_original_standalone':request['actual_standalone'],'original_actual_reader3':{'file':'/tmp/applied-viability16-independent-foundations-full-review27-actual-v3.json','sha256':H('/tmp/applied-viability16-independent-foundations-full-review27-actual-v3.json')},'original_closed_byte_aliases':aliases,'original_closed_evidence_sha256':closed,'selected_dependency_exact_copies':deps,'public_theorem_count':42,'all_public_declarations':peer['all_public_declarations'],'material_units':peer['material_units'],'exercise':peer['exercise'],'precise_component_groups':peer['precise_component_groups'],'canonical_standalone_execution':None,'canonical_named_execution':None,'current55_owned_literal_identity':None,'scope':'TMP-only prospective canonical source byte-copy and full immutable original review/trial/failure/warning/cache/reader history. Preserves all original body/time/decisions. The original source comment says uncompiled draft historically; actual original trial5 and reviewer3 prove the precise packet scope. No current55 identity, canonical source installation, named build, ledger/candidate/integration or current26 amendment claimed. Current55 identity and new protected canonical pair are separate future requirements.'}
out=base/'viability16-42-source-original-whole-review-canonical-preparation-v1.json';assert not out.exists();out.write_text(json.dumps(packet,indent=2)+'\n');print(json.dumps({'packet':str(out),'sha256':H(out),'aliases':len(aliases),'public_theorems':42,'canonical_or_owner_write':False}))
