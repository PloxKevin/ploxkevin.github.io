from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');B=ROOT/'book/coverage/checks/modules-future26/smoothing'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':H(p)}
def checkref(r):
 p=ROOT/r['file'] if not r['file'].startswith('/') else Path(r['file']);assert H(p)==r['sha256'],str(p);return p
request=B/'modules-smoothing44-canonical-source-original-review-binding-request26-v1.json';assert H(request)=='99170dae64227a83c7f6fba341c57b5aaca759e3b1bbd79e4bd2fed22f5b59c1'
q=read(request);readyfile=checkref(q['canonical_readiness']);r=read(readyfile);peerfile=checkref(q['original_full_whole_source_review']);peer=read(peerfile)
assert peer==q['entire_original_full_whole_source_review_body_and_time']==r['entire_original_full_source_peer_body_and_time']
assert peer['errors']==[] and peer['whole_exercise_approved'] is True and peer['remaining_full_literal_bridges']==[]
source=checkref(r['source']);snap=checkref(r['source_snapshot']);assert source.read_bytes()==snap.read_bytes()==Path(peer['proof_source']['file']).read_bytes()
text=source.read_text();assert len(re.findall(r'^theorem ',text,re.M))==r['public_theorem_count']==q['public_theorem_count']==44
names=peer['exercise_lean_declarations'];assert len(names)==len(set(names))==44
for name in names:
 namespace,short=name.rsplit('.',1);assert 'namespace '+namespace in text and re.search(r'^theorem '+re.escape(short)+r'\b',text,re.M)
assert len(r['actual_canonical_pair'])==2
for row in r['actual_canonical_pair']:
 p=checkref(row);a=read(p);assert type(a['exit_code'])is int and a['exit_code']==0 and a['source_unchanged'] is True
 assert a['source_sha256_before']==a['source_sha256_after']==r['source']['sha256']
 assert a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['command'] in [['lake','env','lean','SafeLearning/CompleteModulesSmoothingClassifier26.lean'],['lake','build','SafeLearning.CompleteModulesSmoothingClassifier26']]
 assert H(ROOT/a['log'])==a['log_sha256'];checkref(row['log'])
aliases=r['original_TMP_byte_copies'];assert len(aliases)==119
for original,row in aliases.items():
 p=checkref(row);assert H(Path(original))==row['sha256'],original
for name,digest in q['closed_execution_evidence_sha256'].items():assert H(ROOT/name)==digest,name
failure=read(checkref(q['preserved_collector_only_precompiler_failure']));assert type(failure['actual_exit_code'])is int and failure['actual_exit_code']==1
inv=read(ROOT/'book/coverage/inventory.json');assert H(ROOT/'book/coverage/inventory.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
ex={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']}
assert ex[peer['entire_exercise_record']['key']]==peer['entire_exercise_record']
for row in peer['material_units']:assert units[row['source_unit_key']]==row['entire_inventory_record']
assert len(peer['material_units'])==6
manifest=read(ROOT/'reports/full-coverage/checkpoint-25-manifest.json');frozen=manifest['working_inputs_sha256']
for name,digest in r['protected_input_sha256'].items():
 if name=='book/coverage/inventory.json' or name=='SafeLearning/lyapunov-mpc.html':assert frozen[name]==digest
 else:assert H(ROOT/name)==digest,name
correction=read(ROOT/'reports/full-coverage/source53-correction-application-v1.json');assert correction['selected25_proof_sources_unchanged']==1156 and correction['five_installed25_owner_ledgers_unchanged'] is True
assert correction['source_after']['sha256']==H(ROOT/'SafeLearning/lyapunov-mpc.html')
out={'status':'passed_independent_smoothing44_canonical_source_original_whole_review_binding','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_applied','request':ref(request),'canonical_readiness':ref(readyfile),'canonical_source':r['source'],'original_full_whole_source_review':ref(peerfile),'entire_original_full_whole_source_review_body_and_time':peer,'actual_canonical_pair':r['actual_canonical_pair'],'canonical_public_theorem_count':44,'original_TMP_byte_alias_count':119,'original_TMP_byte_copies':aliases,'whole_exercise_approved':True,'material_units':peer['material_units'],'current53_unchanged_exercise_record':ex[peer['entire_exercise_record']['key']],'current53_inventory':ref(ROOT/'book/coverage/inventory.json'),'source53_actual_application':ref(ROOT/'reports/full-coverage/source53-correction-application-v1.json'),'closed_execution_evidence_sha256':q['closed_execution_evidence_sha256'],'scope':'Narrow exact original-body/time/name/evidence binding only. Both actual canonical records and all119 original aliases checked. All seven entire exercise/material records unchanged52-to53; selected1156, unchanged current30 assets and exact archived52 Lyapunov/inventory protected. Original full mathematical scope and CI premise retained; no semantic redecision, fresh compiler, aggregate or live owner write.'}
p=Path('/tmp/modules-smoothing44-canonical-original-review-binding-independent-applied-confirmation26-v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'passed','report':ref(p)}))
