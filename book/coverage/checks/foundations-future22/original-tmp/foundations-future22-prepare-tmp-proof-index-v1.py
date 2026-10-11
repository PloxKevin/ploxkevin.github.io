from pathlib import Path
import json,hashlib,datetime
R=Path('/home/oxrexkevin/SafetyBased')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
out=Path('/tmp/foundations-future22-tmp-proof-index-v1.json')
assert not out.exists()
expected={
'book/coverage/foundations-audit21-source48-additions-v1.json':'2becbf30d8be360e0872127346bf7e10c84e7bdff3e1670e74da3f81b72720dd',
'book/coverage/foundations.json':'c16c0662b2f74a4d4e30d477d3c8bf0008e2456fdebf506d5f6f6144d150db11',
'book/coverage/build_foundations21.py':'3c7af67b9a17682d26fc8884ecaf7d4bcc0b8012edcb4dea9e82d3c93a100671',
'book/coverage/foundations_promotions21.py':'9529856af764d01e884bbb136c959b22f73107438d59e5ced6ebd4b0c232d63b',
'book/coverage/foundations_held19_current48.py':'29913e29ca24d44276a08c2bb993008e6fb35b64c9b2f1412e33d7ad6b1981e2',
'book/coverage/foundations_material20_current48.py':'901a98799de87358f1154eb51066c15f61f2a150d02bc3b937859c5b637c8890',
'book/coverage/foundations_material21.py':'37124400bfa900f24915394f292ba8925792368680542421d15816e4691ca59d',
'book/coverage/inventory-after-correction48.json':'2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108',
'book/coverage/checks/foundations-future21/foundations-source48-final-mapping-independent-modules-confirmation21-v3.json':'c60ef410d8a4d02a796ffaf6142a2887a12741bc53f9933b897bddb950e29254'}
for p,v in expected.items():assert h(R/p)==v,p
rows=[]
for name,trial,units,status in [
('RKHSBounds22',4,['primer-linalg.html::node-1118','primer-linalg.html::node-1120'],'fresh_whole_peer_approved'),
('WorkedSafety22',4,[f'primer-basics.html::node-{n}' for n in [1467,1477,1483,1486,1495,1497,1498,1500,1565]],'whole_peer_queued'),
('ContinuousLevels22',2,[f'primer-basics.html::node-{n}' for n in [1046,1117,1119]],'whole_peer_queued')]:
 slug={'RKHSBounds22':'rkhs-bounds22','WorkedSafety22':'worked-safety22','ContinuousLevels22':'continuous-levels22'}[name]
 p=Path('/tmp/CompleteFoundations'+name+'.lean');r=Path(f'/tmp/foundations-{slug}-trial{trial}.json');d=json.loads(r.read_text())
 assert d['exit_code']==0 and h(p)==d['source_sha256_before']==d['source_sha256_after']==h(d['preserved_source'])
 assert h(d['log'])==d['log_sha256']
 failed=[]
 for n in range(1,trial):
  q=Path(f'/tmp/foundations-{slug}-trial{n}.json');f=json.loads(q.read_text())
  assert f['exit_code']!=0 and h(f['preserved_source'])==f['preserved_source_sha256'] and h(f['log'])==f['log_sha256']
  failed.append({'record':str(q),'record_sha256':h(q),'exit_code':f['exit_code'],'snapshot':f['preserved_source'],'snapshot_sha256':h(f['preserved_source']),'log':f['log'],'log_sha256':h(f['log'])})
 rows.append({'source':str(p),'source_sha256':h(p),'actual_standalone_record':str(r),'actual_standalone_record_sha256':h(r),'actual_exit_code':0,'preserved_source':d['preserved_source'],'preserved_source_sha256':h(d['preserved_source']),'log':d['log'],'log_sha256':h(d['log']),'historical_failures':failed,'theorem_count':sum(1 for l in p.read_text().splitlines() if l.lstrip().startswith('theorem ')),'literal_review_keys':units,'review_status':status,'named_build':'deferred_during_checkpoint21_freeze','selected_checkpoint21':False})
peer=Path('/tmp/linalg-rkhs-bounds-two-units-independent-applied-source-review22-v1.json')
assert h(peer)=='1d76fb496a73220f33bc5a5930ea37192cdfee09dcba157c31d2f22147cc0428'
d={'schema_version':1,'status':'temporary_unselected_future22_actual_zero_proof_recovery_index','prepared_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inventory':'book/coverage/inventory-after-correction48.json','inventory_sha256':expected['book/coverage/inventory-after-correction48.json'],'held_checkpoint21_assets_exact':expected,'proofs':rows,'whole_literal_peer':{'path':str(peer),'sha256':h(peer),'approved_unit_keys':['primer-linalg.html::node-1118','primer-linalg.html::node-1120']},'counts':{'passing_temporary_files':len(rows),'new_theorems':sum(r['theorem_count'] for r in rows),'failed_trials_preserved':sum(len(r['historical_failures']) for r in rows)},'limits':['Temporary compiler runs write only /tmp records/logs/source snapshots and no olean.','No current owner ledger, helper, offer, inventory or course source was mutated.','No queued literal review is counted as a whole-source approval.','Canonical source/evidence and named builds remain deferred until root releases the freeze/audit window.']}
out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'path':str(out),'sha256':h(out),'counts':d['counts']}))
