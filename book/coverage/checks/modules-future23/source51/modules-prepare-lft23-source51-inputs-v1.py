from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased'); B=R/'book/coverage/checks/modules-future23/source51/lft'; A=B/'original-artifacts';B.mkdir(parents=True,exist_ok=True);A.mkdir(exist_ok=True)
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
aliases={}
def archive(p):
 p=Path(p);assert p.is_file() and not p.is_symlink(),p
 if str(p) in aliases:return aliases[str(p)]
 d=H(p);q=A/(d+p.suffix)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 row={'path':q.relative_to(R).as_posix(),'sha256':d,'original_path':str(p)};aliases[str(p)]=row;return row
def put(p,x):
 assert not p.exists(),p;p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
peerpath=Path('/tmp/modules-nn-two-layer-lft23-full-source-independent-foundations-review-v1.json');assert H(peerpath)=='54e1f8c16c4228601bc1e2afd711ddb69abbcbbc51ea66bdd891ff1060a2b10c';peer=J(peerpath)
assert peer['whole_exercise_approved'] and peer['remaining_gaps']==[] and peer['errors']==[] and len(peer['material_units'])==6
invpath=R/'book/coverage/inventory-after-correction51.json';inv=J(invpath);assert H(invpath)==H(R/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
es={x['key']:x for x in inv['exercises']};us={x['key']:x for x in inv['material_source_units']}
assert peer['entire_original_exercise_record']==es['nn-in-the-loop.html::exercise-15']
assert all(u['entire_inventory_record']==us[u['source_unit_key']] and u['whole_unit_approved'] and u['missing_clauses']==[] for u in peer['material_units'])
selected=J(R/'reports/full-coverage/checkpoint-22-manifest.json');assert len(selected['proof_files'])==1113
protected={n:r['sha256'] for n,r in selected['proof_files'].items()}
protected.update({n:H(R/n) for n in ['book/coverage/inventory.json','book/coverage/core.json','book/coverage/applied.json','book/coverage/foundations.json','book/coverage/modules.json','SafeLearning/nn-in-the-loop.html']})
for n,d in protected.items():assert H(R/n)==d,n
review=archive(peerpath);review['original_review_time']=peer['reviewed_at_utc'];review['reviewer']=peer['reviewer']
proofs=[]
specs=[('CompleteModulesNNTwoLayerLFT23',13,['/tmp/modules-nn-two-layer-lft23-canonical-standalone-actual1.json','/tmp/modules-nn-two-layer-lft23-canonical-named-actual1.json']),('CompleteModulesNNTwoLayerLFTConsequences23',3,['/tmp/modules-nn-two-layer-lft-consequences23-canonical.json','/tmp/modules-nn-two-layer-lft-consequences23-canonical-named-actual1.json'])]
for module,count,records in specs:
 source=R/'verification/lean/SafeLearning'/(module+'.lean');names=[r['name'] for r in declarations(source.read_text()) if r['kind'] in ('theorem','lemma')];assert len(names)==count
 pairs=[]
 for mode,p in zip(['lean_standalone','named_lean_module_build'],records):
  a=J(p);assert a['actual_exit_code']==0 and a['kind']==mode and a['source_unchanged'] is True
  assert a['source_sha256_before']==a['source_sha256_after']==H(source) and a['source']==source.relative_to(R).as_posix()
  assert H(a['log'])==a['log_sha256'] and H(a['source_snapshot'])==a['source_snapshot_sha256']==H(source)
  pairs.append({'actual_record':archive(p),'raw_log':archive(a['log']),'source_snapshot':archive(a['source_snapshot']),'actual_exit_code':0})
 proofs.append({'source':source.relative_to(R).as_posix(),'sha256':H(source),'public_declarations':names,'actual_paired_records':pairs})
for pattern in ['modules-two-layer-lft23-trial*.json','modules-two-layer-lft-consequences23-trial*.json']:
 for p in sorted(Path('/tmp').glob(pattern)):
  a=J(p);archive(p)
  for k,d in [('log','log_sha256'),('raw_log','raw_log_sha256'),('source_snapshot','source_snapshot_sha256')]:
   if k in a:assert H(a[k])==a[d];archive(a[k])
  if a.get('source','').startswith('/tmp/'):
   assert H(a['source'])==a['source_sha256_before'];archive(a['source'])
for p in ['/tmp/modules-nn-two-layer-lft23-full-source-review-request-v1.json','/tmp/review-modules-nn-two-layer-lft23-full-literals-independent-foundations-v1.py','/tmp/modules-nn-two-layer-lft23-independent-foundations-actual-execution-v1.json','/tmp/modules-nn-two-layer-lft23-independent-foundations-actual-execution-v1.log','/tmp/modules-future23-paired-current-source-actual-v2.py','/tmp/run-modules-two-layer-lft-consequences23-trial-v1.py']:
 archive(p)
original_decl_sources={d['name']:n for n in [x['source'] for x in proofs]+['verification/lean/SafeLearning/CompleteModulesNNCertificateAudit23.lean'] for d in declarations((R/n).read_text())}
assert set(peer['lean_declarations']).issubset(original_decl_sources)
for n,d in protected.items():assert H(R/n)==d,n
aliaspath=B/'lft-original-path-aliases-v1.json';put(aliaspath,{'status':'byte_exact_original_review_and_actual_history_aliases','aliases':aliases,'scope':'All original JSON bodies, review times, commands, logs and failed/passed source snapshots preserved; full external primary papers are reference-only, not embedded.'})
inp=B/'lft-source51-input-bindings-v1.json';put(inp,{'status':'actual_paired_sources_and_original_whole_lft_peer_exact_current51_ready','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':str(invpath.relative_to(R)),'inventory_sha256':H(invpath),'original_review':review,'entire_original_review_body_and_time':peer,'whole_exercise_key':'nn-in-the-loop.html::exercise-15','material_unit_keys':[u['source_unit_key'] for u in peer['material_units']],'proof_files':proofs,'canonical_path_aliases':{'file':str(aliaspath.relative_to(R)),'sha256':H(aliaspath)},'protected_selected22_and_owner_sha256':protected,'counts':{'new_whole_exercises':1,'material_units':6,'new_sources':2,'public_theorem_exports':16,'genuine_actual_paired_records':4},'scope':'Isolated new canonical input bindings only. Full original semantic peer54e1 body/time preserved, with genuine companion canonical/named0 separately added. No live ledger/selection/global or aggregate23 claim.'})
print(json.dumps({'input_bindings':str(inp.relative_to(R)),'sha256':H(inp),'aliases':len(aliases)}))
