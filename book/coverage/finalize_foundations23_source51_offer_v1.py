"""Bind the actual narrow independent identity peer without changing candidate bytes."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
ROOT=Path(__file__).resolve().parents[2];BASE=ROOT/'book/coverage/checks/foundations-future23/source51';TMP=Path('/tmp')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
offerpath=BASE/'foundations-audit23-candidate-source51-additions-v1.json';assert sha(offerpath)=='ff9e6e06f1774ae31234022a9e1c126b891e33c50cf8d453d1e2c8a2bb5ab020';offer=read(offerpath)
peerpath=TMP/'foundations23-source51-identity-independent-modules-confirmation-v1.json';assert sha(peerpath)=='d00323fb43ce96d92d3b6ff42300ec6b093a8456aa8a7f0de1b3643df8597abc';peer=read(peerpath)
assert 'passed' in peer['status'] and peer['errors']==[] and peer['candidate_offer']==ref(offerpath) and peer['candidate_ledger']=={'file':offer['mapped_ledger'],'sha256':offer['mapped_ledger_sha256']}
assert sha(ROOT/'book/coverage/inventory.json')==offer['current_inventory_sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
names=[peerpath.name,'modules-owner51-identity-independent-mechanics-v1.py','foundations23-source51-identity-independent-modules-actual-v1.json','foundations23-source51-identity-independent-modules-actual-v1.log'];aliases=[]
for name in names:
 src=TMP/name;dst=BASE/'original-module-source51-identity-peer'/name;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==src.read_bytes()
 else:
  with dst.open('xb') as f:f.write(src.read_bytes())
 aliases.append({'original_file':str(src),'original_sha256':sha(src),'canonical_alias':ref(dst),'exact_original_bytes':True})
actual=read(TMP/names[2]);assert actual['actual_exit_code']==0 and actual['actual_command']==['python3',str(TMP/names[1]),'foundations'] and actual['actual_workdir']==str(ROOT)
assert actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']==sha(TMP/names[1]) and sha(TMP/names[3])==actual['log_sha256']
manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');assert len(manifest['proof_files'])==1113
for n,row in manifest['proof_files'].items():assert sha(ROOT/n)==row['sha256']
for owner,h in peer['held22_live_owner_ledgers_sha256'].items():assert sha(ROOT/f'book/coverage/{owner}.json')==h
for n,row in offer['proof_files'].items():
 assert sha(ROOT/n)==row['sha256']
 for p,h in row['evidence_sha256'].items():assert sha(ROOT/p)==h
assert sha(ROOT/offer['mapped_ledger'])==offer['mapped_ledger_sha256'] and sha(ROOT/offer['material23_exact_interface_binding'])==offer['material23_exact_interface_binding_sha256']
out=BASE/'foundations-audit23-candidate-source51-additions-v2-reviewed.json';assert not out.exists();final=copy.deepcopy(offer)
final.update({'status':'passed_reviewed_isolated_source51_candidate_three_sources39_exports14_complete_literals','finalized_at_utc':datetime.now(timezone.utc).isoformat(),'original_source51_offer':ref(offerpath),'original_source50_final_candidate_mapping_peer':offer['final_independent_candidate_mapping_peer'],'final_independent_candidate_mapping_peer':ref(BASE/'original-module-source51-identity-peer'/peerpath.name),'independent_source51_identity_delta_peer_pending':False,'original_source51_independent_peer_body_and_time':peer,'final_independent_peer_exact_original_provenance':aliases,'finalizer':ref(Path(__file__)),'scope':'FINAL independently reviewed isolated Foundation23 source51 candidate only. Exactly3 new actual paired sources/39 public exports/14 complete mathematical units; every original review body/time and current22 ledger remains held. Genuine identity builder and original source50 candidate builder are distinct from any future live installation; no aggregate23/publication is inferred.'})
with out.open('x') as f:f.write(json.dumps(final,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':final['status'],'offer':ref(out),'candidate':{'file':final['mapped_ledger'],'sha256':final['mapped_ledger_sha256']},'final_peer':final['final_independent_candidate_mapping_peer']}))
