"""Close the independently reviewed isolated Foundation26 exact three-literal offer."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path(__file__).resolve().parents[2];B=R/'book/coverage/checks/foundations-future26/source52';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());P=lambda p:Path(p)if Path(p).is_absolute()else R/p
ref=lambda p:{'file':str(Path(p).relative_to(R)),'sha256':H(p)}
def bind(r):
 p=P(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
def zero(d):
 ks=[k for k in ['actual_exit_code','exit_code']if k in d];assert ks and all(type(d[k])is int and d[k]==0 for k in ks)
def exact_copy(p):
 q=B/'original-independent-module-final-candidate-peer-v1'/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:
  with q.open('xb')as f:f.write(p.read_bytes())
 assert H(q)==H(p);return {'original_file':str(p),'original_sha256':H(p),'canonical_alias':ref(q)}
draft=B/'foundations-audit26-candidate-source52-additions-draft-v1.json';assert H(draft)=='7953624729f7b88281a45c5dec3a8855427fe6ae486f2d9e3ad6ae22d735879d';o=J(draft)
pp=Path('/tmp/foundations26-final-candidate-independent-modules-confirmation-v1.json');assert H(pp)=='ba2329be5dd2de5cccaa9898096988d3c88d8427d5d5d4a3f17db04055dc1d78';peer=J(pp);assert 'passed'in peer['status']and peer['errors']==[]and peer['draft_offer']==ref(draft)and peer['candidate']=={'file':o['mapped_ledger'],'sha256':o['mapped_ledger_sha256']}
cand=J(bind(peer['candidate']));assert peer['new_source_count']==2 and peer['new_public_exports']==15 and peer['actual_canonical_record_count']==4 and peer['baseline_proof_metadata_exact']==245
assert peer['old_exercise_bodies_exact']==119 and peer['old_proved_atoms_exact']==1104 and peer['other_entire_material_records_exact']==1753 and peer['protected_selected25_source_count']==1156 and peer['protected_current52_asset_count']==31 and peer['protected_installed25_owner_count']==5 and peer['original_semantic_bodies_and_times_unchanged']and peer['exact_entire_inverse_restores_installed25_ledger']
assert H(R/'book/coverage/foundations.json')==o['working25_ledger_sha256']==o['held25_ledger_sha256']=='9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada'
assert H(R/'book/coverage/inventory.json')==H(R/o['current_inventory'])==o['current_inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for p,h in {**o['source_sha256'],**o['additional_frozen_inputs'],**peer['closed_evidence_sha256'],**cand['proof_sha256']}.items():assert H(P(p))==h,p
for p,z in o['proof_files'].items():
 assert H(R/p)==z['sha256']
 for f,h in z['evidence_sha256'].items():assert H(R/f)==h
cp=Path('/tmp/check-foundations26-final-candidate-independent-modules-v1.py');ap=Path('/tmp/foundations26-final-candidate-independent-modules-actual-v1.json');a=J(ap);zero(a);assert H(ap)=='626cf0c654acbaf992da65bb419150708cff11cf6ffa2f5f20d1648194d1e90f'and a['actual_command']==['python3',str(cp)]and a['actual_workdir']==str(R)and a['helper_sha256_before']==a['helper_sha256_after']==H(cp)and H(P(a['raw_log']))==a['raw_log_sha256']and H(P(a['actual_runner']))==a['actual_runner_sha256']
originals=[pp,cp,ap,P(a['raw_log']),P(a['actual_runner'])];aliases=[exact_copy(p)for p in originals];lookup={r['original_file']:r['canonical_alias']for r in aliases}
aliasp=B/'independent-module-final-candidate-peer-original-byte-aliases-v1.json';assert not aliasp.exists()
with aliasp.open('x')as f:json.dump({'status':'passed_exact_five_closed_independent_original_byte_aliases','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'originals':aliases,'scope':'Exact original final mechanics peer body/time and genuine actual checker0/log/runner bytes, no semantic/compile/installation rerun.'},f,indent=2);f.write('\n')
bp=bind(peer['actual_isolated_candidate_preparation']);b=J(bp);zero(b);assert b['actual_command']==['python3',o['current_owner_builder']]and b['actual_workdir']==str(R)and H(R/o['current_owner_builder'])==o['current_owner_builder_sha256']==b['helper_sha256_before']==b['helper_sha256_after']and H(P(b['log']))==b['log_sha256']and H(P(b['actual_runner']))==b['actual_runner_sha256']
f=copy.deepcopy(o);changes={'status':'passed_reviewed_isolated_source52_foundation26_two_sources15_exports_three_complete_literals','finalized_at_utc':datetime.now(timezone.utc).isoformat(),'actual_builder_record':ref(bp)['file'],'actual_builder_record_sha256':H(bp),'actual_builder_raw_log':ref(P(b['log'])),'actual_builder_record_pending':False,'independent_final_candidate_mapping_peer_pending':False,'final_independent_candidate_mapping_peer':lookup[str(pp)],'original_final_independent_peer_body_and_time':peer,'final_independent_peer_actual_execution':lookup[str(ap)],'final_independent_peer_raw_log':lookup[a['raw_log']],'final_independent_peer_checker':lookup[str(cp)],'final_independent_peer_runner':lookup[a['actual_runner']],'final_independent_peer_exact_original_provenance':ref(aliasp),'finalizer':ref(Path(__file__)),'scope':'FINAL independently reviewed isolated source52 Foundation26: three complete197/199/209 mathematical literals, two immutable canonical paired sources/15 exports. All119 complete exercises/1104 earlier positive atoms and1753 other unit bodies/time exact. Original full semantic/canonical peers and true warnings/failures/reused-runner label clarification unchanged. No installed25 owner/HTML/inventory/selected1156/frozen25 update or aggregate26 claim.'};f.update(changes)
f['additional_frozen_inputs'].update({r['canonical_alias']['file']:r['canonical_alias']['sha256']for r in aliases})
for p in [aliasp,bp,P(b['log']),P(b['actual_runner']),Path(__file__),R/'book/coverage/checks/run_foundations26_source52_offer_finalizer_v1.py',draft]:f['additional_frozen_inputs'][ref(p)['file']]=H(p)
f['offer_finalization']={'original_draft':ref(draft),'entire_original_draft_body_and_time':o,'changed_original_fields':{k:copy.deepcopy(o[k])for k in changes if k in o},'new_field_names':[k for k in changes if k not in o],'original_additional_frozen_inputs':copy.deepcopy(o['additional_frozen_inputs']),'exact_original_semantic_decisions_and_times_retained':True,'actual_independent_read_only_peer_passed':True,'isolated_only':True}
rev=copy.deepcopy(f);meta=rev.pop('offer_finalization')
for k in meta['new_field_names']:rev.pop(k)
rev.update(meta['changed_original_fields']);rev['additional_frozen_inputs']=meta['original_additional_frozen_inputs'];assert rev==o and f['prepared_at_utc']==o['prepared_at_utc']
out=B/'foundations-audit26-candidate-source52-additions-v1-reviewed.json';assert not out.exists()
with out.open('x')as z:json.dump(f,z,ensure_ascii=False,indent=2);z.write('\n')
print(json.dumps({'status':f['status'],'offer':ref(out),'candidate':peer['candidate'],'final_peer':f['final_independent_candidate_mapping_peer']}))
