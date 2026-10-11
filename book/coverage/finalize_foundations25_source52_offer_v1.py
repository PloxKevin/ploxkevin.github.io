"""Close only the reviewed isolated Foundation25 four-literal offer and exact history."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
ROOT=Path(__file__).resolve().parents[2];BASE=ROOT/'book/coverage/checks/foundations-future25/source52'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(p):return {'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
def bind(r):
 p=path(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
def exact_copy(p):
 p=Path(p);target=BASE/'original-independent-module-canonical-candidate-peer-v1'/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:
  with target.open('xb')as f:f.write(p.read_bytes())
 assert target.read_bytes()==p.read_bytes()
 return {'original_file':str(p),'original_sha256':H(p),'canonical_alias':ref(target)}
draft=BASE/'foundations-audit25-candidate-source52-additions-draft-v1.json';assert H(draft)=='0ec8d52d2735a1e7cda8874bf73b61aecb9e413740995c6b326551bf1b784a8a';o=J(draft)
peer_path=Path('/tmp/foundations25-canonical-and-four-unit-candidate-independent-modules-review-v1.json');assert H(peer_path)=='310a1e64b9881d7d83a46fe51879d3afb1a8002ba047c5f857ff52f47ea311b0';peer=J(peer_path)
assert 'passed'in peer['status']and peer['errors']==[]and peer['candidate_offer']==ref(draft)
assert peer['candidate']=={'file':o['mapped_ledger'],'sha256':o['mapped_ledger_sha256']}
candidate=J(bind(peer['candidate']));assert peer['new_sources']==2 and peer['new_public_exports']==31 and peer['genuine_canonical_actual_zero_records']==4
assert peer['all119_original_exercise_bodies_and1100_prior_positive_atoms_exact']and peer['all1752_other_material_record_bodies_and_times_exact']and peer['all1144_current_and_frozen_selected24_sources_exact']and peer['all40485_frozen24_input_bytes_exact']and peer['all31_current52_assets_and_five_installed24_owners_exact']
assert H(ROOT/'book/coverage/foundations.json')==o['working24_ledger_sha256']==o['held24_ledger_sha256']=='e3ff8460281d2a745c6def2d007b6465a1b5c352a1e14d90d486dec64835982b'
assert H(ROOT/'book/coverage/inventory.json')==H(ROOT/o['current_inventory'])==o['current_inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for n,h in o['source_sha256'].items():assert H(ROOT/n)==h
for n,h in o['additional_frozen_inputs'].items():assert H(ROOT/n)==h
for n,z in o['proof_files'].items():
 assert H(ROOT/n)==z['sha256']
 for f,h in z['evidence_sha256'].items():assert H(ROOT/f)==h
for n,h in candidate['proof_sha256'].items():assert H(ROOT/n)==h
checker=Path('/tmp/check-foundations25-canonical-and-candidate-independent-modules-v1.py');execution=Path('/tmp/foundations25-canonical-candidate-independent-modules-actual-v1.json');ea=J(execution)
assert ea['actual_exit_code']==0 and ea['actual_command']==['python',str(checker)]and ea['actual_workdir']==str(ROOT)
assert ea['helper_sha256_before']==ea['helper_sha256_after']==H(checker)and bind(peer['actual_read_only_checker'])==checker
assert H(path(ea['raw_log']))==ea['raw_log_sha256']and H(path(ea['actual_runner']))==ea['actual_runner_sha256']
originals=[peer_path,checker,execution,path(ea['raw_log']),path(ea['actual_runner'])];aliases=[exact_copy(p)for p in originals];lookup={z['original_file']:z['canonical_alias']for z in aliases}
alias_path=BASE/'independent-module-canonical-candidate-peer-original-byte-aliases-v1.json';assert not alias_path.exists()
with alias_path.open('x')as f:json.dump({'status':'passed_exact_five_closed_independent_original_byte_aliases','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'originals':aliases,'scope':'Entire original independent peer/body/time and genuine zero read-only checker/execution/rawlog/runner, copied unchanged. No semantic decision, compiler or installer rerun.'},f,indent=2);f.write('\n')
ba=bind(peer['actual_candidate_builder']);b=J(ba);assert b['actual_exit_code']==0 and b['actual_command']==['python3',o['current_owner_builder']]and b['actual_workdir']==str(ROOT)
assert H(ROOT/o['current_owner_builder'])==o['current_owner_builder_sha256']==b['helper_sha256_before']==b['helper_sha256_after']
assert H(path(b['log']))==b['log_sha256']and H(path(b['actual_runner']))==b['actual_runner_sha256']
f=copy.deepcopy(o);newfields={
 'status':'passed_reviewed_isolated_source52_foundation25_two_sources31_exports_four_complete_literals',
 'finalized_at_utc':datetime.now(timezone.utc).isoformat(),
 'actual_builder_record':ref(ba)['file'],'actual_builder_record_sha256':H(ba),'actual_builder_raw_log':ref(path(b['log'])),
 'actual_builder_record_pending':False,'independent_final_candidate_mapping_peer_pending':False,'independent_canonical_binding_peer_pending':False,
 'final_independent_candidate_mapping_peer':lookup[str(peer_path)],'canonical_source_peer_bindings_sha256':{lookup[str(peer_path)]['file']:H(peer_path)},
 'original_final_independent_peer_body_and_time':peer,'final_independent_peer_actual_execution':lookup[str(execution)],'final_independent_peer_raw_log':lookup[ea['raw_log']],'final_independent_peer_checker':lookup[str(checker)],'final_independent_peer_runner':lookup[ea['actual_runner']],
 'final_independent_peer_exact_original_provenance':ref(alias_path),'finalizer':ref(Path(__file__)),
 'scope':'FINAL independently reviewed isolated Foundation25 current52 four whole material literals only: all119 prior exercises/1100 positive atoms and1752 other material bodies/time exact, two immutable paired sources31 exports. Original17-grid source retains its24 namespace byte-for-byte while unselected by frozen24. Original full semantic bodies/times and actual warnings/failures retained. No live owner installation, checkpoint25 selection/aggregate audit or publication claimed.'}
f.update(newfields)
f['additional_frozen_inputs'].update({z['canonical_alias']['file']:z['canonical_alias']['sha256']for z in aliases})
for p in [alias_path,ba,path(b['log']),ROOT/b['actual_runner'],Path(__file__),ROOT/'book/coverage/checks/run_foundations25_source52_offer_finalizer_v1.py',draft]:f['additional_frozen_inputs'][ref(p)['file']]=H(p)
f['offer_finalization']={'original_draft':ref(draft),'entire_original_draft_body_and_time':o,'changed_original_fields':{k:copy.deepcopy(o[k])for k in newfields if k in o},'new_field_names':[k for k in newfields if k not in o],'original_additional_frozen_inputs':copy.deepcopy(o['additional_frozen_inputs']),'exact_original_semantic_decisions_and_times_retained':True,'actual_independent_read_only_peer_passed':True,'isolated_only':True}
rev=copy.deepcopy(f);finalization=rev.pop('offer_finalization')
for k in finalization['new_field_names']:rev.pop(k)
rev.update(finalization['changed_original_fields']);rev['additional_frozen_inputs']=finalization['original_additional_frozen_inputs'];assert rev==o
assert f['prepared_at_utc']==o['prepared_at_utc']
out=BASE/'foundations-audit25-candidate-source52-additions-v1-reviewed.json';assert not out.exists()
with out.open('x')as file:json.dump(f,file,ensure_ascii=False,indent=2);file.write('\n')
print(json.dumps({'status':f['status'],'offer':ref(out),'candidate':peer['candidate'],'final_peer':f['final_independent_candidate_mapping_peer']}))
