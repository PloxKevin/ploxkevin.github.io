"""Finalize the held, independently reviewed Foundation24 candidate; never install it."""
from pathlib import Path
from datetime import datetime, timezone
import json,hashlib,copy
ROOT=Path(__file__).resolve().parents[2];BASE=ROOT/'book/coverage/checks/foundations-future24/source51'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def ref(p):return {'file':Path(p).relative_to(ROOT).as_posix(),'sha256':H(p)}
def bind(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and not p.is_symlink() and H(p)==r['sha256'];return p
op=BASE/'foundations-audit24-candidate-source51-additions-draft-v1.json'
assert H(op)=='45011704cef702a8f6fb0a237342cdc91af88d833551d659a12b7234ead6c9ac';o=read(op)
pp=BASE/'original-module-candidate-peer-v1/foundations24-six-whole-literal-candidate-independent-modules-confirmation-v1.json'
assert H(pp)=='3e574cfecada8d1abd1a4a876c3a7f6b076220b67f7d5d533a7f854b6c9b5339';peer=read(pp)
assert 'passed' in peer['status'] and peer['errors']==[]
assert bind(peer['candidate_ledger'])==ROOT/o['mapped_ledger'] and H(ROOT/o['mapped_ledger'])==o['mapped_ledger_sha256']
assert bind(peer['original_draft_offer'])==op and bind(peer['exact_interface'])==ROOT/o['material24_exact_interface_binding']
assert H(ROOT/o['material24_exact_interface_binding'])==o['material24_exact_interface_binding_sha256']
assert peer['new_public_export_count']==o['new_theorem_or_lemma_count']==37 and peer['genuine_paired_zero_record_count']==10
assert peer['new_proof_sources']==o['new_proof_sources_for_checkpoint24'] and len(peer['whole_unit_keys'])==6
assert H(ROOT/'book/coverage/inventory.json')==H(ROOT/o['current_inventory'])==o['current_inventory_sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert H(ROOT/o['working23_ledger'])==H(ROOT/o['held23_ledger'])==o['held23_ledger_sha256']==o['working23_ledger_sha256']
for n,h in o['source_sha256'].items():assert H(ROOT/n)==h
ap=BASE/'original-module-candidate-peer-v1/modules-foundation24-candidate-mechanics-actual-v1.json';a=read(ap)
cp=BASE/'original-module-candidate-peer-v1/modules-foundation24-candidate-mechanics-v1.py';lp=ap.with_suffix('.log')
assert a['actual_exit_code']==0 and a['actual_command']==['python3','/tmp/modules-foundation24-candidate-mechanics-v1.py'] and a['actual_workdir']==str(ROOT)
assert a['actual_checker_sha256_before']==a['actual_checker_sha256_after']==H(cp)==peer['checker']['sha256'] and H(lp)==a['log_sha256']
aliasp=BASE/'candidate-peer-original-byte-aliases-v1.json';assert H(aliasp)=='2d58c07783dc21d4483ac0cc8fdd49823cc37af62966d323d6faf73ea22e656e'
for row in read(aliasp)['originals']:assert H(bind(row['canonical_alias']))==H(row['original_file'])==row['original_sha256']
ba=BASE/'candidate-builder-actual-execution-source51-v1.json';builder=read(ba);helper=ROOT/o['current_owner_builder']
assert H(ba)==peer['actual_candidate_execution']['sha256'] and H(helper)==o['current_owner_builder_sha256']
assert builder['actual_exit_code']==0 and builder['actual_command']==['python',str(helper)] and builder['actual_workdir']==str(ROOT)
assert builder['actual_helper_sha256_before']==builder['actual_helper_sha256_after']==H(helper) and H(ROOT/builder['raw_log'])==builder['raw_log_sha256']
assert H(ROOT/builder['actual_runner'])==builder['actual_runner_sha256']
bindings={}
for name,want in [('foundations24-coercivity-and-printed-route-canonical-binding-independent-applied-confirmation-v1.json','eb7e3f50e45a6b60137284084b68d84e71bc3088f8e26c1388f340aa327725fd'),('foundations-three-canonical-sources-original-module-peers-binding24-v1.json','f788c6308276e91ad63f67cdfb98d7b6c7e680676429f853e84e804a3cc080bc')]:
 p=ROOT/'book/coverage/checks/foundations-future24/material-batch1/canonical-binding-originals-v1'/name
 assert H(p)==want and 'passed' in read(p)['status'] and read(p).get('errors',[])==[];bindings[p.relative_to(ROOT).as_posix()]=want
for field in ['exact_source_reviews_sha256','actual_canonical_execution_records_sha256','canonical_readiness_sha256']:
 for n,h in o[field].items():assert H(ROOT/n)==h
for n,row in o['proof_files'].items():
 assert H(ROOT/n)==row['sha256']
 for f,h in row['evidence_sha256'].items():assert H(ROOT/f)==h
sel=read(ROOT/o['base_selection']);manifest=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json')
assert H(ROOT/o['base_selection'])==o['base_selection_sha256'] and len(sel['proof_files'])==1131
for n,row in sel['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==row['sha256']
assets={n:h for n,h in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==h
for n in ['core','foundations','applied','modules','applied-promotions']:
 p='book/coverage/'+n+'.json';assert H(ROOT/p)==manifest['working_inputs_sha256'][p]
audit=read(ROOT/o['actual_passing_baseline_audit']);assert H(ROOT/o['actual_passing_baseline_audit'])==o['actual_passing_baseline_audit_sha256'] and audit['status']=='passed' and audit['proof_file_count']==1131 and audit['theorem_count']==9193
out=BASE/'foundations-audit24-candidate-source51-additions-v1-reviewed.json';assert not out.exists()
f=copy.deepcopy(o);f.update({'status':'passed_reviewed_isolated_source51_foundation24_candidate_five_sources37_exports_six_complete_literals','finalized_at_utc':datetime.now(timezone.utc).isoformat(),'original_prepared_draft':ref(op),'entire_original_draft_body_and_time':o,'actual_builder_record':ba.relative_to(ROOT).as_posix(),'actual_builder_record_sha256':H(ba),'actual_builder_raw_log':ref(ROOT/builder['raw_log']),'actual_builder_record_pending':False,'independent_final_candidate_mapping_peer_pending':False,'independent_canonical_binding_peer_pending':False,'final_independent_candidate_mapping_peer':ref(pp),'original_final_independent_peer_body_and_time':peer,'final_independent_peer_actual_execution':ref(ap),'final_independent_peer_raw_log':ref(lp),'final_independent_peer_checker':ref(cp),'final_independent_peer_exact_original_provenance':read(aliasp)['originals'],'canonical_source_peer_bindings_sha256':bindings,'canonical_source_binding_reviews_with_original_bodies_and_times':{n:read(ROOT/n)for n in bindings},'finalizer':ref(Path(__file__)),'scope':'FINAL independently reviewed isolated Foundation24 source51 candidate. Exactly6 complete mathematical units,5 new actual paired source files,37 public exports; original119 exercises/1094 proved atoms and every original semantic body/time retained. Genuine isolated candidate builder is separate from future live installation. Live23 owners/31assets/inventory/all1131selected sources exact. No checkpoint24 selection, aggregate or publication inferred.'})
with out.open('x')as file:file.write(json.dumps(f,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':f['status'],'offer':ref(out),'candidate':{'file':f['mapped_ledger'],'sha256':f['mapped_ledger_sha256']},'final_peer':f['final_independent_candidate_mapping_peer']}))
