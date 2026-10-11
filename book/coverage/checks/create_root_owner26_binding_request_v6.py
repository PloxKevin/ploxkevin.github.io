"""Prepare a NEW explicit owner26 binding request after all four final offers exist.

Root authorized request preparation only; this helper does not run the binder,
integrator, compiler, global validator, publication or Git. Original offers and
semantic decisions/times remain exact; actual native schemas are pinned directly.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, re
ROOT=Path(__file__).resolve().parents[3]
OUT='book/coverage/checks/root-owner26-binding-preparation-inputs-v1.json'
DEST='book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json'
BINDER='book/coverage/checks/prepare_root_owner26_bindings_v4.py'
BINDER_SHA='f5b15f859cff5cb39606281c1bc7de8ed8a7e867e1b56337e4af9d3d514cfd0c'
INTEGRATOR='book/coverage/checks/root_integrate_owner26_candidates_v2.py'
INTEGRATOR_SHA='0ad44698e172d8d3b9c52794d2d5a6531c0d19c7828cdad22cd380c26a44fe5c'
BASELINE='reports/full-coverage/checkpoint-25-manifest.json'
BASELINE_SHA='0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'
INV='book/coverage/inventory-after-correction53.json';INV_SHA='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
OFFERS={
 'core':('book/coverage/checks/future26-core/composed-source53-v3/core-audit26-candidate-source53-additions-v1-reviewed.json',None),
 'foundations':('book/coverage/checks/foundations-future26/source53/foundations-audit26-candidate-source53-additions-v1-reviewed.json','5984cedeae7ea23a5faed5b555ea889ce8ebdcd5345ab6ae7e3748e7e29fbcfc'),
 'applied':('book/coverage/checks/applied-future26/source53-v2/applied-audit26-candidate-source53-additions-v1-reviewed.json','5ebc60ba97be9342b817a468eb7168b5d79f59ab565b68591e41fe6d051186d2'),
 'modules':('book/coverage/checks/modules-future26/source53/modules-audit26-candidate-source53-additions-v1-reviewed.json','84565e522eb29a76f11766e7a8e96b84bbbccab185cc9ff535dd7ce75b42f133')}
FINALIZERS={
 'foundations':'book/coverage/checks/foundations-future26/source53/foundations26-source53-identity-finalizer-actual-execution-v1.json',
 'applied':'book/coverage/checks/applied-future26/source53-v2/reviewed-offer-finalization-actual-v2.json',
 'modules':'book/coverage/checks/modules-future26/source53/modules26-source53-reviewed-offer-finalization-actual-v2.json'}
CORE_FINALIZER='book/coverage/checks/finalize_root_core26_offer_v4.py'
CORE_CANDIDATE='book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-v1.json'
CORE_CANDIDATE_SHA='1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38'
def safe(n):
 assert isinstance(n,str) and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts
 p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):
 assert isinstance(r,dict) and set(r)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256']) and sha(r['file'])==r['sha256'];return read(r['file'])
def alias(d,keys):
 values=[d[k] for k in keys if k in d];assert values and all(x==values[0] for x in values);return values[0]
def zero(d):
 values=[d[k] for k in ('actual_exit_code','exit_code') if k in d];assert values and all(type(x)is int and x==0 for x in values)
def add(out,n,h):
 assert isinstance(h,str) and re.fullmatch('[0-9a-f]{64}',h) and sha(n)==h
 assert n not in out or out[n]==h;out[n]=h
# These pointers describe the actual current native schemas; no guessed producer row is fabricated.
def owner_interface(owner,offer,semantics):
 peerkey=['current53_identity_rebase','independent_source53_identity_peer'] if owner=='foundations' else ['final_independent_candidate_mapping_peer']
 peercandidate='candidate_ledger' if owner=='foundations' else 'candidate'
 builderpath=['actual_builder_record'] if owner in ('core','foundations') else ['actual_isolated_candidate_preparation','file'] if owner=='applied' else ['actual_builder','file']
 buildersha=['actual_builder_record_sha256'] if owner in ('core','foundations') else ['actual_isolated_candidate_preparation','sha256'] if owner=='applied' else ['actual_builder','sha256']
 return {'offer_candidate_path_pointer':['mapped_ledger'],'offer_candidate_sha256_pointer':['mapped_ledger_sha256'],'offer_independent_peer_pointer':peerkey,'peer_candidate_path_pointer':[peercandidate,'file'],'peer_candidate_sha256_pointer':[peercandidate,'sha256'],'offer_actual_builder_path_pointer':builderpath,'offer_actual_builder_sha256_pointer':buildersha,'original_full_source_semantic_reviews':semantics}
def collect_finalizer(name,evidence):
 d=read(name);zero(d);command=alias(d,('actual_command','command'))
 assert isinstance(command,list) and len(command)>=2 and command[0] in ('python','python3') and command[1].startswith('book/coverage/') and command[1].endswith('.py')
 assert alias(d,('actual_workdir','cwd','working_directory'))==str(ROOT)
 if any(k in d for k in ('helper_sha256_before','actual_helper_sha256_before')):
  before=alias(d,('helper_sha256_before','actual_helper_sha256_before'));after=alias(d,('helper_sha256_after','actual_helper_sha256_after'));assert before==after
  if isinstance(before,dict):
   assert command[1] in before
   for n,h in before.items():add(evidence,n,h)
  else:add(evidence,command[1],before)
 else:add(evidence,command[1],d['helper_sha256'])
 log=alias(d,('log','raw_log'));digest=alias(d,('log_sha256','raw_log_sha256','original_log_sha256'))
 add(evidence,log,digest);add(evidence,name,sha(name))
 for key in ('actual_runner','helper'):
  if key in d:
   v=d[key]
   if isinstance(v,dict) and set(v)=={'file','sha256'}:add(evidence,v['file'],v['sha256'])
   elif isinstance(v,str) and key+'_sha256' in d:add(evidence,v,d[key+'_sha256'])
 return d
def prepare(args):
 assert args.root_authorized_binding_request_preparation and not safe(OUT).exists() and not safe(DEST).exists()
 assert sha(BINDER)==BINDER_SHA and sha(INTEGRATOR)==INTEGRATOR_SHA and sha(BASELINE)==BASELINE_SHA
 assert sha(INV)==INV_SHA==sha('book/coverage/inventory.json')
 assert sha(args.independent_peer)==args.peer_sha256 and sha(args.core_finalization_execution)==args.core_finalization_execution_sha256
 helperpeer=read(args.independent_peer)
 assert 'passed' in helperpeer['status'] and helperpeer.get('errors',[])==[] and helperpeer['helper_sha256']==INTEGRATOR_SHA
 assert helperpeer['helpers_sha256'][INTEGRATOR]==INTEGRATOR_SHA and helperpeer['helpers_sha256'][BINDER]==BINDER_SHA
 spec=importlib.util.spec_from_file_location('readonly_owner26_binder_native_schema',safe(BINDER));binder=importlib.util.module_from_spec(spec);spec.loader.exec_module(binder)
 manifest=read(BASELINE);held={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/'+o+'.json' for o in ('core','foundations','applied','modules','applied-promotions')}}
 assert len(held)==5
 for n,h in held.items():assert sha(n)==h
 assets={n:sha(n) for n in manifest['frozen_inputs_sha256'] if n.startswith('SafeLearning/')};assert len(assets)==31
 offers={};interfaces={};extras={o:{} for o in OFFERS}
 for owner,(name,pinned) in OFFERS.items():
  if pinned is not None:assert sha(name)==pinned
  offers[owner]=ref(name);offer=read(name)
  assert offer.get('coverage_complete') is False
  vals=[offer[k] for k in ('inventory_sha256','current_inventory_sha256') if k in offer];assert vals and all(h==INV_SHA for h in vals)
  if owner=='core':
   assert offer['mapped_ledger']==CORE_CANDIDATE and offer['mapped_ledger_sha256']==CORE_CANDIDATE_SHA
   binding=offer['exact_candidate_binding'];mpc=binder.checked(binding['new_proof_sources'][0]['readiness']);label=binder.checked(binding['fixed_48_nonformal_label_candidate'])
   semantics=[label['future26_label_material_candidate_binding']['original_full118_label_peer'],mpc['original_full_source_peer'],binding['whole_source_review']]
  elif owner=='foundations':semantics=[{'file':n,'sha256':h} for n,h in sorted(offer['exact_source_reviews_sha256'].items())]
  elif owner=='applied':semantics=offer['original_independent_review_references']
  else:
   semantics=offer['original_full_or_precise_source_reviews']
   # This exact physical-unit interface supplement preserves the original
   # mathematical decision/time. Its preparation time is not a new review.
   supplement={'file':'book/coverage/checks/modules-future26/landscape/original-tmp/landscape15-three-physical-units-independent-foundations-final-scope-supplement26-v1.json','sha256':'0e5cc3e4e44884cba6116a42152217dcee7e161bb2c1237b9058fdb53a22367f'}
   assert semantics.count(supplement)==1
   original_supplement=checked(supplement)
   assert original_supplement['prepared_at_utc']=='2026-10-11T05:47:50.679605+00:00'
   assert 'reviewed_at_utc' not in original_supplement and 'checked_at_utc' not in original_supplement
   add(extras[owner],supplement['file'],supplement['sha256'])
   semantics=[r for r in semantics if r!=supplement]
  for sr in semantics:
   body=checked(sr);assert body.get('errors',[])==[] and body.get('reviewed_at_utc',body.get('checked_at_utc')) is not None
  schema=owner_interface(owner,offer,semantics);interfaces[owner]=schema
  candidate={'file':binder.pointer(offer,schema['offer_candidate_path_pointer']),'sha256':binder.pointer(offer,schema['offer_candidate_sha256_pointer'])};checked(candidate)
  peerref=binder.pointer(offer,schema['offer_independent_peer_pointer']);peer=checked(peerref)
  assert 'passed' in peer['status'] and peer.get('errors',[])==[] and binder.pointer(peer,schema['peer_candidate_path_pointer'])==candidate['file'] and binder.pointer(peer,schema['peer_candidate_sha256_pointer'])==candidate['sha256']
  builderref={'file':binder.pointer(offer,schema['offer_actual_builder_path_pointer']),'sha256':binder.pointer(offer,schema['offer_actual_builder_sha256_pointer'])};builder=binder.checked(builderref);log,digest=binder.actual_builder_evidence(builder)
  add(extras[owner],builderref['file'],builderref['sha256']);add(extras[owner],log,digest)
  for field in ('required_evidence_artifacts_sha256','required_live_integration_evidence_sha256','canonical_readiness_sha256','canonical_source_peer_bindings_sha256','actual_canonical_execution_records_sha256','additional_frozen_inputs'):
   for n,h in binder.native_offer_evidence_map(owner,field,offer).items():add(extras[owner],n,h)
  add(extras[owner],peerref['file'],peerref['sha256'])
  # Original absolute references survive inside reviews; only explicitly verified canonical closure is eligible here.
  for n,h in peer.get('closed_evidence_sha256',{}).items():
   if not Path(n).is_absolute():add(extras[owner],n,h)
  for field in ('original_closed_byte_aliases','original_closed_byte_aliases_sha256'):
   aliases=peer.get(field,{})
   if isinstance(aliases,dict):
    for aliasrow in aliases.values():
     if isinstance(aliasrow,dict) and set(aliasrow)=={'file','sha256'}:add(extras[owner],aliasrow['file'],aliasrow['sha256'])
  if owner!='core':collect_finalizer(FINALIZERS[owner],extras[owner])
 coreactual=collect_finalizer(args.core_finalization_execution,extras['core'])
 assert alias(coreactual,('actual_command','command'))[1]==CORE_FINALIZER
 # Six exact closed original Core candidate checker records, including its unchanged report/time.
 corepeerfolder=ROOT/'book/coverage/checks/future26-core/composed-source53-v3/original-independent-candidate-peer'
 coreoriginals=list(corepeerfolder.iterdir());assert len(coreoriginals)==6 and all(p.is_file() and not p.is_symlink() for p in coreoriginals)
 for p in coreoriginals:add(extras['core'],p.relative_to(ROOT).as_posix(),hashlib.sha256(p.read_bytes()).hexdigest())
 for n in ['reports/full-coverage/prepare-owner26-binding-request-execution-v1.json','reports/full-coverage/prepare-owner26-binding-request-execution-v1.log','book/coverage/checks/create_root_owner26_binding_request_v3.py','book/coverage/checks/prepare_root_owner26_bindings_v2.py','book/coverage/checks/prepare_root_owner26_bindings_v3.py','book/coverage/checks/create_root_owner26_binding_request_v4.py','book/coverage/checks/create_root_owner26_binding_request_v5.py','reports/full-coverage/root-core26-composed-candidate-execution-v1.json','reports/full-coverage/root-core26-composed-candidate-execution-v1.log','reports/full-coverage/root-core26-composed-candidate-execution-v2.json','reports/full-coverage/root-core26-composed-candidate-execution-v2.log']:
  add(extras['core'],n,sha(n))
 for n,h in helperpeer['closed_evidence_sha256'].items():
  assert not Path(n).is_absolute();add(extras['core'],n,h)
 for n in [args.independent_peer,BINDER,INTEGRATOR,str(Path(__file__).relative_to(ROOT)),BASELINE,INV,'reports/full-coverage/source53-correction-application-v1.json','reports/full-coverage/source53-correction-application-execution-v1.json','reports/full-coverage/source53-correction-application-execution-v1.log']:
  add(extras['core'],n,sha(n))
 config={'status':'root_requested_exact_four_owner26_binding_preparation_inputs','root_requested_at_utc':datetime.now(timezone.utc).isoformat(),'preparation_helper':ref(BINDER),'independent_integration_helper_review':ref(args.independent_peer),'destination':DEST,'offers':offers,'owner_interfaces':interfaces,'extra_closed_evidence':{o:[{'file':n,'sha256':h} for n,h in sorted(values.items())] for o,values in extras.items()},'baseline25_manifest':ref(BASELINE),'immutable_current53_inventory':ref(INV),'exact_current53_assets_sha256':assets,'root_request_preparation_helper':ref(str(Path(__file__).relative_to(ROOT))),'actual_final_core_offer_execution':ref(args.core_finalization_execution),'coverage_complete':False,'scope':'New request only, with actual explicit native schema pointers and original full source decisions/times. No binding production, integration, fresh Lean/compiler/audit or publication is executed.'}
 # Read-only binder-native validation confirms all11 sources134 and22 actual pair records before request is written.
 # The function takes in-memory config directly and uses input_name only for
 # a returned fingerprint. Supply this existing preparation source while the
 # destination is deliberately absent. Discard that observation; do not
 # publish it as a production binding or as evidence of an actual request.
 observation=binder.build_binding(config,str(Path(__file__).relative_to(ROOT)))
 assert observation['new_proof_sources']==11 and observation['new_public_exports']==134 and observation['original_canonical_execution_records']==22
 for n,h in held.items():assert sha(n)==h
 for n,h in assets.items():assert sha(n)==h
 assert sha(INV)==INV_SHA==sha('book/coverage/inventory.json')
 with safe(OUT).open('x') as f:f.write(json.dumps(config,indent=2,ensure_ascii=False)+'\n')
 return ref(OUT)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--independent-peer',required=True);parser.add_argument('--peer-sha256',required=True);parser.add_argument('--core-finalization-execution',required=True);parser.add_argument('--core-finalization-execution-sha256',required=True);parser.add_argument('--root-authorized-binding-request-preparation',action='store_true',required=True);args=parser.parse_args()
 print(json.dumps({'status':'passed_exact_explicit_owner26_binding_request_preparation','input':prepare(args),'owners':4,'new_sources':11,'new_public_exports':134,'canonical_execution_records':22,'live_owner_written':False}))
if __name__=='__main__':main()
