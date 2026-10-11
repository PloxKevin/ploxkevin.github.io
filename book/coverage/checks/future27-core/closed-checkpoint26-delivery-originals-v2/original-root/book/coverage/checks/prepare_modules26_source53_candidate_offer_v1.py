"""NEW Source53 offer: reversible identity fields and closed canonical binding only."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json
R=Path(__file__).resolve().parents[3];B='book/coverage/checks/modules-future26/source53';P=lambda n:Path(n)if Path(n).is_absolute()else R/n;H=lambda n:hashlib.sha256(P(n).read_bytes()).hexdigest();J=lambda n:json.loads(P(n).read_text());ref=lambda n:{'file':n,'sha256':H(n)}
parser=argparse.ArgumentParser();parser.add_argument('canonical_binding_peer');parser.add_argument('canonical_binding_peer_sha256');args=parser.parse_args();PEER=args.canonical_binding_peer;PS=args.canonical_binding_peer_sha256
OLD='book/coverage/checks/modules-future26/source52/modules-audit26-candidate-source52-additions-draft-v1.json';C=B+'/modules26-combined-candidate-source53-v1.json';I=B+'/modules26-source52-to53-owner-identity-binding-v1.json';ACT=B+'/modules26-source53-identity-builder-actual-v1.json';OUT=B+'/modules-audit26-candidate-source53-additions-draft-v1.json';INV='book/coverage/inventory-after-correction53.json';IS='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
def zero(d):
 cs=[d[k]for k in['actual_exit_code','exit_code']if k in d];assert cs and all(type(x)is int and x==0 for x in cs)
def alias(n,aliases,closed):
 if not Path(n).is_absolute():closed[n]=H(n);return ref(n)
 p=P(n);assert p.is_file()and not p.is_symlink();q=B+'/original-canonical-smoothing-binding-peer-v1/'+p.name;P(q).parent.mkdir(parents=True,exist_ok=True)
 if P(q).exists():assert H(q)==H(n)
 else:P(q).write_bytes(p.read_bytes())
 assert H(q)==H(n);aliases[n]=ref(q);closed[q]=H(q);return ref(q)
assert H(OLD)=='97570458140f20b339d550022c33d2e5e0c85e995e72725c1da23bf4a2ec634c'and H(C)=='c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231'and H(I)=='208fe8ca0b3f2d9fad5279e1237d492ce38eb580213086270472308cf462c178';assert H(INV)==H('book/coverage/inventory.json')==IS and H(PEER)==PS
old=J(OLD);c=J(C);identity=J(I);act=J(ACT);zero(act);assert H(act['helper'])==act['helper_sha256_before']==act['helper_sha256_after']and H(act['raw_log'])==act['raw_log_sha256'];peer=J(PEER);assert 'passed'in peer['status']and peer['errors']==[]
# The independent peer binds source/pair bytes, not a new semantic decision. Its
# entire native body/time is retained, including reader-failure history.
closed={**old['required_evidence_artifacts_sha256'],OLD:H(OLD),C:H(C),I:H(I),ACT:H(ACT),act['helper']:H(act['helper']),act['raw_log']:H(act['raw_log'])};aliases={}
peerref=alias(PEER,aliases,closed)
def collect(v):
 if isinstance(v,dict):
  for k,w in v.items():collect(k);collect(w)
 elif isinstance(v,list):
  for w in v:collect(w)
 elif isinstance(v,str)and v.startswith('/tmp/')and '\n'not in v and len(v)<240 and '\x00'not in v:
  p=Path(v)
  if p.is_file()and p.suffix in{'.py','.json','.log','.lean','.txt'}:alias(v,aliases,closed)
collect(peer)
for n in ['book/coverage/checks/prepare_modules26_combined_candidate_offer_source52_v1.py','book/coverage/checks/prepare_modules26_combined_candidate_offer_source52_v2.py','book/coverage/checks/modules-future26/source52/modules26-combined-offer-preparation-actual-v1.json','book/coverage/checks/modules-future26/source52/modules26-combined-offer-preparation-actual-v1.log','book/coverage/checks/modules-future26/source52/modules26-combined-offer-preparation-actual-v2.json','book/coverage/checks/modules-future26/source52/modules26-combined-offer-preparation-actual-v2.log']:
 closed[n]=H(n)
root=['reports/full-coverage/source53-correction-application-execution-v1.json','reports/full-coverage/source53-correction-application-execution-v1.log','reports/full-coverage/source53-correction-application-v1.json','book/coverage/checks/root_apply_source53_v2.py'];root_aliases={}
for n in root:
 target=B+'/source53-root-original-byte-aliases/'+H(n)+P(n).suffix;P(target).parent.mkdir(parents=True,exist_ok=True)
 if P(target).exists():assert H(target)==H(n)
 else:P(target).write_bytes(P(n).read_bytes())
 assert H(target)==H(n);closed[target]=H(target);root_aliases[n]=ref(target)
changed_fields={k:copy.deepcopy(old[k])for k in['current_inventory','current_inventory_sha256','module_ledger','module_ledger_sha256','mapped_ledger','mapped_ledger_sha256','module_builder','module_builder_sha256','actual_builder','actual_builder_raw_log','actual_isolated_candidate_preparation','smoothing_canonical_original_body_binding_peer_pending','required_evidence_artifacts_sha256','additional_frozen_inputs']}
out=copy.deepcopy(old);out.update(current_inventory=INV,current_inventory_sha256=IS,module_ledger=C,module_ledger_sha256=H(C),mapped_ledger=C,mapped_ledger_sha256=H(C),module_builder=act['helper'],module_builder_sha256=H(act['helper']),actual_builder=ref(ACT),actual_builder_raw_log=ref(act['raw_log']),actual_isolated_candidate_preparation=ref(ACT),smoothing_canonical_original_body_binding_peer_pending=False,required_evidence_artifacts_sha256=closed,additional_frozen_inputs=copy.deepcopy(closed))
out['source53_unchanged_literal_identity_offer_binding']={'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_source52_offer':ref(OLD),'original_active_fields_for_exact_inverse':changed_fields,'identity_binding':ref(I),'entire_owned_exercises_unchanged':217,'entire_owned_material_source_units_unchanged':4977,'original_isolated_mathematical_candidate_preparation':old['actual_isolated_candidate_preparation'],'actual_copy_only_identity_preparation':ref(ACT),'actual_source53_root_original_byte_aliases':root_aliases,'scope':'Current53 metadata-only binding; original52 mathematics, semantic review bodies/time, proof rows and actual canonical compiler records remain exact. No live installation or fresh mathematical compilation inferred.'}
out['canonical_original_full_smoothing44_review_body_binding_peer']=peerref;out['entire_original_canonical_smoothing_binding_body_and_time']=peer;out['canonical_smoothing_binding_original_byte_aliases']=aliases
rest=copy.deepcopy(out)
for k in['source53_unchanged_literal_identity_offer_binding','canonical_original_full_smoothing44_review_body_binding_peer','entire_original_canonical_smoothing_binding_body_and_time','canonical_smoothing_binding_original_byte_aliases']:del rest[k]
rest.update(changed_fields);assert rest==old
for n,h in closed.items():assert H(n)==h,n
for n,h in c['source_sha256'].items():assert H(n)==h
assert not P(OUT).exists();P(OUT).write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'draft_offer':ref(OUT),'candidate':ref(C),'canonical_binding_peer':peerref,'required_closed_artifacts':len(closed)}))
