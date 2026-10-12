"""Prepare fourteen cumulative reviewed literal patches and real parser receipts.

Only fresh contract/candidate evidence is written. This is not source application.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[3]
SELF='book/coverage/checks/root_prepare_source66_79_contract_v2.py'
APPLY='book/coverage/checks/root_apply_source66_79_v2.py'
s=importlib.util.spec_from_file_location('source66_79_reviewed_writer',ROOT/APPLY)
a=importlib.util.module_from_spec(s);s.loader.exec_module(a)

def prepare(args):
 assert Path(__file__).resolve()==ROOT/SELF
 supplies={k:{'file':getattr(args,k),'sha256':getattr(args,k+'_sha256')} for k in ['foundations','modules','cmdp_proposal','cmdp_peer']}
 for k,r in supplies.items():assert r['sha256']==a.SUPPLY_PINS[k];a.checked(r)
 baseline=a.guards();original_helpers=a.helpers();rows,evidence=a.proposal_steps(supplies)
 directory=ROOT/a.CONTRACT_DIR;assert not directory.exists();directory.mkdir(parents=True)
 candidates={};previous=a.b.read(a.path(a.INVENTORY));steps=[]
 for row in rows:
  num=row['correction_id'];source=row['source'];before=candidates.get(source,a.path(source).read_bytes())
  new=a.forward_inverse(before,row['replacements']);candidate=directory/f'candidate-after-correction{num}.html';a.b.write_new(candidate,new);candidates[source]=new
  data,following,native,raw=a.fresh_parse(candidates,directory,num)
  step={k:row[k] for k in ['correction_id','label','source','proposal','peer','replacements','changed','individual_review_baseline_source65_sha256']}
  step.update({'source_sha256_before':hashlib.sha256(before).hexdigest(),'candidate':a.ref(str(candidate)),'individual_source65_proposed_page':row['individually_proposed'],'cumulative_candidate_is_distinct_identity_explicit':True})
  sd={'source':source,'candidate':step['candidate'],'counts':previous['counts'],'exact_changed_text_keys':row['changed']}
  a.b.inventory_diff(previous,following,sd);assert following['counts']['exercises']==556 and following['counts']['material_source_units']==12774
  ip=directory/f'inventory-after-correction{num}-candidate.json';a.b.write_new(ip,data)
  step.update({'inventory_after':a.ref(str(ip)),'actual_parser':native,'actual_parser_raw_log':raw});steps.append(step);evidence.extend([native,raw]);previous=following
 assert a.guards()==baseline and a.helpers()==original_helpers
 # Direct history input set has no recursively nested snapshots/package trees.
 evidence.extend([a.ref('book/coverage/checks/root_prepare_source66_79_contract_v1.py'),a.ref('book/coverage/checks/root_apply_source66_79_v1.py'),a.ref(SELF),a.ref(APPLY),a.ref(a.BASE),a.ref(a.PARSER),a.ref(a.VALIDATOR),*baseline['delivery_evidence']])
 normalized=[];seen={}
 for r in evidence:
  rr=a.ref(str(a.checked(r)))
  assert rr['file'] not in seen or seen[rr['file']]==rr['sha256'];seen[rr['file']]=rr['sha256']
  if rr not in normalized:normalized.append(rr)
 contract={'status':'prepared_exact_fourteen_step_source66_to79_contract_only','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_helpers_sha256':a.helpers(),'baseline':baseline,'input_supplies':supplies,'steps':steps,'final_source_sha256':previous['source_sha256'],'bounded_original_evidence':normalized,'all14_actual_fresh_parser_subprocesses_completed_before_any_live_write':True,'all_counts556_and12774_and_other29_literal_records_preserved':True,'source_application_or_owner_canonical_mutation':False,'coverage_complete':False}
 a.b.write_new(ROOT/a.CONTRACT,a.b.encoded(contract));print(json.dumps({'contract':a.ref(a.CONTRACT),'steps':[s['correction_id'] for s in steps],'actual_fresh_parser_count':14,'coverage_complete':False}))

if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--foundations-supply',dest='foundations',required=True);p.add_argument('--foundations-supply-sha256',dest='foundations_sha256',required=True)
 p.add_argument('--modules-supply',dest='modules',required=True);p.add_argument('--modules-supply-sha256',dest='modules_sha256',required=True)
 p.add_argument('--cmdp-proposal',dest='cmdp_proposal',required=True);p.add_argument('--cmdp-proposal-sha256',dest='cmdp_proposal_sha256',required=True)
 p.add_argument('--cmdp-peer',dest='cmdp_peer',required=True);p.add_argument('--cmdp-peer-sha256',dest='cmdp_peer_sha256',required=True)
 prepare(p.parse_args())
