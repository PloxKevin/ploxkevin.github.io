from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,re,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
BASE='book/coverage/checks/foundations-future25/source52'
DRAFT=BASE+'/foundations-audit25-candidate-source52-additions-draft-v1.json'
READY='book/coverage/checks/foundations-future25/material-batch1/two-source31-export-actual-canonical-readiness25-v1.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda n:json.loads((ROOT/n).read_text())
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
def readref(r):
 p=ROOT/r['file'];assert H(p)==r['sha256'],r['file'];return json.loads(p.read_text())
def physical(d):
 by={}
 for c in d['material_claims']:
  for k in c['source_unit_keys']:by.setdefault(k,set()).add(c['status'])
 counts=Counter('pending' if 'pending' in s else 'not_a_formal_claim' if s=={'not_a_formal_claim'} else 'proved' for s in by.values())
 return {'total':len(by),'whole_proved':counts['proved'],'nonformal':counts['not_a_formal_claim'],'whole_pending':counts['pending']}
assert H(ROOT/DRAFT)=='0ec8d52d2735a1e7cda8874bf73b61aecb9e413740995c6b326551bf1b784a8a'
assert H(ROOT/READY)=='fb000de1d12fa918106cc181ca07cad500bfbc2d1e167a3b0533fafdae8f4375'
d=J(DRAFT);c=J(d['mapped_ledger']);old=J(d['held24_ledger']);i=J(d['material25_exact_interface_binding']);ready=J(READY)
assert H(ROOT/d['mapped_ledger'])==d['mapped_ledger_sha256']=='9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada'
assert H(ROOT/d['held24_ledger'])==H(ROOT/'book/coverage/foundations.json')==d['held24_ledger_sha256']=='e3ff8460281d2a745c6def2d007b6465a1b5c352a1e14d90d486dec64835982b'
assert H(ROOT/d['material25_exact_interface_binding'])==d['material25_exact_interface_binding_sha256']
assert i['candidate_ledger']==ref(d['mapped_ledger']) and i['held_original24_ledger']==ref(d['held24_ledger'])
inv=J(d['current_inventory']); assert H(ROOT/d['current_inventory'])==H(ROOT/'book/coverage/inventory.json')==d['current_inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
u={r['key']:r for r in inv['material_source_units']};e={r['key']:r for r in inv['exercises']};v48=J('book/coverage/inventory-after-correction48.json');u48={r['key']:r for r in v48['material_source_units']};e48={r['key']:r for r in v48['exercises']}
owned={k:r for k,r in u.items() if r['source'] in old['scope_pages']};ownede={k:r for k,r in e.items() if r['source'] in old['scope_pages']}
assert len(owned)==1756 and len(ownede)==119 and all(r==u48[k] for k,r in owned.items()) and all(r==e48[k] for k,r in ownede.items())
assert c['exercises']==old['exercises'] and c['surrounding_prose_reviews']==old['surrounding_prose_reviews']
manifest=J('reports/full-coverage/checkpoint-24-manifest.json');selection=J('reports/full-coverage/checkpoint-24-selection.json');audit=J('reports/full-coverage/lean-checkpoint-24/verification-original.json')
assert audit['status']=='passed' and audit['proof_file_count']==1144 and audit['theorem_count']==9279 and H(ROOT/d['actual_passing_baseline_audit'])==d['actual_passing_baseline_audit_sha256']
assert H(ROOT/d['base_selection'])==d['base_selection_sha256']==manifest['selection_sha256']
for n,row in selection['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-24'/n)==row['sha256']
for n,h in manifest['frozen_inputs_sha256'].items():assert H(ROOT/'reports/full-coverage/checkpoint-24'/n)==h,n
assert len(manifest['frozen_inputs_sha256'])==40485
for n,h in manifest['working_inputs_sha256'].items():
 if n.startswith('SafeLearning/') or n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']:
  assert H(ROOT/n)==h,n
for n,h in d['source_sha256'].items():assert H(ROOT/n)==h
for n,h in d['additional_frozen_inputs'].items():assert H(ROOT/n)==h,n
packets=[];mapped={};public=[];newfiles={};allaliases={};referenced=set()
for gref in ready['groups']:
 g=readref(gref);p=readref(g['original_preparation']);orig=readref(g['original_full_semantic_peer']);req=readref(g['original_TMP_request'])
 assert orig==g['entire_original_full_semantic_peer_body_and_time'] and p==g['entire_original_preparation_body_and_time'] and req==g['entire_original_TMP_request_body_and_time']
 assert orig['errors']==[] and 'passed' in orig['status']
 src=ROOT/g['canonical_source']['file'];assert H(src)==g['canonical_source']['sha256'];snapshot=ROOT/g['canonical_source_snapshot']['file'];assert src.read_bytes()==snapshot.read_bytes()
 tmp=ROOT/p['original_TMP_source']['file'];assert src.read_bytes()==tmp.read_bytes() and H(src)==p['original_TMP_source']['sha256']
 names=[x['name'] for x in declarations(src.read_text()) if x['kind'] in ('theorem','lemma')];assert names==g['public_theorem_names'] and len(names)==g['public_theorem_count'];public+=names
 assert str(src.relative_to(ROOT)) not in selection['proof_files'] and str(src.relative_to(ROOT)) not in old['proof_files']
 newfiles[str(src.relative_to(ROOT))]=H(src)
 for original,r in g['all_original_TMP_byte_aliases'].items():
  cp=ROOT/r['file'];assert H(cp)==r['sha256'] and cp.read_bytes()==Path(original).read_bytes();allaliases[original]=r
 actuals=[]
 for pair in g['actual_canonical_pair']:
  a=readref(pair['actual_record']);log=ROOT/pair['raw_log']['file'];ss=ROOT/pair['source_snapshot']['file']
  assert H(log)==pair['raw_log']['sha256'] and H(ss)==pair['source_snapshot']['sha256']==H(src) and ss.read_bytes()==src.read_bytes()
  exitfields=[a[k] for k in ['actual_exit_code','exit_code'] if k in a];assert exitfields and all(type(x)is int and x==0 for x in exitfields)
  assert a['actual_workdir']==str(ROOT/'verification/lean') and a['source']==str(src.relative_to(ROOT))
  assert a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==H(src)
  assert a['log']==str(log.relative_to(ROOT)) and a['log_sha256']==H(log)
  assert a['source_snapshot']==str(ss.relative_to(ROOT)) and a['started_at_utc']<a['finished_at_utc'] and a['elapsed_seconds']>0
  assert a['actual_command'] in [['lake','build','SafeLearning.'+src.stem],['lake','env','lean','SafeLearning/'+src.name]]
  assert H(ROOT/a['actual_pair_helper'])==a['actual_pair_helper_sha256'] and ref(a['actual_pair_helper'])==g['actual_helper'];actuals.append(a['actual_command'][1])
  assert d['proof_files'][str(src.relative_to(ROOT))]['evidence_sha256'][pair['actual_record']['file']]==pair['actual_record']['sha256']
  assert d['proof_files'][str(src.relative_to(ROOT))]['evidence_sha256'][pair['raw_log']['file']]==pair['raw_log']['sha256']
  assert d['proof_files'][str(src.relative_to(ROOT))]['evidence_sha256'][pair['source_snapshot']['file']]==pair['source_snapshot']['sha256']
 assert sorted(actuals)==['build','env']
 packet=next(x for x in i['proof_packets'] if x['group']==g['group']);assert packet['entire_original_semantic_body_and_time']==orig and packet['canonical_source']==g['canonical_source'] and packet['public_theorem_names']==names
 for row in orig['material_units']:
  k=row['key'];assert row['inventory_record']==u[k] and row['whole_material_unit_approved'] and row['missing']==[]
  assert k not in mapped; m=next(m for m in i['material_units'] if m['source_unit_key']==k)
  assert m['entire_original_whole_literal_peer_row']==row and m['entire_current52_inventory_record']==u[k]
  original=[x for x in old['material_claims'] if k in x['source_unit_keys']];pending=[x for x in original if x['status']=='pending'];assert len(pending)==1
  assert m['entire_original_pending_clauses']==pending and m['retained_original_nonpending_clauses']==[x for x in original if x['status']!='pending']
  new=m['new_candidate_claim'];assert new in c['material_claims'] and new['status']=='proved' and new['lean_declarations']==row['decls'] and new['hypotheses']==row['hypotheses'] and new['correspondence']==row['reason'] and new['remaining_gaps']==[]
  assert new['source_unit_keys']==[k] and new['source_text']==new['statement_in_prose']==u[k]['source_text'] and new['source_text_sha256']==u[k]['text_sha256'] and new['source_sha256']==u[k]['source_sha256']
  assert new['source_review']['reviewed_at_utc']==m['original_reviewed_at_utc']==row.get('reviewed_at_utc',orig['reviewed_at_utc']) and m['original_full_peer_reviewed_at_utc']==orig['reviewed_at_utc']
  assert new['source_review']['file']==g['original_full_semantic_peer']['file'] and new['source_review']['sha256']==g['original_full_semantic_peer']['sha256'] and new['source_review']['reviewer']==orig['reviewer']
  mapped[k]=m
 packets.append({'canonical_source':g['canonical_source'],'original_complete_semantic_peer':g['original_full_semantic_peer'],'entire_original_semantic_body_and_time':orig,'public_names':names,'actual_pair':g['actual_canonical_pair']})
assert set(mapped)=={'primer-basics.html::node-1175','primer-optimization.html::node-152','primer-optimization.html::node-154','primer-optimization.html::node-166'}
assert len(newfiles)==2 and len(public)==31 and len(set(public))==31 and i['all_original_TMP_byte_aliases']==allaliases
removed={p['id'] for m in mapped.values() for p in m['entire_original_pending_clauses']};added={m['new_candidate_claim']['id'] for m in mapped.values()}
assert [x for x in old['material_claims'] if x['id'] not in removed]==[x for x in c['material_claims'] if x['id'] not in added]
assert all(x in c['material_claims'] for x in old['material_claims'] if x['status']=='proved') and sum(x['status']=='proved' for x in old['material_claims'])==1100
assert len(c['limits'])==len(old['limits'])+1 and c['limits'][:-1]==old['limits']
assert physical(old)=={'total':1756,'whole_proved':768,'nonformal':524,'whole_pending':464} and physical(c)=={'total':1756,'whole_proved':772,'nonformal':524,'whole_pending':460}
expectedproof=set(old['proof_files'])|set(newfiles)|set(i['referenced_existing_selected24_proof_sources']);assert set(c['proof_files'])==expectedproof
for n,h in old['proof_sha256'].items():assert c['proof_sha256'][n]==h
for n,h in i['referenced_existing_selected24_proof_sources'].items():assert H(ROOT/n)==selection['proof_files'][n]['sha256']==h
assert set(c['proof_sha256'])==expectedproof and d['proof_files'].keys()==newfiles.keys()
reverse=copy.deepcopy(c)
for k in ['current25_owner_identity','current25_material_mapping']:reverse.pop(k)
for k in ['material_claims','counts','proof_files','proof_sha256','limits']:reverse[k]=copy.deepcopy(old[k])
assert reverse==old,'Unexplained candidate metadata or historical-body delta'
assert c['counts']['material_claim_statuses']==dict(Counter(x['status'] for x in c['material_claims']))
actualname=BASE+'/foundations25-isolated-candidate-builder-actual-execution-v1.json';a=J(actualname)
assert a['actual_exit_code']==0 and H(ROOT/a['log'])==a['log_sha256'] and a['helper_sha256_before']==a['helper_sha256_after']==H(ROOT/d['current_owner_builder'])==d['current_owner_builder_sha256']
assert all(H(ROOT/n)==h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json'])
report={'status':'independent_foundation25_original_canonical_body_pair_and_four_literal_candidate_mechanics_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','candidate':ref(d['mapped_ledger']),'candidate_offer':ref(DRAFT),'exact_interface':ref(d['material25_exact_interface_binding']),'canonical_readiness':ref(READY),'baseline24_ledger':ref(d['held24_ledger']),'current_inventory':ref(d['current_inventory']),'original_complete_semantic_decisions_and_times':packets,'fresh_whole_unit_keys':sorted(mapped),'all119_original_exercise_bodies_and1100_prior_positive_atoms_exact':True,'all1756_entire_foundation_records_unchanged48_to52':True,'all1752_other_material_record_bodies_and_times_exact':True,'new_sources':2,'new_public_exports':31,'genuine_canonical_actual_zero_records':4,'original_TMP_byte_aliases':len(allaliases),'physical_before':physical(old),'physical_after':physical(c),'all1144_current_and_frozen_selected24_sources_exact':True,'all40485_frozen24_input_bytes_exact':True,'all31_current52_assets_and_five_installed24_owners_exact':True,'actual_candidate_builder':ref(actualname),'actual_candidate_builder_raw_log':ref(a['log']),'scope':'Narrow byte-exact original complete source-body/semantic decision/time/canonical pair binding plus independently reconstructed isolated candidate mechanics. No new mathematics, Lean execution, live owner installation, global25 or aggregate25 claim.','actual_read_only_checker':{'file':__file__,'sha256':H(Path(__file__))}}
out=Path('/tmp/foundations25-canonical-and-four-unit-candidate-independent-modules-review-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':str(out),'sha256':H(out),'whole_units':4,'sources':2,'exports':31}))
