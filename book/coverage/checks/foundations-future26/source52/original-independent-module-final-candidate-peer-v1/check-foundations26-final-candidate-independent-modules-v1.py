from pathlib import Path
from datetime import datetime,timezone
import collections,copy,hashlib,json,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
B='book/coverage/checks/foundations-future26/source52';OUT=Path('/tmp/foundations26-final-candidate-independent-modules-confirmation-v1.json')
def P(n):return Path(n)if Path(n).is_absolute()else R/n
def H(n):return hashlib.sha256(P(n).read_bytes()).hexdigest()
def J(n):return json.loads(P(n).read_text())
def ref(n):return {'file':n,'sha256':H(n)}
def bind(r):assert H(r['file'])==r['sha256'],r['file'];return J(r['file'])
def zero(d):
 cs=[d[k]for k in ['actual_exit_code','exit_code']if k in d];assert cs and all(type(v)is int and v==0 for v in cs)
def names(n):return {x['name']for x in declarations(P(n).read_text())if x['kind']in['theorem','lemma']}
def physical(d):
 by={}
 for row in d['material_claims']:
  for k in row['source_unit_keys']:by.setdefault(k,set()).add(row['status'])
 return dict(collections.Counter('pending'if'pending'in s else'not_a_formal_claim'if s=={'not_a_formal_claim'}else'proved'for s in by.values()))
D=B+'/foundations-audit26-candidate-source52-additions-draft-v1.json';assert H(D)=='7953624729f7b88281a45c5dec3a8855427fe6ae486f2d9e3ad6ae22d735879d';d=J(D)
C=d['mapped_ledger'];I=d['material26_exact_interface_binding'];OLD=d['held25_ledger'];assert H(C)==d['mapped_ledger_sha256'] and H(I)==d['material26_exact_interface_binding_sha256'] and H(OLD)==d['held25_ledger_sha256']==H('book/coverage/foundations.json')=='9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada'
c=J(C);i=J(I);old=J(OLD);bind(i['candidate_ledger']);bind(i['held_original25_ledger']);iv=bind(i['current_inventory']);assert H(i['current_inventory']['file'])==H('book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert c['exercises']==old['exercises'] and len(c['exercises'])==119 and c['surrounding_prose_reviews']==old['surrounding_prose_reviews'] and c['source_sha256']==old['source_sha256'];assert sum(r['status']=='proved'for r in old['material_claims'])==1104
um={u['key']:u for u in iv['material_source_units']};iv48=J('book/coverage/inventory-after-correction48.json');u48={u['key']:u for u in iv48['material_source_units']};e48={e['key']:e for e in iv48['exercises']};owned={k:u for k,u in um.items()if u['source']in old['scope_pages']};assert len(owned)==1756 and all(u==u48[k]for k,u in owned.items());ex=[e for e in iv['exercises']if e['source']in old['scope_pages']];assert len(ex)==119 and all(e==e48[e['key']]for e in ex)
peer=bind(i['independent_canonical_binding_peer']);assert peer==i['entire_original_canonical_binding_peer_body_and_time'] and peer['errors']==[] and 'passed'in peer['status'];assert H(i['independent_canonical_binding_peer']['file'])=='db18f351445a96334ba52d32bf50230917f9ac2923b9dad22d757e79a7eca92f';bind(i['reused_runner_label_limitation'])
removed={};newids=set();semantics={};allnames=set();referenced={};pairs=[];keys=set();closure={D:H(D),C:H(C),I:H(I),OLD:H(OLD),**d['additional_frozen_inputs']}
for pkt in i['proof_packets']:
 src=pkt['canonical_source']['file'];assert H(src)==pkt['canonical_source']['sha256'];sem=bind(pkt['original_semantic_review']);assert sem==pkt['entire_original_semantic_body_and_time'] and sem['full_source_body_read']==P(src).read_text();assert set(pkt['public_theorem_names'])==names(src);allnames.update(names(src));semantics[pkt['original_semantic_review']['file']]=sem
 assert set(d['proof_files'][src]['evidence_sha256'])=={p[k]['file']for p in pkt['actual_pair']for k in ['record','raw_log','source_snapshot']}
 assert d['proof_files'][src]['sha256']==H(src) and src not in old['proof_files']
 kinds=[]
 for p in pkt['actual_pair']:
  a=bind(p['record']);zero(a);assert a==p['entire_original_actual_record_and_time'] and a['source']==src and a['source_sha256_before']==a['source_sha256_after']==H(src)
  assert a['command']in [['lake','env','lean','SafeLearning/'+Path(src).name],['lake','build','SafeLearning.'+Path(src).stem]];kinds.append(a['command'][1]);assert H(p['raw_log']['file'])==p['raw_log']['sha256']==a['log_sha256'] and H(p['source_snapshot']['file'])==p['source_snapshot']['sha256']==H(src);assert a['elapsed_seconds']>0 and a['started_at_utc']<a['finished_at_utc'];pairs.append(p)
 assert sorted(kinds)==['build','env']
assert len(allnames)==15 and len(pairs)==4 and len(d['proof_files'])==2
selected=J(d['base_selection']);assert H(d['base_selection'])==d['base_selection_sha256'] and len(selected['proof_files'])==1156
for m in i['material_units']:
 k=m['source_unit_key'];keys.add(k);assert m['entire_current52_inventory_record']==um[k]==u48[k]
 sem=semantics[m['original_semantic_review']['file']];row=next(r for r in sem['literal_unit_decisions']if r['key']==k);assert row==m['entire_original_whole_literal_peer_row'] and row['status']=='approved_whole_literal' and row['missing_clauses']==[]
 expected_time=row.get('reviewed_at_utc',sem['reviewed_at_utc']);assert m['original_reviewed_at_utc']==expected_time and m['original_full_peer_reviewed_at_utc']==sem['reviewed_at_utc']
 n=m['new_candidate_claim'];assert n in c['material_claims'] and n['lean_declarations']==row['lean_declarations'] and n['hypotheses']==row['hypotheses'] and n['correspondence']==row['reason'] and n['statement_in_prose']==um[k]['source_text'] and n['source_review']['reviewed_at_utc']==expected_time and n['status']=='proved'and n['remaining_gaps']==[];newids.add(n['id'])
 prior=[r for r in old['material_claims']if k in r['source_unit_keys']];pend=[r for r in prior if r['status']=='pending'];assert len(pend)==1 and pend==m['entire_original_pending_clauses'] and [r for r in prior if r['status']!='pending']==m['retained_original_nonpending_clauses'];removed[pend[0]['id']]=pend[0]
 for decl in row['lean_declarations']:
  if decl in allnames:continue
  candidates=[n for n,s in selected['proof_files'].items()if decl in names(n)]
  assert len(candidates)==1,decl;referenced[candidates[0]]=selected['proof_files'][candidates[0]]['sha256']
assert keys=={'primer-linalg.html::node-197','primer-linalg.html::node-199','primer-linalg.html::node-209'} and len(removed)==3
assert [r for r in old['material_claims']if r['id']not in removed]==[r for r in c['material_claims']if r['id']not in newids]
rest=copy.deepcopy(c);rest['material_claims']=copy.deepcopy(old['material_claims']);rest['proof_files']=copy.deepcopy(old['proof_files']);rest['proof_sha256']=copy.deepcopy(old['proof_sha256']);rest['counts']=copy.deepcopy(old['counts']);rest['limits']=copy.deepcopy(old['limits']);del rest['current26_owner_identity'];del rest['current26_material_mapping'];assert rest==old
assert set(c['proof_files'])==set(old['proof_files'])|set(d['proof_files'])|set(referenced) and len(c['proof_files'])==len(old['proof_files'])+2==247
assert {n:c['proof_sha256'][n]for n in old['proof_sha256']}==old['proof_sha256'];assert i['referenced_existing_selected25_proof_sources']==referenced
assert physical(old)=={'proved':772,'not_a_formal_claim':524,'pending':460}and physical(c)=={'proved':775,'not_a_formal_claim':524,'pending':457}
for absolute,r in i['all_original_TMP_byte_aliases'].items():assert P(absolute).read_bytes()==P(r['file']).read_bytes()and H(r['file'])==r['sha256'];closure[r['file']]=r['sha256']
for n,h in closure.items():assert H(n)==h,n
for n,r in selected['proof_files'].items():assert H(n)==r['sha256']==H('reports/full-coverage/checkpoint-25/'+n)
manifest=J('reports/full-coverage/checkpoint-25-manifest.json');assert manifest['status']=='formal_verification_passed_partial_coverage'
assets={n:h for n,h in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
owners={n:manifest['working_inputs_sha256'][n]for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
for n,h in assets.items():assert H(n)==h==H('reports/full-coverage/checkpoint-25/'+n)
for n,h in owners.items():assert H(n)==h
act=B+'/foundations26-isolated-candidate-builder-actual-execution-v1.json';a=J(act);zero(a);assert a['helper']==d['current_owner_builder'] and H(a['helper'])==a['helper_sha256_before']==a['helper_sha256_after']==d['current_owner_builder_sha256'];assert H(a['log'])==a['log_sha256'];closure.update({act:H(act),a['log']:H(a['log']),a['helper']:H(a['helper']),a['actual_runner']:H(a['actual_runner'])})
assert not OUT.exists();OUT.write_text(json.dumps({'status':'passed_independent_exact_foundations26_candidate_mapping_mechanics','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent Modules domain agent; exact mapping/evidence mechanics only','candidate':ref(C),'draft_offer':ref(D),'interface':ref(I),'actual_isolated_candidate_preparation':ref(act),'original_semantic_bodies_and_times_unchanged':True,'exact_entire_inverse_restores_installed25_ledger':True,'old_exercise_bodies_exact':119,'old_proved_atoms_exact':1104,'other_entire_material_records_exact':1753,'whole_literal_keys':sorted(keys),'new_source_count':2,'new_public_exports':15,'actual_canonical_record_count':4,'baseline_proof_metadata_exact':245,'protected_selected25_source_count':1156,'protected_current52_asset_count':31,'protected_installed25_owner_count':5,'closed_evidence_sha256':closure,'own_checker':ref(str(Path(__file__))),'coverage_complete':False,'scope':'Three original approved whole literal decisions/hypotheses/reasons/declarations/time mapped exactly, old119 exercises/all1104 positive atoms preserved; two genuine canonical pairs and source bodies remain exact. No live integration, new semantic decision, compiler invocation or aggregate26 claim.'},indent=2)+'\n');print(json.dumps(ref(str(OUT))))
