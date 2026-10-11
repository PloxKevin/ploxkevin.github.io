"""NEW isolated Foundation26 candidate: three exact whole literals; no installed ledger mutation."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import json,hashlib,re,copy
R=Path(__file__).resolve().parents[2];B=R/'book/coverage/checks/foundations-future26/source52';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());rel=lambda p:Path(p).relative_to(R).as_posix();ref=lambda p:{'file':rel(p),'sha256':H(p)}
OLD=R/'book/coverage/foundations.json';OS='9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada';INV=R/'book/coverage/inventory-after-correction52.json';IS='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';PACK=R/'book/coverage/checks/foundations-future26/metric-isometry/two-source15-canonical-paired-readiness-v1.json';PS='047f99bf8bbac7974db392993e316e97531237107bb4553e2b168bd1fefdc950';PEER=Path('/tmp/foundations26-metric-isometry-canonical-original-body-binding-independent-modules-v1.json');PEERSHA='db18f351445a96334ba52d32bf50230917f9ac2923b9dad22d757e79a7eca92f'
def zero(d):
 ks=[k for k in ['actual_exit_code','exit_code']if k in d];assert ks and all(type(d[k])is int and d[k]==0 for k in ks)
def bind(r):
 p=Path(r['file']);p=p if p.is_absolute()else R/p;assert H(p)==r['sha256'],str(p);return p
def write(p,d):
 with p.open('x')as f:json.dump(d,f,ensure_ascii=False,indent=2);f.write('\n')
def physical(d):
 by={}
 for row in d['material_claims']:
  for k in row['source_unit_keys']:by.setdefault(k,set()).add(row['status'])
 c=Counter('pending'if'pending'in s else'not_a_formal_claim'if s=={'not_a_formal_claim'}else'proved'for s in by.values());return {'total':len(by),'whole_proved':c['proved'],'nonformal':c['not_a_formal_claim'],'whole_pending':c['pending']}
assert H(OLD)==OS and H(INV)==H(R/'book/coverage/inventory.json')==IS and H(PACK)==PS and H(PEER)==PEERSHA
old=J(OLD);inv=J(INV);pack=J(PACK);peer=J(PEER);assert 'passed'in peer['status']and peer['errors']==[] and peer['source_count']==2 and peer['public_theorem_count']==15 and peer['actual_canonical_record_count']==4
MAN=R/'reports/full-coverage/checkpoint-25-manifest.json';SEL=R/'reports/full-coverage/checkpoint-25-selection.json';AUD=R/'reports/full-coverage/lean-checkpoint-25/verification-original.json';m=J(MAN);audit=J(AUD);assert m['status']=='formal_verification_passed_partial_coverage' and m['selection_sha256']==H(SEL) and m['successful_verification']['report_sha256']==H(AUD) and audit['status']=='passed' and len(m['proof_files'])==audit['proof_file_count']==1156 and audit['theorem_count']==9369
selected={p:v['sha256']for p,v in m['proof_files'].items()};assets={p:h for p,h in m['working_inputs_sha256'].items()if p.startswith('SafeLearning/')};assert len(assets)==31
owners={p:m['working_inputs_sha256'][p]for p in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']};protected={**selected,**assets,**owners,**old['source_sha256'],rel(INV):IS,'book/coverage/inventory.json':IS,rel(SEL):H(SEL)}
def guard():
 for p,h in protected.items():assert H(R/p)==h,p
 for p,h in {**selected,**assets}.items():assert H(R/'reports/full-coverage/checkpoint-25'/p)==h,p
for stem in ['verify-checkpoint25-execution-v1','export-checkpoint25-execution-v1']:
 a=J(R/'reports/full-coverage'/f'{stem}.json');zero(a);assert H(R/a['log'])==a['log_sha256']
guard();B.mkdir(parents=True,exist_ok=True)
C=B/'foundations26-candidate-source52-v1.json';I=B/'foundations26-three-whole-literal-interface-source52-v1.json';D=B/'foundations-audit26-candidate-source52-additions-draft-v1.json';G=B/'candidate-original25-preservation-source52-v1.json';HELD=B/'held-foundations25-original-source52-v1.json';assert not any(p.exists()for p in [C,I,D,G,HELD])
with HELD.open('xb')as f:f.write(OLD.read_bytes())
prep=J(bind(pack['canonical_preparation']));aliases=copy.deepcopy(prep['canonical_original_byte_aliases']);additional={rel(PACK):PS,rel(bind(pack['canonical_preparation'])):pack['canonical_preparation']['sha256']}
for p,r in aliases.items():assert bind(r).read_bytes()==Path(p).read_bytes();additional[r['file']]=r['sha256']
PD=B/'original-independent-module-canonical-binding-v1';assert not PD.exists();PD.mkdir()
peeractual=Path('/tmp/foundations26-metric-isometry-canonical-independent-modules-actual-v1.json');pa=J(peeractual);zero(pa);assert H(Path(pa['raw_log']))==pa['raw_log_sha256'] and H(Path(pa['actual_command'][1]))==pa['actual_helper_sha256_before']==pa['actual_helper_sha256_after'] and H(Path(pa['actual_runner']))==pa['actual_runner_sha256']
originals=[PEER,Path(pa['actual_command'][1]),peeractual,Path(pa['raw_log']),Path(pa['actual_runner']),Path('/tmp/foundations26-metric-isometry-canonical-reused-runner-label-observation-v1.json')]
for p in originals:
 q=PD/p.name
 with q.open('xb')as f:f.write(p.read_bytes())
 assert H(p)==H(q);aliases[str(p)]=ref(q);additional[rel(q)]=H(q)
peerref=aliases[str(PEER)];labelref=aliases[str(originals[-1])]
units={u['key']:u for u in inv['material_source_units']if u['source']in old['scope_pages']};exs={e['key']:e for e in inv['exercises']if e['source']in old['scope_pages']};assert len(units)==1756 and len(exs)==119
iv48=J(R/'book/coverage/inventory-after-correction48.json');u48={u['key']:u for u in iv48['material_source_units']};e48={e['key']:e for e in iv48['exercises']};assert all(r==u48[k]for k,r in units.items())and all(r==e48[k]for k,r in exs.items())
candidate=copy.deepcopy(old);newproofs={};newnames=set();packets=[];maps=[];removed=set();mapped=set();semanticrefs={};actualrefs={};declfiles={d['name']:d['file']for d in audit['declarations']};referenced={};covered=set()
assert pack['public_theorem_count']==15 and pack['actual_canonical_execution_count']==4
for s in pack['proof_sources']:
 src=bind(s['source']);text=src.read_text();snapshot=bind(s['source_snapshot']);assert H(src)==H(snapshot)==s['original_source']['sha256'];ns=re.search(r'^namespace (\S+)',text,re.M)[1];names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)];assert names==s['public_theorems'] and not newnames.intersection(names) and rel(src)not in selected and rel(src)not in old['proof_files'] and not re.search(r'\b(sorry|admit|axiom)\b',text);newnames.update(names)
 for n in names:declfiles[n]=rel(src)
 sr=aliases[s['original_semantic_peer']['file']];sp=bind(sr);sem=J(sp);assert sem==s['entire_original_semantic_body_and_time'] and 'passed'in sem['status']and sem['errors']==[] and sem['full_source_body_read']==text;semanticrefs[rel(sp)]=H(sp)
 match=[g for g in peer['groups']if g['source']==s['source']];assert len(match)==1 and match[0]['entire_original_semantic_body_and_time']==sem and match[0]['literal_unit_decisions_unchanged']==sem['literal_unit_decisions']
 ev={rel(snapshot):H(snapshot)};pairs=[]
 for pr in s['actual_canonical_pair']:
  rp=bind(pr['record']);a=J(rp);zero(a);log=R/a['log'];assert H(log)==a['log_sha256'] and a['source']==rel(src) and a['source_sha256_before']==a['source_sha256_after']==H(src) and a['actual_workdir']==str(R/'verification/lean') and a['command']in [['lake','build','SafeLearning.'+src.stem],['lake','env','lean','SafeLearning/'+src.name]] and a['started_at_utc']<a['finished_at_utc'] and a['elapsed_seconds']>0
  ev.update({rel(rp):H(rp),rel(log):H(log)});actualrefs[rel(rp)]=H(rp);pairs.append({'record':ref(rp),'entire_original_actual_record_and_time':a,'raw_log':ref(log),'source_snapshot':ref(snapshot)})
 assert len(pairs)==2 and {p['entire_original_actual_record_and_time']['command'][1]for p in pairs}=={'env','build'}
 newproofs[rel(src)]={'sha256':H(src),'evidence_sha256':ev,'evidence_scope':'Four genuine canonical standalone/named native records, actual nonempty warning logs and exact snapshots preserved. Aggregate26/selection/live ownership remain separate.'};candidate['proof_files'].append(rel(src));candidate['proof_sha256'][rel(src)]=H(src)
 packets.append({'canonical_source':ref(src),'public_theorem_names':names,'original_semantic_review':sr,'entire_original_semantic_body_and_time':sem,'actual_pair':pairs,'canonical_readiness':ref(PACK)})
 for row in sem['literal_unit_decisions']:
  k=row['key'];u=units[k];assert row['entire_inventory_record']==u==u48[k] and k not in mapped and row['status']=='approved_whole_literal'and row['missing_clauses']==[];mapped.add(k)
  declarations=row['lean_declarations'];assert declarations and row['reason'] and row['hypotheses']
  for n in declarations:
   assert n in declfiles,n
   p=declfiles[n]
   if p in selected:
    referenced[p]=selected[p]
    if p not in candidate['proof_files']:candidate['proof_files'].append(p);candidate['proof_sha256'][p]=selected[p]
  covered.update(set(declarations)&newnames);prior=[r for r in old['material_claims']if k in r['source_unit_keys']];pending=[r for r in prior if r['status']=='pending'];assert len(pending)==1 and pending[0]['source_unit_keys']==[k];removed.add(pending[0]['id']);reviewtime=row.get('reviewed_at_utc',sem['reviewed_at_utc'])
  new={'id':k+'::independently-reviewed26-whole-literal','source_unit_keys':[k],'source':u['source'],'locator':u['locator'],'source_text':u['source_text'],'source_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'statement_in_prose':u['source_text'],'kind':'independently_reviewed_complete_mathematical_literal','status':'proved','lean_declarations':declarations,'hypotheses':row['hypotheses'],'correspondence':row['reason'],'remaining_gaps':[],'source_review':{**sr,'reviewed_at_utc':reviewtime,'reviewer':sem['reviewer'],'reviewer_scope':'Exact original whole mathematical unit/body/time preserved; narrow canonical binding records no new semantic decision.'}}
  candidate['material_claims']=[r for r in candidate['material_claims']if r['id']!=pending[0]['id']];candidate['material_claims'].append(new);maps.append({'source_unit_key':k,'entire_current52_inventory_record':u,'entire_original_whole_literal_peer_row':row,'original_semantic_review':sr,'original_reviewed_at_utc':reviewtime,'original_full_peer_reviewed_at_utc':sem['reviewed_at_utc'],'entire_original_pending_clauses':pending,'retained_original_nonpending_clauses':[r for r in prior if r['status']!='pending'],'new_candidate_claim':new})
assert mapped=={'primer-linalg.html::node-197','primer-linalg.html::node-199','primer-linalg.html::node-209'} and len(newnames)==15 and len(newproofs)==2 and covered==newnames and len(removed)==3
candidate['proof_files']=sorted(set(candidate['proof_files']));candidate['counts']['material_claim_statuses']=dict(Counter(r['status']for r in candidate['material_claims']));newids={x['new_candidate_claim']['id']for x in maps};assert candidate['exercises']==old['exercises']and candidate['surrounding_prose_reviews']==old['surrounding_prose_reviews']and candidate['source_sha256']==old['source_sha256'] and [r for r in old['material_claims']if r['id']not in removed]==[r for r in candidate['material_claims']if r['id']not in newids]
assert sum(r['status']=='proved'for r in old['material_claims'])==1104 and physical(old)=={'total':1756,'whole_proved':772,'nonformal':524,'whole_pending':460} and physical(candidate)=={'total':1756,'whole_proved':775,'nonformal':524,'whole_pending':457}
candidate['current26_owner_identity']={'inventory':ref(INV),'original25_ledger':ref(HELD),'original25_selection':ref(SEL),'actual_passed25_aggregate':ref(AUD),'unchanged_entire_foundation_source_records':1756,'unchanged_entire_foundation_exercise_records':119,'scope':'Isolated candidate only; installed25 owners, frozen25 snapshot and all current52 assets remain exact.'}
candidate['current26_material_mapping']={'interface_binding':rel(I),'whole_material_units':3,'removed_prior_pending_claims':3,'new_public_exports':15,'new_proof_sources':2,'already_selected_referenced_declaration_sources':referenced,'physical_before':physical(old),'physical_after':physical(candidate),'scope':'Exact original three complete literal decisions/reasons/hypotheses/times and narrow canonical evidence binding preserved.'}
candidate['limits'].append('Future26 isolated current52 Foundation candidate adds3 independently approved complete metric/set-distance/isometric-embedding literals using2 exact canonical paired sources/15 exports. All119 complete exercises,1104 prior proved atoms and old full semantic bodies/times remain exact. Remaining457 physical units still need mathematical work; no aggregate26 or live installation claim.');write(C,candidate);guard()
interface={'status':'exact_three_original_complete_semantic_decisions_and_times_bound_to_isolated_candidate26','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':ref(C),'held_original25_ledger':ref(HELD),'current_inventory':ref(INV),'material_units':maps,'proof_packets':packets,'all_original_TMP_byte_aliases':aliases,'independent_canonical_binding_peer':peerref,'entire_original_canonical_binding_peer_body_and_time':peer,'reused_runner_label_limitation':labelref,'referenced_existing_selected25_proof_sources':referenced,'all1756_units_and119_exercises_equal_source48_to52':True,'all1104_original_proved_atoms_and_semantic_bodies_times_exact':True,'physical_before':physical(old),'physical_after':physical(candidate),'coverage_complete':False};write(I,interface)
additional.update({rel(I):H(I),rel(HELD):H(HELD),**semanticrefs,**actualrefs})
for pkt in packets:
 for pair in pkt['actual_pair']:
  for field in ['raw_log','source_snapshot']:additional[pair[field]['file']]=pair[field]['sha256']
for p in [R/'book/coverage/checks/run_foundations26_metric_isometry_canonical_pair_v1.py',R/'book/coverage/checks/run_foundations26_metric_isometry_actual_wrapper_v1.py',R/'book/coverage/checks/foundations26-metric-isometry-canonical-pair-execution-v1.json',R/'book/coverage/checks/foundations26-metric-isometry-canonical-pair-execution-v1.log']:
 additional[rel(p)]=H(p)
outer=J(R/'book/coverage/checks/foundations26-metric-isometry-canonical-pair-execution-v1.json');zero(outer)
for p,h in additional.items():assert H(R/p)==h,p
newproofsfiles=sorted(newproofs)
draft={'schema_version':1,'status':'isolated_actual_two_source15_export_three_whole_literal_candidate26_pending_independent_final_mechanics','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'base_selection':rel(SEL),'base_selection_sha256':H(SEL),'actual_passing_baseline_audit':rel(AUD),'actual_passing_baseline_audit_sha256':H(AUD),'proof_files':newproofs,'new_proof_sources_for_checkpoint26':newproofsfiles,'new_proof_file_count':2,'new_theorem_or_lemma_count':15,'mapped_ledger':rel(C),'mapped_ledger_sha256':H(C),'held25_ledger':rel(HELD),'held25_ledger_sha256':H(HELD),'working25_ledger':'book/coverage/foundations.json','working25_ledger_sha256':OS,'source_sha256':candidate['source_sha256'],'current_inventory':rel(INV),'current_inventory_sha256':IS,'current_owner_builder':rel(Path(__file__)),'current_owner_builder_sha256':H(Path(__file__)),'exact_source_reviews_sha256':semanticrefs,'actual_canonical_execution_records_sha256':actualrefs,'canonical_readiness_sha256':{rel(PACK):PS},'material26_exact_interface_binding':rel(I),'material26_exact_interface_binding_sha256':H(I),'new_material_dispositions':{'exact_current_rows':3,'whole_proved':3,'nonformal':0,'whole_pending':0,'previous_pending_claims_removed':3},'exercise_counts':candidate['counts']['exercise_statuses'],'material_counts':physical(candidate),'additional_frozen_inputs':additional,'original_semantic_reviews_body_and_time_retained':True,'independent_canonical_binding_peer':peerref,'reused_runner_label_limitation':labelref,'independent_final_candidate_mapping_peer_pending':True,'actual_builder_record_pending':True,'coverage_complete':False,'scope':'Isolated candidate only;3 exact source52 whole literals,15 genuine canonical exports,119 exercises/1104 old positive atoms and all prior full bodies/times preserved; no current25 owner/HTML/inventory/frozen25 mutation or aggregate26 claim.'};write(D,draft);guard()
write(G,{'status':'passed_isolated_candidate_preserves_all_prior25_bodies_and_frozen_sources','checked_at_utc':datetime.now(timezone.utc).isoformat(),'held25_ledger':ref(HELD),'candidate':ref(C),'interface':ref(I),'draft_offer':ref(D),'all1156_selected25_sources_and_frozen_copies_exact':True,'all31_current52_assets_and_frozen_copies_exact':True,'five_installed25_owner_sha256':owners,'all119_exercise_bodies_and1104_prior_proved_atoms_exact':True,'all1756_entire_foundation_source_records_equal48_to52':True,'removed_pending_claim_ids':sorted(removed),'coverage_complete':False});guard();print(json.dumps({'status':'passed','candidate':ref(C),'interface':ref(I),'draft_offer':ref(D),'preservation':ref(G),'new_sources':2,'new_exports':15,'whole_units':3,'physical_after':physical(candidate)}))
