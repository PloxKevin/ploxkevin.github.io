"""Read-only independent inverse/mapping/actual TMP evidence audit; no canonical execution."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/foundations27-source55-three-source43-five-whole-unit-draft-v2')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(p),'sha256':H(p)}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else R/p;assert H(p)==r['sha256'],str(p);return p
ready=B/'foundations27-current55-three-source43-five-whole-unit-readiness-draft-v1.json';assert H(ready)=='1796b230351781e57b26921ccf47b92fff5a561500d292af1b4c6a413c6f7c7e';d=J(ready)
C=checked(d['candidate_ledger']);I=checked(d['interface']);P=checked(d['canonical_pair_plan']);BASE=checked(d['installed26_baseline']);INV=checked(d['current55_inventory'])
assert H(C)=='f3e3e1f9a2e4df54cf63dedf1024b832613de685490dc182909c7fbafc859ccf';assert H(I)=='6eeb431a61714664f027d064bed7b624a6417f7b7556c2505cecf28d7a57f68e';assert H(P)=='cfa5e5aaf7a32bdbbb4493ec87cc2232ae0141fba970af8974073dfc95147eca';assert H(BASE)=='60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a';assert H(INV)==H(R/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
old,c,inter,plan,inv=J(BASE),J(C),J(I),J(P),J(INV);oldinv=J(R/'book/coverage/inventory-after-correction53.json');scope=set(old['scope_pages'])
for sec,count in [('exercises',119),('material_source_units',1756)]:
 a={r['key']:r for r in oldinv[sec]if r['source']in scope};b={r['key']:r for r in inv[sec]if r['source']in scope};assert a==b and len(b)==count
allunits={r['key']:r for r in inv['material_source_units']};oldrows={r['id']:r for r in old['material_claims']};newrows={r['id']:r for r in c['material_claims']};assert len(oldrows)==len(old['material_claims'])and len(newrows)==len(c['material_claims'])
removed=[];added=[];reviews={};evidence={}
for mp in inter['material_units']:
 key=mp['source_unit_key'];unit=mp['entire_original_whole_literal_peer_row'];semfile=checked(mp['original_semantic_review']);sem=J(semfile);reviews[str(semfile)]=sem
 assert sem['errors']==[] and unit in sem['material_units']and unit['whole_literal_approved']is True and unit['missing_clauses']==[]
 assert mp['entire_current55_inventory_record']==unit['entire_inventory_record']==allunits[key]
 assert mp['original_reviewed_at_utc']==sem['reviewed_at_utc']
 prior=[r for r in old['material_claims']if key in r['source_unit_keys']];pending=[r for r in prior if r['status']=='pending'];assert len(pending)==1 and pending[0]['source_unit_keys']==[key]and mp['entire_original_pending_rows']==pending
 assert mp['retained_original_nonpending_rows']==[r for r in prior if r['status']!='pending']
 row=mp['new_candidate_claim'];assert newrows[row['id']]==row and row['id']not in oldrows and row['source_unit_keys']==[key]and row['status']=='proved'and row['remaining_gaps']==[]
 assert row['source_text']==row['statement_in_prose']==unit['entire_inventory_record']['source_text'];assert row['source_text_sha256']==allunits[key]['text_sha256']and row['source_sha256']==allunits[key]['source_sha256']
 assert row['lean_declarations']==unit['lean_declarations']and row['correspondence']==unit['reason'];hyps=unit['hypotheses'];assert row['hypotheses']==(hyps if isinstance(hyps,list)else[hyps]);assert row['source_review']['reviewed_at_utc']==sem['reviewed_at_utc']and row['source_review']['reviewer']==sem['reviewer']and row['source_review']['sha256']==H(semfile)
 removed.append(pending[0]['id']);added.append(row['id'])
assert len(removed)==len(set(removed))==len(added)==5
assert {r['source_unit_key']for r in inter['material_units']}=={'primer-linalg.html::node-'+str(k)for k in [1264,1266,1268,1269,1289]}
assert [r for r in old['material_claims']if r['id']not in removed]==[r for r in c['material_claims']if r['id']not in added]
recovered=copy.deepcopy(c);recovered['material_claims']=[copy.deepcopy(oldrows[r['id']])if r['id']in removed else copy.deepcopy(newrows[r['id']])for r in old['material_claims']];recovered['counts']['material_claim_statuses']=copy.deepcopy(old['counts']['material_claim_statuses']);assert len(c['limits'])==len(old['limits'])+1;assert c['limits'][:-1]==old['limits'];recovered['limits']=copy.deepcopy(old['limits']);assert 'current55_owner_identity'not in old and 'current27_material_mapping_draft'not in old;recovered.pop('current55_owner_identity');recovered.pop('current27_material_mapping_draft');assert recovered==old
assert c['exercises']==old['exercises']and len(c['exercises'])==119;assert c['proof_files']==old['proof_files']and c['proof_sha256']==old['proof_sha256']and len(c['proof_files'])==247
assert c['counts']['material_claim_statuses']==dict(Counter(r['status']for r in c['material_claims']));assert d['original_positive_claim_count']==1107 and d['new_positive_claim_count']==1112 and d['original_pending_claim_count']==488 and d['new_pending_claim_count']==483
for n,h in c['source_sha256'].items():assert H(R/n)==h
assert len(inter['exact_original_byte_aliases'])==d['original_byte_alias_count']==110
historyroot=R/'reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root'
for k,v in inter['exact_original_byte_aliases'].items():
 n,h=v['original_path'],v['original_sha256'];assert k==n+'::'+h
 dest=checked(v['immutable_byte_copy']);actual=Path(v['actual_byte_copy_source']);assert H(actual)==h and actual.read_bytes()==dest.read_bytes();orig=Path(n)if Path(n).is_absolute()else R/n
 if not orig.exists()or H(orig)!=h:
  rel=orig.relative_to(R);assert actual==historyroot/rel and H(actual)==h
 evidence[str(dest)]=h
assert plan['planned_sources']==c['current27_material_mapping_draft']['planned_proof_files'];assert len(plan['planned_sources'])==3 and plan['public_export_count']==43 and plan['planned_canonical_commands']==6;assert plan['paired_execution_records']==[]and plan['canonical_or_named_execution_claimed']is False;assert inter['canonical_pair_execution_count']==d['canonical_pair_execution_count']==0 and d['eligible_for_owner_integration_or_selection']is False
names=[];counts=[]
for n,row in plan['planned_sources'].items():
 src=checked(row['exact_original_tmp_source']);s=src.read_text();assert s==row['entire_source_bytes']and H(src)==row['source_sha256'];assert not (R/n).exists();assert n.startswith('verification/lean/SafeLearning/')and n.endswith('.lean')
 currentns=None;decls=[]
 for line in s.splitlines():
  if line.startswith('namespace '):currentns=line.split()[1]
  if line.startswith('theorem '):decls.append(currentns+'.'+line.split()[1])
 assert decls==row['all_public_declarations']and len(decls)==row['public_theorem_count'];assert not re.search(r'\b(sorry|admit|axiom)\b',s);names+=decls;counts.append(len(decls))
 sempath=checked(row['original_full_source_semantic_peer']);sem=J(sempath);assert reviews[str(sempath)]==sem and sem['source']==row['exact_original_tmp_source'];packet=next(x for x in inter['proof_packets']if x['planned_canonical_source']==n);assert packet['entire_original_semantic_body_and_time']==sem
 actualfile=checked(row['actual_original_tmp_standalone']);a=J(actualfile);assert packet['entire_genuine_tmp_standalone_body_and_time']==a
 codes=[a[k]for k in ('actual_exit_code','actual_runner_exit_code')if k in a];assert len(codes)==2 and all(type(code)is int and code==0 for code in codes);assert a['actual_command']==['lake','env','lean',str(src)]and a['actual_workdir']==str(R/'verification/lean')and a['protection_errors']==[];assert H(a['source_snapshot'])==a['source_sha256_before']==a['source_sha256_after']==H(src)and H(a['raw_log'])==a['raw_log_sha256'];assert all(row[k]is False for k in ['canonical_source_installation_executed','canonical_standalone_executed','named_build_executed','namespace_or_body_changes_planned'])
 target=Path(n).stem;assert row['canonical_pair_plan']==[{'kind':'standalone','command':['lake','env','lean','SafeLearning/'+target+'.lean']},{'kind':'named','command':['lake','build','SafeLearning.'+target]}];assert row['actual_workdir']==str(R/'verification/lean')
assert counts==[16,10,17]and len(names)==len(set(names))==43
prep=Path('/tmp/foundations27-source55-five-whole-unit-draft-preparation-actual-v2.json');a=J(prep);assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0;helper=Path('/tmp/prepare-foundations27-source55-five-whole-unit-draft-v2.py');assert H(helper)=='0708b2bce819c301cb7c62fcbbe74d34f332af335ce77a90849ec8ca6b20a98d';checked(d['prepared_by']);assert d['prepared_by']['file']==str(helper);failed=d['original_preparer_v1_failure'];assert J(checked(failed['record']))==failed['entire_original_actual_body_and_time'];f=failed['entire_original_actual_body_and_time'];assert type(f['actual_exit_code'])is int and f['actual_exit_code']==1
sel=J(R/'reports/full-coverage/checkpoint-26-selection.json');assert len(sel['proof_files'])==1167
for n,r in sel['proof_files'].items():assert H(R/n)==r['sha256'],n
binding=J(R/'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json');app=J(R/'reports/full-coverage/source54-55-corrections-application-v1.json');assets={**binding['exact_current53_safelearning_assets_sha256'],**{r['source_after']['file']:r['source_after']['sha256']for r in app['applications']}};assert len(assets)==31
for n,h in assets.items():assert H(R/n)==h,n
for n,h in d['preserved_installed26_owner_sha256'].items():assert H(R/n)==h,n
assert len(d['preserved_installed26_owner_sha256'])==5
out=Path('/tmp/foundations27-current55-draft-independent-applied-check-result-v1.json');assert not out.exists();report={'status':'passed_independent_tmp_only_foundations27_current55_draft_mechanics_pair_plan_pending','errors':[],'reviewer':'/root/applied_next; independent of Foundation author and Module semantic peers','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'readiness':ref(ready),'candidate':ref(C),'interface':ref(I),'canonical_pair_plan':ref(P),'baseline_installed26':ref(BASE),'current55_inventory':ref(INV),'exact_entire_ledger_inverse':True,'all119_exercises_247_oldproof_rows_and_original_nonpending_material_rows_exact':True,'five_material_keys':[r['source_unit_key']for r in inter['material_units']],'entire_original_semantic_reviews_body_and_time':reviews,'all_five_original_decisions_hypotheses_names_reasons_times_match':True,'all110_original_byte_aliases_exact':True,'three_source_counts':counts,'all43_original_public_names_unique_exact':True,'actual_three_original_tmp_compilers_zero_and_all_failure_warning_history_retained':True,'paired_canonical_execution_count':0,'eligible_for_live_integration_or_selection':False,'all1167_proofs_31_current55_assets_and_five_owners_exact':True,'original_preparer_v1_failure':failed,'checked_exact_byte_evidence':evidence,'scope':'Read-only candidate/mapping/history/pending-plan mechanics. Original semantic decisions/body/time retained verbatim, no semantic rereview. Planned canonical sources/commands are unexecuted and no eligible offer or proof-selection pass is claimed; actual6 canonical commands and a separate narrow binding/final mapping peer remain required.'};out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'report':ref(out),'status':report['status'],'errors':[],'original_whole_review_count':3,'original_mapped_decision_count':5,'canonical_pair_execution_count':0}))
