from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,re,copy
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());real=lambda f:Path(f)if Path(f).is_absolute()else R/f
closed={}
def checked(r):
 assert set(r)=={'file','sha256'};p=real(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'],r;closed[r['file']]=r['sha256'];return p
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':H(p)}
def zero(d):
 codes=[d[k]for k in ['actual_exit_code','exit_code','actual_runner_exit_code']if k in d];assert codes and all(type(c)is int and c==0 for c in codes)
B=R/'book/coverage/checks/foundations-future27/source55';OP=B/'foundations-audit27-candidate-source55-additions-v1.json';assert H(OP)=='5114ee9d15f977df95dae5e98c47e84f2ae07dd7224c00270da5d650d1b485e2';offer=J(checked(ref(OP)));C=checked(offer['candidate']);candidate=J(C);BP=checked(offer['material27_exact_interface_binding']);binding=J(BP)
P=Path('/tmp/foundations27-current55-draft-independent-applied-confirmation-v1.json');assert H(P)=='733a98acc304123c805e12e9b08ee89fb8bfa7b1251c5b662b4f41fdaf045119';prior=J(checked(ref(P)));assert prior['errors']==[] and prior['exact_entire_ledger_inverse']is True
D=checked(prior['candidate']);draft=J(D);I=checked(prior['interface']);interface=J(I);old=J(checked(prior['baseline_installed26']));assert H(C)==offer['mapped_ledger_sha256']and offer['mapped_ledger']==ref(C)['file']and binding['candidate']==offer['candidate']
assert offer['proof_files']==binding['new_proof_files'];assert len(offer['proof_files'])==3 and offer['new_theorem_or_lemma_count']==43 and offer['new_whole_material_units']==5 and offer['actual_canonical_commands']==6
assert binding['material_units']==interface['material_units']and binding['original_closed_byte_aliases']==offer['original_closed_byte_aliases']
assert len(offer['original_closed_byte_aliases'])==124
for k,r in offer['original_closed_byte_aliases'].items():
 assert k==r['original_path']+'::'+r['original_sha256']and r['immutable_byte_copy']['sha256']==r['original_sha256'];dst=checked(r['immutable_byte_copy']);src=real(r['byte_copy_source']);assert H(src)==r['original_sha256']and src.read_bytes()==dst.read_bytes()
for f,h in prior['closed_evidence_sha256'].items():
 key=f+'::'+h;assert key in offer['original_closed_byte_aliases'];checked(offer['original_closed_byte_aliases'][key]['immutable_byte_copy'])
for f,h in offer['additional_frozen_inputs'].items():checked({'file':f,'sha256':h})
assert J(checked(offer['original_independent_draft_mechanics_peer']))==prior
mapping=candidate['current27_material_mapping'];assert mapping['full_original_semantic_body_time_scope_preserved']is True and len(mapping['active_review_path_changes'])==5
rev=copy.deepcopy(candidate);rev.pop('current27_material_mapping');rev['proof_files']=mapping['original_proof_files'];rev['proof_sha256']=mapping['original_proof_sha256']
for c in mapping['active_review_path_changes']:
 row=next(r for r in rev['material_claims']if r['id']==c['claim_id']);assert row['source_review']==c['canonical_source_review'];row['source_review']=c['original_source_review'];assert J(checked({'file':c['canonical_source_review']['file'],'sha256':c['canonical_source_review']['sha256']}))==J(real(c['original_source_review']['file']))
assert rev==draft,'canonical inverse differs from full reviewed TMP draft'
oldrows={r['id']:r for r in old['material_claims']};newrows={r['id']:r for r in draft['material_claims']};remove=[];add=[];allunits={r['key']:r for r in J(checked(prior['current55_inventory']))['material_source_units']};reviews={}
for mp in interface['material_units']:
 sem=J(checked(mp['original_semantic_review']));unit=mp['entire_original_whole_literal_peer_row'];assert unit in sem['material_units']and unit['whole_literal_approved']is True and unit['missing_clauses']==[]
 assert allunits[mp['source_unit_key']]==mp['entire_current55_inventory_record']==unit['entire_inventory_record'];assert sem['reviewed_at_utc']==mp['original_reviewed_at_utc']
 row=mp['new_candidate_claim'];assert newrows[row['id']]==row and row['correspondence']==unit['reason']and row['lean_declarations']==unit['lean_declarations'];assert row['hypotheses']==(unit['hypotheses']if isinstance(unit['hypotheses'],list)else[unit['hypotheses']]);assert row['source_review']['reviewed_at_utc']==sem['reviewed_at_utc']and row['statement_in_prose']==unit['entire_inventory_record']['source_text'];remove.extend(r['id']for r in mp['entire_original_pending_rows']);add.append(row['id']);reviews[mp['original_semantic_review']['file']]=sem
restored=copy.deepcopy(draft);restored['material_claims']=[copy.deepcopy(oldrows[r['id']])if r['id']in remove else copy.deepcopy(newrows[r['id']])for r in old['material_claims']];restored['counts']['material_claim_statuses']=old['counts']['material_claim_statuses'];restored['limits']=old['limits'];restored.pop('current55_owner_identity');restored.pop('current27_material_mapping_draft');assert restored==old,'combined inverse differs from complete installed26 ledger'
assert set(remove).isdisjoint(add)and len(remove)==len(add)==5
assert candidate['exercises']==old['exercises']and len(candidate['exercises'])==119 and len(old['proof_files'])==247 and len(candidate['proof_files'])==250
assert candidate['proof_files']==sorted(old['proof_files']+list(offer['proof_files']))and candidate['proof_sha256']==old['proof_sha256']|{k:r['sha256']for k,r in offer['proof_files'].items()}
assert candidate['counts']['material_claim_statuses']==dict(Counter(r['status']for r in candidate['material_claims']))
for f,h in candidate['source_sha256'].items():checked({'file':f,'sha256':h})
PA=checked(offer['actual_canonical_paired_readiness']);pairs=J(PA);assert pairs['errors']==[]and pairs['actual_compiler_command_count']==16 and pairs['source_count']==8 and pairs['public_theorem_count']==141
outer=J(checked(offer['actual_canonical_pair_execution']));zero(outer);assert outer['actual_command']==['python3','book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py','--apply']and outer['actual_workdir']==str(R);assert outer['helper_sha256_before']==outer['helper_sha256_after'];checked({'file':outer['log'],'sha256':outer['log_sha256']})
for f,h in outer['helper_sha256_before'].items():checked({'file':f,'sha256':h})
commands=[];names=[];sources=[]
for f,row in offer['proof_files'].items():
 canonical=checked({'file':f,'sha256':row['sha256']});packet=next(x for x in interface['proof_packets']if x['planned_canonical_source']==f);original=checked(packet['original_tmp_source']);assert canonical.read_bytes()==original.read_bytes();text=canonical.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 ns='';decls=[]
 for line in text.splitlines():
  if line.startswith('namespace '):ns=line.split()[1]
  if line.startswith('theorem '):decls.append(ns+'.'+line.split()[1])
 assert decls==row['public_theorem_names']==row['mapped_named_declarations']and len(decls)==row['theorem_count']==packet['public_theorem_count'];names+=decls;sources.append({'canonical':ref(canonical),'original':packet['original_tmp_source'],'entire_source':text,'public_theorem_names':decls})
 assert len(row['actual_pair'])==2 and {r['kind']for r in row['actual_pair']}=={'standalone','named'}
 for r in row['actual_pair']:
  assert r in pairs['actual_paired_records']and r['source']=={'file':f,'sha256':row['sha256']}and type(r['actual_exit_code'])is int and r['actual_exit_code']==0
  d=J(checked(r['actual_record']));zero(d);expected=['lake','env','lean','SafeLearning/'+canonical.name]if r['kind']=='standalone'else['lake','build','SafeLearning.'+canonical.stem];assert d['command']==expected and d['actual_workdir']==str(R/'verification/lean')and d['source']==f and d['source_unchanged']is True and d['source_sha256_before']==d['source_sha256_after']==row['sha256'];assert r['raw_log']=={'file':d['log'],'sha256':d['log_sha256']};checked(r['raw_log']);assert checked(r['source_snapshot']).read_bytes()==canonical.read_bytes();commands.append({'kind':r['kind'],'native_record':r['actual_record'],'entire_native_actual_body_time_and_log':d,'raw_log':r['raw_log']})
 for e,h in row['evidence_sha256'].items():checked({'file':e,'sha256':h})
assert len(names)==len(set(names))==43 and len(commands)==6
A=R/'reports/full-coverage/foundations27-current55-canonical-binding-execution-v1.json';actual=J(checked(ref(A)));zero(actual);assert actual['actual_command']==['python3','book/coverage/checks/root_finalize_foundations27_current55_v1.py','--apply']and actual['actual_workdir']==str(R);assert actual['helper_sha256_before']==actual['helper_sha256_after']=={'book/coverage/checks/root_finalize_foundations27_current55_v1.py':'eefc6488a65b9ce326488e909ae09ec80ca69b33b9feac96792b1ae8a37bc24b'};checked({'file':actual['log'],'sha256':actual['log_sha256']});checked({'file':'book/coverage/checks/root_finalize_foundations27_current55_v1.py','sha256':'eefc6488a65b9ce326488e909ae09ec80ca69b33b9feac96792b1ae8a37bc24b'})
assert H(R/'book/coverage/inventory.json')==offer['current_inventory_sha256']=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
for f,h in pairs['protected_input_sha256'].items():checked({'file':f,'sha256':h})
for s in pairs['sources']:checked({'file':s['canonical_source'],'sha256':s['source']['sha256']})
assert len(pairs['sources'])==8;selection=J(R/'reports/full-coverage/checkpoint-26-selection.json');assert len(selection['proof_files'])==1167
for f,row in selection['proof_files'].items():assert H(R/f)==row['sha256']
for f,h in J(checked(prior['readiness']))['preserved_installed26_owner_sha256'].items():assert H(R/f)==h
result={'status':'passed_independent_exact_foundations27_current55_canonical_three_source43_final_mapping_mechanics','errors':[],'reviewer':'/root/applied_next; independent of Foundation author, Root finalizer and Module whole semantic reviewers','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_offer':ref(OP),'candidate':ref(C),'canonical_binding':ref(BP),'prior_draft_independent_peer':ref(P),'entire_original_draft_independent_peer_body_and_time':prior,'entire_original_three_whole_semantic_peers_body_and_time':reviews,'all_five_original_whole_claim_reasons_hypotheses_names_times_exact':True,'material_keys':[m['source_unit_key']for m in interface['material_units']],'exact_canonical_inverse_to_entire_reviewed_tmp_draft':True,'exact_composed_inverse_to_entire_installed26_foundations':True,'all119_exercises_247_old_proof_rows_nonpending_material_rows_exact':True,'all124_typed_original_byte_aliases_exact':True,'new_proof_file_count':3,'new_public_theorem_count':43,'genuine_canonical_compiler_commands':commands,'sources_exact_entire_original_bodies':sources,'actual_root_finalizer':ref(A),'entire_original_actual_finalizer_body_time':actual,'all_old1167_and_new8_canonical_sources_and_current55_assets_and_five_owners_exact':True,'closed_evidence_sha256':closed,'scope':'Independent read-only final source/name/native paired proof/evidence/mapping mechanics. All old full semantic bodies, hypotheses, reasons and times remain exact; no semantic redecision, compiler rerun, live installation, selection/aggregate/publication pass or whole parent exercise approval.'}
O=Path('/tmp/foundations27-current55-canonical-final-mapping-independent-applied-check-result-v1.json');assert not O.exists();O.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'result':ref(O),'candidate':ref(C),'actual_commands':6,'new_exports':43,'whole_material_units':5,'closed_evidence_count':len(closed)}))
