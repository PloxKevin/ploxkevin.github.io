from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/foundations-owner28-approved21-scope-plan-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT))if p.is_relative_to(ROOT)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def read(p):return json.loads(Path(p).read_bytes())
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else ROOT/p;assert sha(p)==r['sha256'],str(p);return p
started=datetime.now(timezone.utc).isoformat();invp=ROOT/'book/coverage/inventory.json';corrp=ROOT/'book/coverage/material-corrections.json';ownerp=ROOT/'book/coverage/foundations.json'
assert sha(invp)=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a';assert sha(corrp)=='90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81';assert sha(ownerp)=='b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55'
inv=read(invp);oldinvp=ROOT/'book/coverage/inventory-after-correction55.json';assert sha(oldinvp)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf';oldinv=read(oldinvp);units={u['key']:u for u in inv['material_source_units']};oldunits={u['key']:u for u in oldinv['material_source_units']};owner=read(ownerp);assert len(owner['exercises'])==119 and all(r['status']=='complete_math'for r in owner['exercises'])
specs=[
('residual17','/tmp/foundations-residual17-independent-modules-full-source-review28-v1.json','04b0d3c1ad2fd92657d8561ca0ae3ed62897cc7e4b837f510eccf4ec434f37e8','/tmp/foundations-residual-weighting-identification28-trial3.json',17,'CompleteFoundationsResidualWeightingIdentification27.lean'),
('allocation19','/tmp/foundations-allocation19-eight-full-literals-independent-applied-review28-v1.json','5d50809580ccdb91cef3f9323896201a719be9c616833513773edc2f285012ac','/tmp/foundations-allocation-clearance-whole8-28-trial2.json',19,'CompleteFoundationsAllocationClearanceWholeUnits28.lean'),
('gradient_hessian15','/tmp/foundations-literal-gradient15-independent-modules-full-source-review28-v1.json','f6eb36bc6e27e4b93f365fbadfd3b877c61a3afdfe9e5c660c83b387482766d8','/tmp/foundations-literal-gradient-hessian28-trial3.json',15,'CompleteFoundationsLiteralGradientHessian28.lean'),
('partial_pitfall7','/tmp/foundations-literal-partial7-independent-applied-full-source-review28-v1.json','637035cd4581e93e3c737bdb4d463765dcf45e171b4e91654340e55379f8b20f','/tmp/foundations-literal-partial-pitfall7-28-trial3.json',7,'CompleteFoundationsLiteralPartialPitfall28.lean'),
('jacobian30','/tmp/foundations-jacobian30-independent-modules-review28-v2.json','126089d8e3223c41cd4b5d4c684609c613d01c4e5975225a05564428d066a873','/tmp/foundations-literal-jacobian30-28-trial7.json',30,'CompleteFoundationsLiteralJacobian28.lean'),
('chain_lie11','/tmp/foundations-chain-lie11-independent-applied-full-source-review28-v1.json','107609037c7adf5a8f9dfd49bef612a5699ce8e45f80cd56d02ba64d2a10f694','/tmp/foundations-literal-chain-lie11-28-trial2.json',11,'CompleteFoundationsLiteralChainLie28.lean')]
proofs=[];material=[];closed={};allnames=set()
for group,pname,pin,tname,count,dest in specs:
 p=Path(pname);assert sha(p)==pin;j=read(p);assert j['errors']==[];source=checked(j.get('proof_source',j.get('source')));s=source.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',s)
 names=[];namespace=None
 for line in s.splitlines():
  if line.startswith('namespace '):namespace=line.split()[1]
  if line.startswith('theorem '):names.append(namespace+'.'+line.split()[1])
 assert len(names)==count and len(set(names))==count and not(allnames&set(names));allnames.update(names)
 tp=Path(tname);a=read(tp);assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0 and a['actual_runner_exit_code']==0 and a['protection_errors']==[]and a['source_unchanged']is True
 assert sha(source)==a['source_sha256_before']==a['source_sha256_after']==sha(a['source_snapshot'])==a['source_snapshot_sha256'];assert sha(a['raw_log'])==a['raw_log_sha256']
 assert a['actual_command']==['lake','env','lean',str(source)]and a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['protected_selected27_proof_sources']==1175 and a['unchanged_current55_book_assets']==31 and a['unchanged_installed27_live_owners']==5
 warnings=len(re.findall(r'^.*:\d+:\d+: warning:',Path(a['raw_log']).read_text(),re.M));destination='verification/lean/SafeLearning/'+dest;assert not(ROOT/destination).exists()
 if group=='jacobian30':rows=j['individual_unit_decisions']
 else:rows=j['material_units']
 keys=[]
 for row in rows:
  key=row.get('source_unit_key',row.get('inventory_key',row.get('key')));assert key in units
  assert any(row.get(k)is True for k in ['whole_approved','whole_unit_approved','whole_source_unit_approved'])
  gaps=row.get('missing_clauses',row.get('missing',row.get('remaining_gaps')));assert gaps==[]
  assert units[key]==oldunits[key]
  if 'entire_inventory_record'in row:assert row['entire_inventory_record']==units[key]
  if 'text_sha256'in row:assert row['text_sha256']==units[key]['text_sha256']
  decls=row.get('lean_declarations',row.get('new_declarations',names));reused=row.get('selected_reused_declarations',[])
  assert all(n in names for n in decls)
  material.append({'inventory_key':key,'expected_current60_text_sha256':units[key]['text_sha256'],'expected_current60_source_sha256':units[key]['source_sha256'],'source':units[key]['source'],'proof_group':group,'whole_peer':ref(p),'original_peer_reviewed_at_utc':j['reviewed_at_utc'],'whole_literal_scope_independently_approved':True,'missing_clauses':[],'lean_declarations':decls,'selected_reused_declarations':reused,'hypotheses':row.get('hypotheses','All original literal differentiability/finite-dimensional/actual source example hypotheses; exact full Jacobian30 peer clause decisions apply.'),'correspondence':row.get('reason',row.get('correspondence','Entire literal approved in the exact independent full-source peer, including all listed clause decisions.')),'fresh_current60_literal_record_exactly_equals_original55':True,'canonical_paired_kernel_record_pending':True,'owner_candidate_or_installed_coverage_promotion_claimed':False})
  keys.append(key)
 proofs.append({'id':group,'original_tmp_proof':ref(source),'public_theorem_count':count,'public_theorem_names':names,'original_tmp_trial':ref(tp),'original_raw_log':ref(Path(a['raw_log'])),'original_source_snapshot':ref(Path(a['source_snapshot'])),'original_actual_exit_code':0,'original_started_at_utc':a['started_at_utc'],'original_finished_at_utc':a['finished_at_utc'],'original_warning_count':warnings,'whole_peer':ref(p),'original_peer_reviewed_at_utc':j['reviewed_at_utc'],'whole_literal_keys':keys,'proposed_root_canonical_destination':destination,'requires_exact_unchanged_tmp_source_bytes':True,'canonical_paired_kernel_record_pending':True,'canonical_source_installation_claimed':False})
 for q in [source,p,tp,Path(a['raw_log']),Path(a['source_snapshot'])]:closed[str(q)]=sha(q)
assert len(material)==21 and len({r['inventory_key']for r in material})==21 and sum(r['public_theorem_count']for r in proofs)==99
assert sha(invp)=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'and sha(corrp)=='90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81'and sha(ownerp)=='b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55'
for source in {r['source']for r in material}:assert sha(ROOT/source)==inv['source_sha256'][source]
d={'status':'prepared_exact_current60_approved21_scope_plan_only_not_owner_candidate_or_canonical_build','author':'/root/foundations_recovery28','started_at_utc':started,'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'current60_inventory':ref(invp),'current60_corrections':ref(corrp),'base_unmodified_installed27_current55_foundations_owner':ref(ownerp),'immutable_original55_inventory':ref(oldinvp),'exercise_scope':[],'material_scope':material,'proof_source_scope':proofs,'scope_counts':{'new_whole_exercises':0,'existing119_complete_exercises_unchanged':119,'whole_material_units':21,'new_proof_sources':6,'public_theorem_bodies_across_exact_six_sources':99},'preservation_requirements':['Retain every original pending/partial claim body and prior source/history/native failure/time by exact SHA references.','Six original passed sources and whole peers are from genuine Source55 TMP checks; do not relabel their times/context as current60 kernel checks.','Fresh current60 source55-literal identity is exact for all21 targets; independent current60 mapping/candidate review and actual canonical standalone/named pairs remain required.','Root alone copies the exact six sources and closes real canonical receipts; this plan contains no canonical build receipt or installed owner coverage.','Whole gradient/Jacobian/chain parent-body overlap remains explicit; existing selected dependency declarations are reused without counting independent proofs.'], 'closed_evidence_sha256':closed,'canonical_owner_source_selection_or_publication_mutated':False,'owner_candidate_prepared':False,'coverage_complete':False}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'scope_plan':ref(OUT),'scope_counts':d['scope_counts'],'whole_keys':[r['inventory_key']for r in material]}))
