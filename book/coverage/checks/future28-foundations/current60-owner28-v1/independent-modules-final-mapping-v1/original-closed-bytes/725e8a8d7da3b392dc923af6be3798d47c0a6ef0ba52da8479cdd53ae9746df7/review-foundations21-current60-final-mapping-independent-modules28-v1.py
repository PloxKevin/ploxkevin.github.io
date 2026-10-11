from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,re

R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/future28-foundations/current60-owner28-v1'
OFFER=B/'foundations28-current60-offer-draft-v3.json'
OUT=Path('/tmp/foundations21-current60-final-mapping-independent-modules28-reader-v1.json')
START=datetime.now(timezone.utc).isoformat()
def P(n):return Path(n) if Path(n).is_absolute() else R/n
def H(n):return hashlib.sha256(P(n).read_bytes()).hexdigest()
def J(n):return json.loads(P(n).read_bytes())
def ref(n):
 p=P(n);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':H(p),'bytes':p.stat().st_size}
def checked(v):
 assert isinstance(v,dict) and type(v['file']) is str and type(v['sha256']) is str
 assert H(v['file'])==v['sha256'],v['file']
 return P(v['file'])
def zero(v):
 keys=[k for k in ['exit_code','actual_exit_code','actual_runner_exit_code'] if k in v]
 assert keys and all(type(v[k]) is int and v[k]==0 for k in keys)
def execution(v,cmd,cwd):
 zero(v);assert v['status']=='passed'
 keys=[k for k in ['command','actual_command'] if k in v]
 assert keys and all(v[k]==cmd for k in keys)
 keys=[k for k in ['cwd','working_directory','actual_workdir'] if k in v]
 assert keys and all(v[k]==cwd for k in keys)
def declarations(n):
 names=[];namespace=''
 for line in P(n).read_text().splitlines():
  if line.startswith('namespace '):namespace=line.split()[1]
  if line.startswith('theorem '):names.append(namespace+'.'+line.split()[1])
 return names

assert H(OFFER)=='d2e2da5637cd39bbc033f09561144308e8c7b98adea87462a84eb096be69668f'
o=J(OFFER)
for k in ['candidate','exact_interface','integrity','original_installed27_ledger','actual_canonical_readiness','actual_canonical_outer_execution','inventory','actual_candidate_preparation','actual_candidate_preparation_raw_log','candidate_builder','candidate_preparation_runner','original_preparation_draft','preparation_original_byte_catalog','original_proofmetadata_draft2']:
 checked(o[k])
c,iface,old,ready=(J(checked(o[k])) for k in ['candidate','exact_interface','original_installed27_ledger','actual_canonical_readiness'])
scope=J(checked(iface['original_scope_plan']))
inv=J(checked(o['inventory']));oldinv=J('book/coverage/inventory-after-correction55.json')
assert H(o['candidate']['file'])=='269b6f6053c4fd91fa9c4346b469e190a804f41a5edb0f9d5a74319fcadf5ddf'
assert H(o['original_installed27_ledger']['file'])==H('book/coverage/foundations.json')=='b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55'
assert H('book/coverage/inventory.json')==H('book/coverage/inventory-after-correction60.json')==o['inventory_sha256']=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert ready['errors']==[] and (ready['source_count'],ready['public_theorem_count'],ready['actual_compiler_command_count'])==(10,235,20)
assert ready['coverage_complete'] is False and ready['selection_or_aggregate_or_publication_claimed'] is False
assert iface['errors']==[] and iface['coverage_complete'] is False
assert o['coverage_complete'] is False and o['aggregate28_selection_installation_or_publication_claimed'] is False
assert o['candidate_preparation_actual_pending'] is False and o['independent_final_candidate_mapping_peer_pending'] is True
assert o['source_sha256']==old['source_sha256']
assert len(old['proof_files'])==len(old['proof_sha256'])==250
for n,h in old['proof_sha256'].items():assert H(n)==h,n
for n,h in old['source_sha256'].items():assert H(n)==h,n
for section,count in [('exercises',119),('material_source_units',1756)]:
 a=[u for u in oldinv[section] if u['source'] in old['scope_pages']]
 b=[u for u in inv[section] if u['source'] in old['scope_pages']]
 assert a==b and len(a)==count
assert len(old['exercises'])==119 and all(x['status']=='complete_math' for x in old['exercises'])
mutable={'book/coverage/'+n+'.json' for n in ['core','foundations','applied','applied-promotions','modules']}
closed=o['required_evidence_artifacts_sha256']
assert len(closed)==354
for n,h in closed.items():
 assert type(n) is str and n and not Path(n).is_absolute() and '..' not in Path(n).parts and n not in mutable
 assert H(n)==h,n
alias_catalogs={}
for r in o['original_scope_history_byte_catalogs']:
 d=J(checked(r));assert closed[r['file']]==r['sha256']
 for original,a in d['original_closed_byte_aliases'].items():
  checked(a);assert closed[a['file']]==a['sha256']
  if P(original).exists():assert H(original)==a['sha256']
 alias_catalogs[r['file']]=r['sha256']
assert len(alias_catalogs)==12
original_aliases=ready['original_closed_byte_aliases']
def historical(original):
 a=original_aliases[original['file']];checked(a)
 assert a['sha256']==original['sha256']
 if P(original['file']).exists():assert H(original['file'])==a['sha256']
 return a
sources={x['canonical_source']:x for x in ready['sources']}
pairs={(x['source']['file'],x['kind']):x for x in ready['actual_paired_records']}
assert len(sources)==10 and len(pairs)==20
outer=J(checked(o['actual_canonical_outer_execution']))
execution(outer,['python3','book/coverage/checks/run_root28_current60_canonical_pairs_v2.py','--plan','/tmp/root28-current60-canonical-pair-plan-v1.json','--plan-sha256','64fe57b1296bf5d016eaf3da375a382454ea8c310c23c3421220000f0565533b','--apply'],str(R))
assert outer['helper_sha256_before']==outer['helper_sha256_after']=={'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py':'69a8eab0c5710ea143dde3c72ecf08c5c6811fa87536cec688c3fe2ea7afbe83'}
assert H(outer['log'])==outer['log_sha256']=='6e91e0b5fde820e9dd17935837f832acd245f542e185fdc2ad1bea908bc055e4'

groups={};unit_peer_decisions={};allnames=set();native_rows=[];semantic_refs=[]
def pair_check(p,n,h,native):
 assert p['source']=={'file':n,'sha256':h} and type(p['actual_exit_code']) is int and p['actual_exit_code']==0
 kind=p['kind'];assert kind in ['standalone','named']
 cmd=['lake','env','lean',str(Path(n).relative_to('verification/lean'))] if kind=='standalone' else ['lake','build','.'.join(Path(n).relative_to('verification/lean').with_suffix('').parts)]
 execution(native,cmd,str(R/'verification/lean'))
 assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==h and native['source_unchanged'] is True
 assert native['log']==p['raw_log']['file'] and native['log_sha256']==p['raw_log']['sha256']
 assert p['source_snapshot']['sha256']==h
 assert H(p['source_snapshot']['file'])==H(n)==h
 assert H(native['log'])==native['log_sha256']
for s in scope['proof_source_scope']:
 n=s['proposed_root_canonical_destination'];row=o['proof_files'][n];rs=sources[n]
 h=s['original_tmp_proof']['sha256'];assert H(n)==h==row['sha256']==rs['original_tmp_source']['sha256']
 names=declarations(n);assert names==s['public_theorem_names']==row['public_theorem_names']==row['mapped_named_declarations']==rs['public_declarations']
 assert len(names)==s['public_theorem_count']==row['theorem_count'] and not(allnames&set(names));allnames.update(names)
 assert not re.search(r'\b(sorry|admit|axiom)\b',P(n).read_text())
 expected_pair=[pairs[(n,k)] for k in ['standalone','named']]
 assert row['actual_pair']==expected_pair
 for p in expected_pair:
  native=J(checked(p['actual_record']))
  for k in ['raw_log','source_snapshot']:checked(p[k])
  pair_check(p,n,h,native);native_rows.append((p,n,h,native))
  for k in ['actual_record','raw_log','source_snapshot']:
   assert row['evidence_sha256'][p[k]['file']]==p[k]['sha256'] and closed[p[k]['file']]==p[k]['sha256']
 peerref=historical(s['whole_peer']);peer=J(checked(peerref))
 assert row['original_whole_source_peer']==peerref and row['original_peer_reviewed_at_utc']==s['original_peer_reviewed_at_utc']==peer['reviewed_at_utc']
 assert peer.get('errors',[])==[] and peer['status']==rs['expected_peer_status']
 for k in ['original_tmp_trial','original_raw_log','original_source_snapshot']:
  a=historical(s[k]);assert row['evidence_sha256'][a['file']]==a['sha256'] and closed[a['file']]==a['sha256']
 trial=J(checked(historical(s['original_tmp_trial'])));zero(trial)
 assert trial['started_at_utc']==s['original_started_at_utc'] and trial['finished_at_utc']==s['original_finished_at_utc']
 assert H(historical(s['original_source_snapshot'])['file'])==h
 material=peer.get('material_units',peer.get('individual_unit_decisions'))
 assert len(material)==len(s['whole_literal_keys'])
 for decision in material:
  k=decision.get('source_unit_key',decision.get('key',decision.get('inventory_key')))
  assert k in s['whole_literal_keys'] and k not in unit_peer_decisions
  approved=decision.get('whole_unit_approved',decision.get('whole_source_unit_approved',decision.get('whole_approved')))
  assert approved is True
  assert all(decision.get(k,[])==[] for k in ['missing','missing_clauses','remaining_gaps'])
  unit_peer_decisions[k]=(peer,decision)
 if s['id']=='jacobian30':
  assert len(peer['clause_semantic_decisions'])==12 and peer['prior_independent_definition_gap_resolved'] is True
  assert all(x['remaining_gaps']==[] and set(x['lean_declarations'])<=set(names) for x in peer['clause_semantic_decisions'])
 if s['id']=='chain_lie11':assert all(x['approved'] is True and x['missing_clauses']==[] for x in peer['component_groups'])
 groups[s['id']]=(n,peerref,peer,expected_pair)
 semantic_refs.append({'proof_source':n,'source_sha256':h,'original_full_semantic_peer':peerref,'original_reviewed_at_utc':peer['reviewed_at_utc'],'whole_keys':s['whole_literal_keys'],'public_export_count':len(names)})
assert len(groups)==6 and len(allnames)==99 and len(unit_peer_decisions)==21 and len(native_rows)==12

units={u['key']:u for u in inv['material_source_units']}
keys={m['inventory_key'] for m in scope['material_scope']};assert len(keys)==21
removed=[{'original_index':j,'claim':copy.deepcopy(x)} for j,x in enumerate(old['material_claims']) if x['status']=='pending' and keys.intersection(x['source_unit_keys'])]
affected=[{'original_index':j,'claim':copy.deepcopy(x)} for j,x in enumerate(old['material_claims']) if keys.intersection(x['source_unit_keys'])]
assert len(removed)==21 and len(affected)==31 and all(len(x['claim']['source_unit_keys'])==1 for x in removed)
assert removed==iface['removed21_pending_rows_with_original_indices'] and affected==iface['all31_original_affected_claim_rows']
assert iface['entire_21_current60_literal_records']==[units[m['inventory_key']] for m in scope['material_scope']]
new=[];scope_read=[]
for m in scope['material_scope']:
 k=m['inventory_key'];u=units[k];n,peerref,peer,pp=groups[m['proof_group']];decision=unit_peer_decisions[k][1]
 assert m['whole_literal_scope_independently_approved'] is True and m['missing_clauses']==[]
 assert u['text_sha256']==m['expected_current60_text_sha256'] and u['source_sha256']==m['expected_current60_source_sha256'] and m['source']==u['source']
 assert H(u['source'])==u['source_sha256'] and hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
 if m['proof_group']=='jacobian30':
  assert next(x for x in peer['entire_current55_inventory_literals'] if x['key']==k)==u
  assert decision['text_sha256']==u['text_sha256'] and decision['entire_literal_read'] is True
  assert m['lean_declarations']==m['new_source_declarations']==o['proof_files'][n]['public_theorem_names']
 elif m['proof_group']=='allocation19':
  assert decision['entire_inventory_record']==u and m['new_source_declarations']==decision['new_declarations']
  assert m['selected_reused_declarations']==decision['selected_reused_declarations']
  assert m['hypotheses']==decision['hypotheses'] and m['correspondence']==decision['reason']
 else:
  assert decision['entire_inventory_record']==u and m['lean_declarations']==decision['lean_declarations'] and m['hypotheses']==decision['hypotheses']
  if m['proof_group']!='chain_lie11':assert m['correspondence']==decision['reason']
 assert set(m['new_source_declarations'])<=set(o['proof_files'][n]['public_theorem_names'])
 assert set(m['selected_reused_declarations'])==set(m['selected_reused_declaration_source_refs'])
 for d,r in m['selected_reused_declaration_source_refs'].items():
  text=checked(r).read_text();assert r['file'] in old['proof_files'] and old['proof_sha256'][r['file']]==r['sha256']
  assert re.search(r'(?m)^theorem '+re.escape(d.split('.')[-1])+r'\b',text) and d.rsplit('.',1)[0] in text
 pairdict={'standalone':pp[0],'named':pp[1],'outer_execution':o['actual_canonical_outer_execution'],'readiness':o['actual_canonical_readiness']}
 new.append({'source_unit_keys':[k],'source':u['source'],'locator':u['locator'],'source_text':u['source_text'],'source_text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'id':k+'::independently-reviewed28-whole-literal','statement_in_prose':u['source_text'],'kind':'independently_reviewed_whole_material_unit','lean_declarations':m['lean_declarations'],'status':'proved','hypotheses':m['hypotheses'],'correspondence':m['correspondence'],'remaining_gaps':[],'source_review':dict(peerref,reviewed_at_utc=m['original_peer_reviewed_at_utc'],scope='Original entire literal full-source semantic approval, exact Source55 body/time; entire current60 literal record unchanged. Actual current60 canonical compiler pair is separate.'),'actual_current60_canonical_pair':pairdict,'new_source_declarations':m['new_source_declarations'],'selected_reused_declarations':m['selected_reused_declarations'],'whole_literal_scope_independently_approved':True})
 scope_read.append({'inventory_key':k,'entire_literal':u['source_text'],'text_sha256':u['text_sha256'],'hypotheses':m['hypotheses'],'correspondence':m['correspondence'],'original_semantic_peer':peerref,'original_semantic_time':m['original_peer_reviewed_at_utc'],'all_mapped_declarations_preserved':True,'whole_mapping_approved':True})
assert new==iface['new21_whole_claim_rows']
for gid,(n,_,_,_) in groups.items():
 assert set(d for m in scope['material_scope'] if m['proof_group']==gid for d in m['new_source_declarations'])==set(o['proof_files'][n]['public_theorem_names'])

expected=copy.deepcopy(old)
expected['material_claims']=[x for j,x in enumerate(old['material_claims']) if j not in {x['original_index'] for x in removed}]+new
expected['proof_files']=old['proof_files']+list(o['proof_files'])
expected['proof_sha256']=dict(old['proof_sha256'],**{n:x['sha256'] for n,x in o['proof_files'].items()})
expected['counts']=copy.deepcopy(old['counts']);expected['counts']['material_claim_statuses']=dict(Counter(x['status'] for x in expected['material_claims']))
expected['current60_owner_identity']={'inventory':o['inventory'],'original_installed27_source55_ledger':o['original_installed27_ledger'],'all1756_entire_owned_material_records_equal55_to60':True,'all119_entire_owned_exercise_records_equal55_to60':True,'actual_source56_to60_application':ref('reports/full-coverage/source56-60-corrections-application-v1.json'),'scope':'Only global inventory identity changes; all three Foundation pages and all entire owned records are byte-identical. Original semantic bodies and times are retained.'}
expected['current60_owner_identity']['actual_source56_to60_application'].pop('bytes')
expected['current28_material_mapping']={'exact_interface':o['exact_interface'],'original_scope_plan':iface['original_scope_plan'],'actual_canonical_readiness':o['actual_canonical_readiness'],'actual_canonical_outer_execution':o['actual_canonical_outer_execution'],'new_proof_files':list(o['proof_files']),'new_public_exports':99,'whole_material_units':21,'actual_canonical_commands':12,'original_21_pending_rows_retained_in_exact_interface':True,'all1112_prior_proved_claims_and119_exercises_retained_exact':True,'whole_physical_pending_before':452,'whole_physical_pending_after':431,'final_independent_mapping_review_pending':True,'installed_owner_or_aggregate28_claimed':False}
def candidate_check(x):
 assert x==expected
 inverse=copy.deepcopy(x);inverse.pop('current60_owner_identity');inverse.pop('current28_material_mapping')
 inverse['proof_files']=old['proof_files'];inverse['proof_sha256']=old['proof_sha256'];inverse['counts']=old['counts'];inverse['material_claims']=inverse['material_claims'][:-21]
 for item in removed:inverse['material_claims'].insert(item['original_index'],item['claim'])
 assert inverse==old
 assert [x for x in x['material_claims'] if x['status']=='proved'][:-21]==[x for x in old['material_claims'] if x['status']=='proved']
candidate_check(c)
assert c['counts']['material_claim_statuses']==o['material_claim_counts']=={'not_a_formal_claim':524,'proved':1133,'pending':462}
assert c['counts']['exercise_statuses']==o['exercise_counts']
assert len({k for x in c['material_claims'] if x['status']=='pending' for k in x['source_unit_keys']})==o['physical_pending_unit_count']==431
prep=J(checked(o['actual_candidate_preparation']))
execution(prep,['python3','/tmp/prepare-foundations-owner28-current60-canonical-candidate-v1.py'],str(R))
assert prep['protection_errors']==[] and prep['canonical_owner_source_selection_or_publication_mutated'] is False
assert prep['helper_sha256_before']==prep['helper_sha256_after']==o['candidate_builder']['sha256']
assert prep['raw_log_sha256']==H(o['actual_candidate_preparation_raw_log']['file'])
norm=J('/tmp/foundations28-current60-offer-installer-normalization-actual-v1.json')
execution(norm,['python3','/tmp/normalize-foundations28-current60-offer-for-installer-v1.py'],str(R))
assert norm['protection_errors']==[] and norm['canonical_owner_source_selection_or_publication_mutated'] is False
assert norm['helper_sha256_before']==norm['helper_sha256_after']==H(norm['helper']['file'])
assert H(norm['raw_log'])==norm['raw_log_sha256']
d2=J(checked(o['original_proofmetadata_draft2']))
for n,row in o['proof_files'].items():
 prev=d2['proof_files'][n];back=copy.deepcopy(row);back['actual_pair']=prev['actual_pair'];back['mapped_named_declarations']=prev['mapped_named_declarations'];assert back==prev
assert o['candidate']==d2['candidate'] and o['exact_interface']==d2['exact_interface']

fixtures=[]
def reject(name,base,mutate,validate):
 d=copy.deepcopy(base);mutate(d)
 try:validate(d)
 except (AssertionError,KeyError,TypeError,ValueError,IndexError):fixtures.append({'case':name,'rejected':True});return
 raise AssertionError('fixture accepted: '+name)
reject('foreign owner historical field changes',c,lambda x:x.update(status='complete'),candidate_check)
reject('old exercise changed',c,lambda x:x['exercises'][0].update(status='pending'),candidate_check)
reject('old proved material omitted',c,lambda x:x['material_claims'].pop(0),candidate_check)
reject('old proof bytes metadata lost',c,lambda x:x['proof_sha256'].pop(next(iter(old['proof_sha256']))),candidate_check)
reject('new literal text changed',c,lambda x:x['material_claims'][-1].update(source_text='foreign'),candidate_check)
reject('new literal hypotheses omitted',c,lambda x:x['material_claims'][-1].update(hypotheses=[]),candidate_check)
reject('new declaration mapping pruned',c,lambda x:x['material_claims'][-1]['lean_declarations'].pop(),candidate_check)
reject('new full unit still pending',c,lambda x:x['material_claims'][-1].update(status='pending'),candidate_check)
reject('source review historical time relabelled',c,lambda x:x['material_claims'][-1]['source_review'].update(reviewed_at_utc='now'),candidate_check)
reject('current inventory incorrectly55',c,lambda x:x['current60_owner_identity']['inventory'].update(sha256='0'*64),candidate_check)
reject('whole exercise inferred',c,lambda x:x['current28_material_mapping'].update(whole_exercises=1),candidate_check)
reject('new proof source missing',c,lambda x:x['proof_files'].pop(),candidate_check)
p,n,h,native=native_rows[0]
for name,mutation in [
 ('bool compiler exit',lambda x:x.update(exit_code=False)),
 ('nonzero compiler exit',lambda x:x.update(exit_code=1)),
 ('wrong compiler command',lambda x:x.update(command=['true'])),
 ('wrong compiler cwd',lambda x:x.update(actual_workdir='/tmp')),
 ('wrong compiler source',lambda x:x.update(source='foreign.lean')),
 ('wrong source-after hash',lambda x:x.update(source_sha256_after='0'*64)),
 ('false unchanged source',lambda x:x.update(source_unchanged=False)),
 ('wrong raw log hash',lambda x:x.update(log_sha256='0'*64))]:
 reject(name,native,mutation,lambda x:pair_check(p,n,h,x))
reject('bool pair exit',p,lambda x:x.update(actual_exit_code=False),lambda x:pair_check(x,n,h,native))
reject('wrong pair source hash',p,lambda x:x['source'].update(sha256='0'*64),lambda x:pair_check(x,n,h,native))
reject('wrong snapshot hash',p,lambda x:x['source_snapshot'].update(sha256='0'*64),lambda x:pair_check(x,n,h,native))
assert not OUT.exists()
result={'status':'passed_independent_foundations28_current60_final_candidate_mapping','errors':[],'reviewer':'Modules independent peer','reader_started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'offer':ref(OFFER),'candidate':o['candidate'],'exact_interface':o['exact_interface'],'original_installed27_ledger':o['original_installed27_ledger'],'independent_exact_forward_mapping':True,'independent_exact_inverse_restores_entire_original_ledger':True,'all119_exercises_and1112_prior_proved_claims_exact':True,'full_current_owned_inventory_records_compared':{'exercises':119,'material_source_units':1756},'new_whole_material_units':21,'new_proof_sources':6,'new_public_declarations':99,'actual_current60_compiler_pairs_checked':12,'source_and_original_semantic_peer_refs':semantic_refs,'individual_full_literal_mapping_decisions':scope_read,'required_durable_evidence_hashes_checked':354,'original_history_catalogs_checked':12,'source_review_original_bodies_and_times_preserved':True,'author_preparation_actual':o['actual_candidate_preparation'],'author_normalization_actual_original':ref('/tmp/foundations28-current60-offer-installer-normalization-actual-v1.json'),'negative_fixtures':fixtures,'fresh_full99_mathematical_semantic_redo_claimed':False,'new_whole_exercise_approval':False,'coverage_complete':False,'canonical_owner_source_selection_or_publication_written':False,'scope':'Independent final mechanical forward/inverse and full21 literal-to-existing independent semantic decision mapping, with real current60 twelve canonical compiler records. All original full mathematical source peer bodies and times remain unchanged; no installed owner, selection, aggregate or publication closure inferred.'}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'result':ref(OUT),'negative_fixtures':len(fixtures),'new_units':21,'new_sources':6,'native_pairs':12}))
