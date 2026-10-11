from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future27-core/core-current55-final-v1';O=Path('/tmp/core27-current55-final-candidate-independent-modules-check-result-v2.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def read(n):return json.loads(path(n).read_bytes())
def ref(p):return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'],r;return p
def zero(d):
 c=[d[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in d];assert c and all(type(x)is int and x==0 for x in c)
cp=B/'core27-current55-eleven-component-candidate-v1.json';op=B/'core27-current55-eleven-component-offer-v1.json'
assert sha(cp)=='0bf99e01c47c7b9fa18488fdc3104c189e3977597c15f1c7e20253afad1245c0' and sha(op)=='94342fdf4455ef7e257227956b1ec55a6b3d7fed213f1b83f5aa379952d3d66f'
c=read(cp);o=read(op);assert o['candidate']==ref(cp) and o['mapped_ledger']==ref(cp)['file'] and o['mapped_ledger_sha256']==sha(cp)
ready=read(check(o['original_draft']));draft=read(check(ready['candidate']));identity=read(check(ready['identity']));old=read(check(ready['entire_original_ledger']));oldpeer=read(check(o['original_draft_mechanics_peer']))
assert oldpeer['status']=='passed' and oldpeer['errors']==[] and oldpeer['readiness']['sha256']==o['original_draft']['sha256'] and sha(check(oldpeer['readiness']))==o['original_draft']['sha256'] and oldpeer['candidate']==ready['candidate']
assert oldpeer['mechanics']['whole_candidate_inverse_restores_original_source53_core_ledger'] is True and oldpeer['canonical_pair_execution_count']==0
assert oldpeer['whole_exercise18_and_units737_739_1387_approved'] is False
assert o['inventory_sha256']==ready['current_inventory']['sha256']==sha(R/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert o['source_sha256']==c['source_sha256']==draft['source_sha256']
canon='verification/lean/SafeLearning/CompleteCoreMPCFirstSuccessor27.lean';sourcehash='09fc59984a9e53f86e8ddfa82b2bee79f163aeffd5dc173b88eb6d8fc9c8000c'
assert set(o['proof_files'])=={canon} and sha(R/canon)==sourcehash
pairs=read(check(o['canonical_original_history_packet']));pa=read(check(o['actual_canonical_pair_execution']));zero(pa)
assert pairs['status']=='passed_actual_eight_source141_canonical_standalone_and_named_pairs_unselected_future27' and pairs['errors']==[]
assert pairs['source_count']==8 and pairs['public_theorem_count']==141 and len(pairs['actual_paired_records'])==16
assert pa['actual_command']==['python3','book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py','--apply'] and pa['actual_workdir']==str(R)
assert pa['helper_sha256_before']==pa['helper_sha256_after'];check({'file':pa['log'],'sha256':pa['log_sha256']})
for n,h in pa['helper_sha256_after'].items():check({'file':n,'sha256':h})
row=next(x for x in pairs['sources'] if x['canonical_source']==canon);names=row['all_public_declarations'];assert len(names)==len(set(names))==11
assert names==o['proof_files'][canon]['public_theorem_names']==o['proof_files'][canon]['mapped_named_declarations']
assert len(re.findall(r'^theorem\s+', (R/canon).read_text(),re.M))==11
assert o['proof_files'][canon]['sha256']==sourcehash and o['proof_files'][canon]['theorem_count']==11
pr=[x for x in pairs['actual_paired_records'] if x['source']['file']==canon];assert len(pr)==2 and {x['kind'] for x in pr}=={'standalone','named'} and pr==o['proof_files'][canon]['actual_pair']
for r in pr:
 assert r['source']=={'file':canon,'sha256':sourcehash};zero(r);d=read(check(r['actual_record']));zero(d)
 assert d['source']==canon and d['source_sha256_before']==d['source_sha256_after']==sourcehash
 expected=['lake','env','lean','SafeLearning/CompleteCoreMPCFirstSuccessor27.lean'] if r['kind']=='standalone' else ['lake','build','SafeLearning.CompleteCoreMPCFirstSuccessor27']
 assert d['command']==expected and d['actual_workdir']==str(R/'verification/lean')
 assert r['raw_log']=={'file':d['log'],'sha256':d['log_sha256']};check(r['raw_log']);check(r['source_snapshot']);assert r['source_snapshot']['sha256']==sourcehash
aliasmap=pairs['original_closed_byte_aliases']
expected=copy.deepcopy(draft);assert canon not in draft['proof_files'] and len(draft['proof_files'])==181
expected['proof_files'][canon]=sourcehash;expected['counts']['proof_files']=182;changed=[]
for item in expected['material_claims']+[x for e in expected['exercises'] for x in e['claims']]:
 if 'core27-mpc-precise-component-' in item['id']:
  r=item['independent_review'];a=aliasmap[r['source']+'::'+r['sha256']];assert a['original_file']==r['source'] and a['original_sha256']==r['sha256'];check({'file':a['file'],'sha256':a['sha256']});item['independent_review']={**r,'source':a['file']};changed.append(item)
assert len(changed)==44
expected['future27_component_pair_binding']={'paired_readiness':o['canonical_original_history_packet'],'actual_execution':o['actual_canonical_pair_execution'],'new_source':{'file':canon,'sha256':sourcehash},'public_theorem_count':11,'whole_MPC_exercise_and_certificate_pending':True}
assert c==expected and c['generated_at_utc']==draft['generated_at_utc']==old['generated_at_utc']
inverse=copy.deepcopy(c);inverse.pop('future27_component_pair_binding');inverse['proof_files']=copy.deepcopy(draft['proof_files']);inverse['counts']['proof_files']=draft['counts']['proof_files']
for rows,orows in [(inverse['material_claims'],draft['material_claims'])]+[(a['claims'],b['claims']) for a,b in zip(inverse['exercises'],draft['exercises'])]:
 for a,b in zip(rows,orows):
  if 'core27-mpc-precise-component-' in a['id']:a['independent_review']=copy.deepcopy(b['independent_review'])
assert inverse==draft
for r in reversed(identity['exact_field_changes']):
 target=inverse
 for k in r['path'][:-1]:target=target[k]
 k=r['path'][-1]
 if r.get('operation')=='append':assert target[k][r['original_length']:]==r['appended'];target[k]=target[k][:r['original_length']]
 else:
  assert target[k]==r['after']
  if r['before_present']:target[k]=copy.deepcopy(r['before'])
  else:del target[k]
assert inverse==old==read('book/coverage/core.json')
assert len(c['exercises'])==92 and [e['status'] for e in c['exercises']]==[e['status'] for e in old['exercises']]
assert next(e for e in c['exercises'] if e['inventory_key']=='lyapunov-mpc.html::exercise-18')['status']=='partial'
for key in ['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739','lyapunov-mpc.html::node-1387']:assert any(key in r['source_unit_keys'] and r['status']=='pending' for r in c['material_claims'])
assert o['new_material_component_rows']==33 and o['new_components']==11 and o['whole_exercise18_and_material737_739_1387_pending'] is True and o['coverage_complete'] is False
for a,b in zip(o['original_full_component_peers'],ready['original_full_component_peers']):
 q=read(check(a));assert q==b['entire_original_body_and_time'];assert a['original_review_status']==q['status'] and a['original_review_time']==q['reviewed_at_utc']
assert len(o['original_byte_aliases'])==18
for original,r in o['original_byte_aliases'].items():assert sha(path(original))==r['sha256'];check(r)
assert len(oldpeer['closed_evidence_sha256'])==13
for n,h in oldpeer['closed_evidence_sha256'].items():assert o['original_byte_aliases'][n]['sha256']==h
for n,h in o['proof_files'][canon]['evidence_sha256'].items():check({'file':n,'sha256':h})
actualp=R/'reports/full-coverage/core27-current55-canonical-binding-execution-v1.json';actual=read(actualp);zero(actual)
helper=check(o['prepared_by']);assert actual['helper_sha256_before']==actual['helper_sha256_after']=={o['prepared_by']['file']:o['prepared_by']['sha256']}
assert actual['actual_command'][0:2]==['python3',o['prepared_by']['file']] and actual['actual_command'][2]=='--draft-peer' and actual['actual_command'][4]=='--draft-peer-sha256' and actual['actual_command'][5]==o['original_draft_mechanics_peer']['sha256']
assert sha(path(actual['actual_command'][3]))==o['original_draft_mechanics_peer']['sha256'] and actual['actual_workdir']==str(R);check({'file':actual['log'],'sha256':actual['log_sha256']})
sel=read('reports/full-coverage/checkpoint-26-selection.json');assert len(sel['proof_files'])==1167
protected={n:r['sha256'] for n,r in sel['proof_files'].items()}
assets={n:h for n,h in read('reports/full-coverage/checkpoint-26-manifest.json')['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for application in read('reports/full-coverage/source54-55-corrections-application-v1.json')['applications']:assets[application['source_after']['file']]=application['source_after']['sha256']
protected.update(assets)
owners={'core':'1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38','foundations':'60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a','applied':'a0e087260288c8e8abc45eb0806eb3b09d17da463f5e918966c3a0686f3976a6','applied-promotions':'fa58595aacac0b82f9cd9d3bfe41718365113a2ebf76879001edcf3ab4b68fcb','modules':'c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231'}
for n,h in owners.items():protected['book/coverage/'+n+'.json']=h
protected['book/coverage/inventory.json']=o['inventory_sha256']
for r in pairs['sources']:protected[r['canonical_source']]=r['source']['sha256']
for n,h in protected.items():check({'file':n,'sha256':h})
closed={ref(cp)['file']:sha(cp),ref(op)['file']:sha(op),ref(helper)['file']:sha(helper),ref(actualp)['file']:sha(actualp),actual['log']:actual['log_sha256']}
closed.update(o['proof_files'][canon]['evidence_sha256'])
failure_path=Path('/tmp/core27-current55-final-candidate-independent-modules-actual-v1.json');failure=read(failure_path);assert type(failure['actual_exit_code']) is int and failure['actual_exit_code']==1 and sha(path(failure['raw_log']))==failure['raw_log_sha256']
for p in [failure_path,path(failure['raw_log']),path(failure['checker']['file']),path(failure['actual_runner']['file'])]:closed[str(p)]=sha(p)
result={'preserved_original_reader1_failure':failure,'reader_delta':'Readiness alias compares exact original digest/bytes rather than requiring the historical absolute path equal its new canonical bytealias; all producer paths and bodies unchanged. Also pins known installed26 owner hashes explicitly.','status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Modules agent; Root authored finalizer','candidate':ref(cp),'reviewed_offer':ref(op),'actual_candidate_preparation':ref(actualp),'actual_candidate_preparer':ref(helper),'original_draft':o['original_draft'],'original_draft_mechanics_peer':o['original_draft_mechanics_peer'],'entire_original_draft_mechanics_peer_body_and_time':oldpeer,'new_sources':1,'new_public_exports':11,'genuine_actual_canonical_records':2,'new_precise_exercise_components':11,'new_material_component_rows':33,'all92_exercise_statuses_and181_old_proof_metadata_exact':True,'candidate_inverse_recovers_entire_draft_then_installed26_exact':True,'all44_new_claim_bodies_hypotheses_reasons_and_original_times_exact_except_explicit_canonical_review_aliases':True,'all18_original_draft_peer_aliases_and13_original_reader_histories_exact':True,'all1167_selected31_current55_assets_fiveowners_eight_new_sources_exact':True,'whole_exercise18_or_certificate_approved':False,'new_semantic_decision_or_retiming':False,'owner_installation_or_global_claim':False,'closed_evidence_sha256':closed,'scope':'Independent read-only final actual-pair/mapping mechanics; exact full candidate inverses and original semantic bodies/time preserved. No fresh mathematics, owner install, aggregate or selection claim.'}
with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','result':ref(O),'new_sources':1,'new_public_exports':11}))
