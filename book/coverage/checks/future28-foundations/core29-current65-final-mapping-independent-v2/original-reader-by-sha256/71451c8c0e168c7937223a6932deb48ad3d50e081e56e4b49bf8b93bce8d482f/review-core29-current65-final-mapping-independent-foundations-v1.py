from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,importlib.util,json
R=Path('/home/oxrexkevin/SafetyBased');O='book/coverage/checks/future29-core/current65-three-source-pair-bound-v1/core29-current65-three-source-pair-bound-offer-draft-v2.json';C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':str(n),'sha256':sha(n)}
def check(q):assert sha(q['file'])==q['sha256'],q['file'];return read(q['file'])
assert sha(O)=='a1fcc9eabe3db2f6307f839cf19451659632e0fe72297023266bd737256fba50'
assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';ctx=read(C);o=read(O)
def guard():
 for k in ('pins_sha256','held_current_source_sha256','owners_sha256'):
  for n,h in ctx[k].items():assert sha(n)==h,n
 assert sha(O)=='a1fcc9eabe3db2f6307f839cf19451659632e0fe72297023266bd737256fba50'
guard();started=datetime.now(timezone.utc).isoformat()
assert o['errors']==[] and o['canonical_pair_ready'] is True and o['coverage_complete'] is False and o['live_owner_written'] is False
es=o['required_evidence_artifacts_sha256'];assert len(es)==300
for n,h in es.items():
 pp=R/n;assert not Path(n).is_absolute() and '..' not in Path(n).parts and pp.resolve().is_relative_to(R) and not pp.is_symlink() and pp.is_file(),n
 assert n not in ctx['owners_sha256'] and sha(n)==h,n
aliases=o['original_closed_byte_aliases']
for n,q in aliases.items():assert sha(q['file'])==q['sha256'] and es[q['file']]==q['sha256'],n
catalog=check(o['original_closed_byte_aliases_catalog']);assert catalog['original_closed_byte_aliases']==aliases
candidate=check(o['candidate']);base=check(o['original_entire_owner']);history=check(o['original_changed_rows_and_inverse']);identity=check(o['identity']);pending=check(o['original_pending_pair_candidate']);check(o['integrity']);check(o['original_pending_pair_offer'])
assert sha('book/coverage/core.json')==o['original_entire_owner']['sha256']
assert o['inventory_sha256']==sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction65.json')=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
inv=read('book/coverage/inventory-after-correction65.json');oldinv=read('book/coverage/inventory-after-correction60.json');scope=set(base['scope_pages'])
for section,total in [('exercises',92),('material_source_units',3982)]:
 a={x['key']:x for x in oldinv[section] if x['source'] in scope};b={x['key']:x for x in inv[section] if x['source'] in scope};assert a==b and len(a)==total
assert identity['changed_owned_literal_keys']==[] and identity['entire_equal_owned_inventory_records']=={'exercises':92,'material_source_units':3982}
assert candidate['source_sha256']==base['source_sha256']==o['source_sha256']=={n:inv['source_sha256'][n] for n in scope}
assert len(candidate['exercises'])==92 and len(candidate['material_claims'])==4219 and len(candidate['proof_files'])==185
assert candidate['counts']==o['counts'] and candidate['counts']['exercise_statuses']==dict(Counter(x['status'] for x in candidate['exercises']))=={'complete_math':90,'partial':2}
assert set(history['original_exercises'])=={'lyapunov-mpc.html::exercise-18','cmdp.html::exercise-21'} and len(history['original_material_rows'])==16 and len(history['appended_material_claim_ids'])==9 and len(history['appended_exercise_claim_ids'])==5
oldex={x['inventory_key']:x for x in base['exercises']};newex={x['inventory_key']:x for x in candidate['exercises']};oldmat={x['id']:x for x in base['material_claims']};newmat={x['id']:x for x in candidate['material_claims']}
assert set(newex)==set(oldex) and set(newmat)-set(oldmat)==set(history['appended_material_claim_ids'])
for key,e in oldex.items():
 if key not in history['original_exercises']:assert newex[key]==e,key
 oldclaims={x['id']:x for x in e['claims']};newclaims={x['id']:x for x in newex[key]['claims']}
 for cid,row in oldclaims.items():
  if row['status']!='pending':assert newclaims[cid]==row,cid
for cid,row in oldmat.items():
 if cid not in history['original_material_rows']:assert newmat[cid]==row,cid
 if row['status']!='pending':assert newmat[cid]==row,cid
reverse=copy.deepcopy(candidate)
reverse['exercises']=[copy.deepcopy(history['original_exercises'].get(e['inventory_key'],e)) for e in reverse['exercises']]
reverse['material_claims']=[copy.deepcopy(history['original_material_rows'].get(x['id'],x)) for x in reverse['material_claims'] if x['id'] not in history['appended_material_claim_ids']]
for n in history['new_planned_proof_files']:reverse['proof_files'].pop(n)
for k,v in history['original_top_level'].items():reverse[k]=copy.deepcopy(v)
reverse.pop('future29_current65_candidate_binding');assert reverse==base
assert (json.dumps(reverse,indent=2,ensure_ascii=False)+'\n').encode()==p(o['original_entire_owner']['file']).read_bytes()
# Every difference from the original pending candidate is solely its new exact
# archive pointers and actual three-source canonical-readiness binding.
unbound=copy.deepcopy(candidate)
for e in unbound['exercises']:
 for row in e['claims']:
  if row.get('original_pending_row_archive')==o['original_changed_rows_and_inverse']:row['original_pending_row_archive']=pending['future29_current65_candidate_binding']['original_changed_rows_and_exact_inverse']
for row in unbound['material_claims']:
 if row.get('original_pending_row_archive')==o['original_changed_rows_and_inverse']:row['original_pending_row_archive']=pending['future29_current65_candidate_binding']['original_changed_rows_and_exact_inverse']
unbound['future29_current65_candidate_binding']=copy.deepcopy(pending['future29_current65_candidate_binding']);assert unbound==pending
spec=importlib.util.spec_from_file_location('core29_independent_names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
public={};theorems={};allnew=set()
for n,x in o['proof_files'].items():
 assert candidate['proof_files'][n]==sha(n)==x['sha256'] and sha(x['original_tmp_source']['file'])==x['sha256']
 ds=names.declarations(p(n).read_text());ts=[d['name'] for d in ds if d['kind'] in ('theorem','lemma')]
 assert ds==x['public_declarations'] and len(ds)==x['public_declaration_count'] and ts==x['public_theorem_names']==x['mapped_named_declarations'] and len(ts)==x['theorem_count']
 public[n]=ds;theorems[n]=ts;assert not allnew.intersection(d['name'] for d in ds);allnew.update(d['name'] for d in ds)
assert len(public)==3 and len(allnew)==142 and sum(map(len,theorems.values()))==93
assert set(candidate['proof_files'])-set(base['proof_files'])==set(public)
for n,h in base['proof_files'].items():assert candidate['proof_files'][n]==h
units={x['key']:x for x in inv['material_source_units']}
for cid in set(history['original_material_rows'])|set(history['appended_material_claim_ids']):
 row=newmat[cid];u=units[row['source_unit_keys'][0]]
 for k in ('source','source_sha256','source_text','text_sha256'):assert row[k]==u[k],(cid,k)
mpc,dual,mon,editorial=[check(q) for q in o['source_correspondence_peers']]
assert all(j['errors']==[] and j['status'].startswith('passed_') for j in [mpc,dual,mon,editorial])
assert [d['inventory_key'] for d in mpc['whole_decisions']]==['lyapunov-mpc.html::exercise-18','lyapunov-mpc.html::node-1387'] and all(d['whole_unit_approved'] is True and d['missing_clauses']==[] for d in mpc['whole_decisions'])
mpcnew=[n for n in allnew if n.rsplit('.',1)[-1] in mpc['new_public_names']];assert len(mpcnew)==9
mpcrow=[x for x in newex['lyapunov-mpc.html::exercise-18']['claims'] if x['kind']=='independently_reviewed_entire_source_exercise'];assert len(mpcrow)==1;row=mpcrow[0]
assert row['original_complete_literal_review_record']==mpc['whole_decisions'][0] and row['hypotheses']==mpc['scope_limits'] and row['remaining_gaps']==[] and row['status']=='proved'
oldproved=[n for x in oldex['lyapunov-mpc.html::exercise-18']['claims'] if x['status']=='proved' for n in x['lean_declarations']]
assert set(row['lean_declarations'])==set(oldproved)|set(mpcnew)
nr=newmat['lyapunov-mpc.html::node-1387::semantic-review'];assert nr['original_complete_literal_review_record']==mpc['whole_decisions'][1] and set(nr['lean_declarations'])==set(mpcnew) and nr['hypotheses']==mpc['scope_limits']
whole=dual['whole_material_units'];assert len(whole)==1 and whole[0]['key']=='cmdp.html::node-749' and whole[0]['whole_unit_approved'] is True and whole[0]['missing_clauses']==[]
nr=newmat['cmdp.html::node-749::semantic-review'];assert nr['original_complete_literal_review_record']==whole[0] and nr['hypotheses']==whole[0]['operational_hypotheses']
assert dual['whole750_752_or_exercise21_approved'] is False and mon['whole_exercise21_or_node1141_approved'] is False and o['whole_exercise21_or_generic_stochastic_CMDP_approved'] is False
for key in ('cmdp.html::node-750','cmdp.html::node-752','cmdp.html::node-1141'):assert any(x['status']=='pending' and x['remaining_gaps'] for x in newmat.values() if x.get('source_unit_keys')==[key])
assert newex['cmdp.html::exercise-21']['status']=='partial' and any(x['status']=='pending' and x['remaining_gaps'] for x in newex['cmdp.html::exercise-21']['claims'])
components=[x for x in newmat.values() if x['id'] in history['appended_material_claim_ids']]+[x for x in newex['cmdp.html::exercise-21']['claims'] if x['id'] in history['appended_exercise_claim_ids']]
assert len(components)==14
for row in components:
 assert row['status']=='proved' and row['remaining_gaps']==[] and set(row['lean_declarations'])<=allnew
 decision=row['original_review_component']
 if 'groups' in decision:assert decision['groups']==mon['components'] and all(x['approved'] is True and x['missing_clauses']==[] for x in decision['groups'])
 else:assert decision in dual['components'] and decision['approved'] is True and decision['missing_clauses']==[] and row['hypotheses']==[decision['scope']]
eds=editorial['individual_full_literal_decisions'];assert len(eds)==13
for d in eds:
 row=newmat[d['claim_id']];assert d['entire_literal_classification_approved'] is True and d['approved_status']=='not_a_formal_claim' and row['status']=='not_a_formal_claim' and row['original_complete_literal_review_record']==d and row['lean_declarations']==[] and row['hypotheses']==[] and row['correspondence']==d['rationale'] and row['remaining_gaps']==[]
def native(d,command,cwd,status='passed'):
 codes=[d[k] for k in ('exit_code','actual_exit_code','native_exit_code') if k in d];assert codes and all(type(v) is int and v==0 for v in codes)
 cs=[d[k] for k in ('command','actual_command') if k in d];assert cs and all(type(v) is list and v==command for v in cs)
 ws=[d[k] for k in ('cwd','workdir','actual_workdir','working_directory') if k in d];assert ws and all(type(v) is str and v==cwd for v in ws)
 assert d['status']==status
def paircheck(pair):
 n=pair['source']['file'];h=pair['source']['sha256'];d=check(pair['actual_record']);assert type(pair['actual_exit_code']) is int and pair['actual_exit_code']==0 and pair['kind'] in ('standalone','named')
 cmd=['lake','env','lean',str(Path(n).relative_to('verification/lean'))] if pair['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
 native(d,cmd,str(R/'verification/lean'));assert d['source']==n and d['source_sha256_before']==d['source_sha256_after']==sha(n)==h and d['source_unchanged'] is True
 assert pair['raw_log']=={'file':d['log'],'sha256':d['log_sha256']} and sha(d['log'])==d['log_sha256'] and sha(pair['source_snapshot']['file'])==h
 return d
batches=[check(q) for q in candidate['future29_current65_candidate_binding']['actual_canonical_readiness_reports']]
for b in batches:
 assert b['status']=='passed_actual_reviewed29_canonical_standalone_and_named_pairs_unselected' and b['errors']==[] and b['actual_compiler_command_count']==len(b['actual_paired_records'])==2*b['source_count']
 for pair in b['actual_paired_records']:paircheck(pair)
assert sum(b['actual_compiler_command_count'] for b in batches)==22 and sum(b['public_theorem_count'] for b in batches)==218
for n,x in o['proof_files'].items():
 pairs=x['actual_pair'];assert len(pairs)==2 and {q['kind'] for q in pairs}=={'standalone','named'}
 for pair in pairs:
  assert pair['source']=={'file':n,'sha256':x['sha256']} and any(pair==q for b in batches for q in b['actual_paired_records']);paircheck(pair)
  for k in ('actual_record','raw_log','source_snapshot'):q=pair[k];assert x['evidence_sha256'][q['file']]==es[q['file']]==q['sha256']
assert o['actual_canonical_compiler_command_count']==6
author=check(o['actual_finalizer']);native(author,['python3','/tmp/bind-core29-current65-three-source-pairs-v1.py'],str(R),'passed_actual_core29_three_source_canonical_binding')
assert author['helper_sha256_before']==author['helper_sha256_after'] and author['protection_errors']==[]
for n,h in author['helper_sha256_before'].items():assert aliases[n]['sha256']==h and sha(aliases[n]['file'])==h
assert aliases[author['log']]['sha256']==author['log_sha256'] and sha(aliases[author['log']]['file'])==author['log_sha256']
guard()
findings={'status':'passed_independent_full_core29_current65_actual_pair_bound_final_mapping_foundations','errors':[],'reader_started_at_utc':started,'reader_finished_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':o['candidate'],'offer':ref(O),'exact_original_owner':o['original_entire_owner'],'exact_inverse_interface':o['original_changed_rows_and_inverse'],'full_forward_and_byte_inverse_verified':True,'all_previous_proved_rows_body_review_times_and_existing_proofs_exact':True,'owned_source60_to65_entire_literal_identity':[92,3982],'counts':candidate['counts'],'new_sources_public_theorems_actual_commands':[3,142,93,6],'source_correspondence_peers':o['source_correspondence_peers'],'whole_exercises':['lyapunov-mpc.html::exercise-18'],'whole_material_units':['lyapunov-mpc.html::node-1387','cmdp.html::node-749'],'individually_justified_not_formal_rows':13,'appended_precise_components':{'exercise':5,'material':9},'whole_exercise21_or_nodes750_752_1141_approved':False,'all22_root_canonical_commands_checked':True,'durable_evidence_count':len(es),'original_byte_alias_count':len(aliases),'semantic_scope':'The exact four original independent semantic/classification decisions supply literal correspondence, not integrity alone. Generic stochastic A1-A3 feasibility remains pending; the fixed-selector and projected dual components retain exact hypotheses. Classical MPC argmin measurability is not inferred; actual implemented policy measurability remains explicit. The13 editorial classifications exclude mathematical validity, research status and bibliography correctness. Original null editorial review-time pointers remain unchanged; the full exact original peer/native body and time are closed separately.','protection_errors':[],'no_new_compiler_source_owner_selection_or_publication_writes':True,'coverage_complete':False}
Path('/tmp/core29-current65-final-mapping-independent-foundations-findings-v1.json').write_text(json.dumps(findings,indent=2)+'\n')
print(json.dumps({'status':findings['status'],'candidate':o['candidate'],'offer':ref(O),'durable_evidence_count':len(es),'counts':candidate['counts'],'errors':[]}))
