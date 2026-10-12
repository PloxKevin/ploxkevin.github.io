from pathlib import Path
from collections import Counter
from datetime import datetime,timezone
import hashlib,json,copy,importlib.util
R=Path('/home/oxrexkevin/SafetyBased');O=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-offer-draft-v2.json';OUT=Path('/tmp/modules29-current65-final-mapping-independent-applied-findings-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def path(n):p=Path(n);return p if p.is_absolute() else R/p
def checked(q):
 assert {'file','sha256'}<=set(q)<={'file','sha256','bytes'};p=path(q['file']);assert sha(p)==q['sha256'],str(p)
 if 'bytes' in q:assert type(q['bytes']) is int and q['bytes']==p.stat().st_size
 return read(p)
def ref(p):return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
assert sha(O)=='9a65783affb34e05da2967a7169977572bf42b3f083b8a4b5e5cad2570103f21';of=read(O);c=checked(of['candidate']);base=checked(of['original_owner']);pending=checked(of['original_pending_candidate']);first=checked(of['exact_inverse_interface']);bind=checked(of['exact_pair_binding_inverse_interface']);inv=checked(of['inventory']);oldinv=read(R/'book/coverage/inventory-after-correction60.json')
assert of['inventory_sha256']==sha(R/'book/coverage/inventory.json')=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert c['scope_pages']==base['scope_pages'] and len(c['exercises'])==217 and len(c['material_claims'])==len(base['material_claims'])==5200
assert c['source_sha256']==of['source_sha256']=={n:inv['source_sha256'][n] for n in c['scope_pages']}
for n,h in c['source_sha256'].items():assert sha(R/n)==h
for n,h in c['chapter_fragment_sha256'].items():assert sha(R/n)==h
# Apply both independent inverse patch sequences, and check whole byte equality.
def reverse(data,patches):
 out=copy.deepcopy(data)
 for p in reversed(patches):
  d=out
  for k in p['path'][:-1]:d=d[k]
  if p['existed']:d[p['path'][-1]]=copy.deepcopy(p['before'])
  else:del d[p['path'][-1]]
 return out
r=reverse(c,bind['restore_patches_in_reverse_order']);assert r==pending and (json.dumps(r,indent=2,ensure_ascii=False)+'\n').encode()==path(of['original_pending_candidate']['file']).read_bytes()
r=reverse(r,first['restore_patches_in_reverse_order']);assert r==base and (json.dumps(r,indent=2,ensure_ascii=False)+'\n').encode()==path(of['original_owner']['file']).read_bytes()
assert len(first['restore_patches_in_reverse_order'])==62 and len(bind['restore_patches_in_reverse_order'])==68
assert all(c['proof_files'][n]==p for n,p in base['proof_files'].items()) and len(base['proof_files'])==500 and len(c['proof_files'])==502
assert c['declarations'][:len(base['declarations'])]==base['declarations'] and len(base['declarations'])==3412 and len(c['declarations'])==3484
expectedex={'lipsdp.html::exercise-16','lipsdp.html::exercise-19'};expectedmat={'lipsdp.html::node-'+str(n) for n in [1289,1290,1291,1292,1293,1320,1324,1326,1327,1328,1329]};assert set(of['new_exercises'])==expectedex and set(of['new_material_keys'])==expectedmat
scope=set(c['scope_pages']);changed={'exercises':set(),'material_source_units':set()}
for section,count in [('exercises',217),('material_source_units',4977)]:
 old={x['key']:copy.deepcopy(x) for x in oldinv[section] if x['source'] in scope};new={x['key']:copy.deepcopy(x) for x in inv[section] if x['source'] in scope};assert set(old)==set(new) and len(old)==count
 for key in old:
  old[key].pop('source_sha256');new[key].pop('source_sha256')
  if old[key]!=new[key]:changed[section].add(key)
assert changed=={'exercises':expectedex,'material_source_units':{'lipsdp.html::node-1293','lipsdp.html::node-1328','lipsdp.html::node-1329'}}
units={x['key']:x for x in inv['material_source_units']};exs={x['key']:x for x in inv['exercises']}
leaky=checked(of['original_full_leaky_peer']);scalar=checked(of['original_full_scalar_peer']);assert leaky['errors']==scalar['errors']==[]
assert of['original_full_leaky_peer']['sha256']=='cb9e1cf744d8acb4e2fd66ea5582545dfebcd2180555e1e573cec72692f35215' and of['original_full_scalar_peer']['sha256']=='b690a6d229fd067aa426216c9c9711ac9750fe917736eb0a2abf17f5c531a3ef'
def literal_equal(reviewed,current):
 a=copy.deepcopy(reviewed);b=copy.deepcopy(current);a.pop('source_sha256');b.pop('source_sha256');assert a==b,current['key']
literal_equal(leaky['prospective_source63_exercise']['entire_source_record'],exs['lipsdp.html::exercise-16']);assert leaky['prospective_source63_exercise']['whole_exercise_approved'] is True and leaky['prospective_source63_exercise']['missing_clauses']==[]
literal_equal(scalar['exercise']['entire_prospective_corrected65_literal'],exs['lipsdp.html::exercise-19']);assert scalar['exercise']['prospective_corrected65_whole_exercise_approved'] is True and scalar['exercise']['prospective_missing_source_claims']==[]
for d in leaky['material_units'][:4]:literal_equal(d['entire_source_record'],units[d['key']]);assert d['whole_unit_approved'] is True and d['missing_clauses']==[]
literal_equal(leaky['prospective_source63_node1293']['entire_source_record'],units['lipsdp.html::node-1293']);assert leaky['prospective_source63_node1293']['whole_unit_approved'] is True and leaky['prospective_source63_node1293']['missing_clauses']==[]
for d in scalar['material_units']:literal_equal(d['entire_prospective_corrected65_literal'],units[d['key']]);assert d['prospective_corrected65_whole_material_unit_approved'] is True and d['prospective_missing_source_claims']==[]
assert leaky['current_exercise']['whole_exercise_approved'] is False and scalar['exercise']['whole_exercise_approved'] is False
# Every earlier proved semantic row survives, apart from the two documented
# fully discharged gap lists, which do not change the old claim's proof scope.
association=checked(of['completion_associations']);assocs={x['claim_id']:x for x in association['associations']};assert len(assocs)==2
closedold=0;gapclears=[]
for old,e in zip(base['exercises'],c['exercises']):
 assert old['inventory_key']==e['inventory_key'] and len(old['claims'])==len(e['claims'])
 if e['inventory_key'] not in expectedex:assert e['status']==old['status']
 else:
  assert e['status']=='complete_math' and e['source_text_sha256']==exs[e['inventory_key']]['text_sha256'];assert e['entire_literal_closure29']['whole_exercise_approved'] is True and e['entire_literal_closure29']['remaining_gaps']==[]
  assert all(x['status']!='pending' and x['remaining_gaps']==[] for x in e['claims'])
 for oc,nc in zip(old['claims'],e['claims']):
  assert oc['id']==nc['id']
  if oc['status']=='pending':
   if e['inventory_key'] not in expectedex:assert oc==nc
   else:assert nc['status']=='proved' and nc['reviewed_owner29_transition']['canonical_pair_pending'] is False
  elif oc['id'] in assocs:
   a=assocs[oc['id']];assert a['exercise']==e['inventory_key'] and oc['remaining_gaps']==a['original_remaining_gaps'] and nc['remaining_gaps']==a['new_remaining_gaps']==[]
   restored=copy.deepcopy(nc);restored['remaining_gaps']=oc['remaining_gaps'];assert restored==oc;gapclears.append(oc['id'])
  else:assert oc==nc;closedold+=1
changedm=[];oldclosedm=0
for oc,nc in zip(base['material_claims'],c['material_claims']):
 assert oc['id']==nc['id']
 if oc==nc:
  if oc['status']!='pending':oldclosedm+=1
  continue
 assert oc['status']=='pending' and len(nc['source_unit_keys'])==1 and nc['source_unit_keys'][0] in expectedmat
 key=nc['source_unit_keys'][0];assert nc['status']=='proved' and nc['remaining_gaps']==[] and nc['statement_in_prose']==units[key]['source_text'];assert nc['reviewed_owner29_transition']['canonical_pair_pending'] is False;changedm.append(key)
assert set(changedm)==expectedmat and len(changedm)==11 and len(gapclears)==2
ready=checked(of['actual_canonical_readiness']);assert ready['actual_compiler_command_count']==20 and ready['source_count']==10 and ready['errors']==[]
spec=importlib.util.spec_from_file_location('reader_names',R/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
allnew=set();theorems=[]
for n,p in of['proof_files'].items():
 assert c['proof_files'][n]==p and sha(R/n)==p['sha256'];ds=names.declarations((R/n).read_text());th=[d['name'] for d in ds if d['kind'] in ['theorem','lemma']];allnew.update(d['name'] for d in ds);theorems+=th
 assert th==p['public_theorem_names']==p['mapped_named_declarations']==p['declarations'] and len(th)==p['theorem_count']
 originalpeer=leaky if 'Leaky' in n else scalar;assert originalpeer['proof_source']['sha256']==p['sha256']
 pair=[x for x in ready['actual_paired_records'] if x['source']['file']==n];assert p['actual_pair']==pair and len(pair)==2 and {x['kind'] for x in pair}=={'standalone','named'}
 assert p['evidence_sha256']==next(x for x in pair if x['kind']=='standalone')['actual_record']['sha256']
 for x in pair:
  rec=checked(x['actual_record']);assert rec['status']=='passed' and type(rec['exit_code']) is int and rec['exit_code']==0 and rec['source_unchanged'] is True
  assert rec['source']==n and rec['source_sha256_before']==rec['source_sha256_after']==p['sha256'] and rec['actual_workdir']==str(R/'verification/lean')
  assert rec['command']==(['lake','env','lean','SafeLearning/'+Path(n).name] if x['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem])
  assert rec['log']==x['raw_log']['file'] and rec['log_sha256']==x['raw_log']['sha256']
  for k in ['source','actual_record','raw_log','source_snapshot']:q=x[k];assert sha(R/q['file'])==q['sha256'];assert of['required_evidence_artifacts_sha256'][q['file']]==q['sha256']
assert len(allnew)==91 and len(theorems)==72 and c['declarations'][3412:]==theorems
for a in association['associations']:assert set(a['completion_support_declarations'])<=set(theorems)
for e in c['exercises']:
 if e['inventory_key'] in expectedex:
  for nc in e['claims']:
   if nc['id'] not in assocs:assert set(nc['lean_declarations'])<=allnew
for nc in c['material_claims']:
 if nc.get('reviewed_owner29_transition'):assert set(nc['lean_declarations'])<=allnew
assert dict(Counter(e['status'] for e in c['exercises']))==c['counts']['exercise_status']=={'complete_math':189,'pending':19,'partial':9}
assert dict(Counter(x['status'] for e in c['exercises'] for x in e['claims']))==c['counts']['exercise_claim_status']
assert dict(Counter(x['status'] for x in c['material_claims']))==c['counts']['material_claim_status']
assert c['counts']['new_declarations']==3484
closed=of['required_evidence_artifacts_sha256'];assert len(closed)==1352 and not set(closed)&{'book/coverage/core.json','book/coverage/modules.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/applied-promotions.json'}
for n,h in closed.items():assert not Path(n).is_absolute() and Path(n).as_posix()==n and (R/n).resolve().is_relative_to(R) and not (R/n).is_symlink() and sha(R/n)==h,n
for n,q in of['original_closed_byte_aliases'].items():assert not Path(q['file']).is_absolute() and (R/q['file']).resolve().is_relative_to(R) and sha(R/q['file'])==q['sha256'] and closed[q['file']]==q['sha256'],n
assert len(of['original_closed_byte_aliases'])==1330
# Preserve every true author attempt and native role; only attempt7 passed.
statuses=[]
for i in range(1,8):
 n='/tmp/modules29-current65-durable-pair-binding-actual-v'+str(i)+'.json';q=of['original_closed_byte_aliases'][n];d=checked(q);statuses.append(d['actual_exit_code']);assert d['protection_errors']==[]
 assert type(d['helper_sha256_before']) is str and d['helper_sha256_before']==d['helper_sha256_after']
 assert of['original_closed_byte_aliases'][d['helper']]['sha256']==d['helper_sha256_before'] and of['original_closed_byte_aliases'][d['raw_log']]['sha256']==d['raw_log_sha256']
assert statuses==[1,1,1,1,1,1,0]
# Source correspondence confirmations are scope-specific; no nearby-unit promotion.
assert next(x for x in c['material_claims'] if x['id']=='lipsdp.html::node-976::claim-review')['status']=='pending'
result={'status':'passed_independent_full_modules29_current65_two_source_actual_pair_bound_candidate_mapping','errors':[],'review_completed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':of['candidate'],'offer':ref(O),'original_owner':of['original_owner'],'source_identity':of['identity_sidecar'],'whole_exercises':sorted(expectedex),'whole_material_units':sorted(expectedmat),'full_two_original_gap_associations_approved':association['associations'],'exact_whole_inverse_sequences':{'pair_bound_to_pending_patch_count':68,'pending_to_installed28_patch_count':62,'both_entire_byte_inverse':True},'old_metadata_and_records_preserved':{'proof_rows':500,'declaration_prefix':3412,'unchanged_closed_exercise_claims':closedold,'only_documented_gap_arrays_changed':gapclears,'old_closed_material_records':oldclosedm,'total_exercises':217,'material_rows':5200,'entire_owned_exercises':217,'entire_owned_material_records':4977},'new_sources':2,'new_public_declarations':91,'new_theorem_lemma_declarations':72,'actual_canonical_commands':4,'original_author_preparation_exit_codes':statuses,'physically_root_closed_evidence_count':len(closed),'physically_root_alias_count':len(of['original_closed_byte_aliases']),'counts':c['counts'],'old_full_semantic_decisions_and_review_times_unchanged':True,'mathematical_semantic_redecision_claimed':False,'nearby_node976_or_others_approved':False,'live_owner_or_source_or_compiler_or_selection_or_publication_written':False,'coverage_complete':False}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'findings':ref(OUT),'candidate':of['candidate'],'status':result['status']}))
