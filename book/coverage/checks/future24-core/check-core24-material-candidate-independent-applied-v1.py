from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,re,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def read(n):return json.loads(P(n).read_text())
def ref(n):p=P(n);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':H(p)}
oldname='book/coverage/core.json';old=read(oldname);assert H(P(oldname))=='1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a'
cname='book/coverage/checks/future24-core/core24-source51-material-candidate-v1.json';candidate=read(cname)
reportname='book/coverage/checks/future24-core/core24-source51-material-candidate-integrity-v1.json';integrity=read(reportname)
assert integrity['candidate']==ref(cname) and integrity['original_owner']==ref(oldname)
invname='book/coverage/inventory.json';inv=read(invname);assert H(P(invname))=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
units={z['key']:z for z in inv['material_source_units']}
readyname='book/coverage/checks/future24-core/barrier-intro/root-barrier-intro24-canonical-readiness-v1.json';ready=read(readyname);assert integrity['canonical_readiness']==ref(readyname)
src=ready['source']['file'];digest=ready['source']['sha256'];assert src=='verification/lean/SafeLearning/CompleteBarrierIntroMaterial24.lean'
assert digest=='600e2c860622dcb5f132453deb00a4025d5ec2fd27033cfd42e412fe72604c89' and H(P(src))==digest
assert H(P(ready['source_snapshot']['file']))==ready['source_snapshot']['sha256']==digest
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
names=[n['name'] for n in declarations(P(src).read_text()) if n['kind'] in ['theorem','lemma']];assert len(names)==4
actualpairs=[]
for pair in ready['actual_canonical_pair']:
 assert H(P(pair['file']))==pair['sha256'];a=read(pair['file'])
 assert a['exit_code']==0 and a['source']==src and a['source_unchanged']
 assert a['source_sha256_before']==a['source_sha256_after']==digest
 assert a['actual_workdir']==str(ROOT/'verification/lean') and a['elapsed_seconds']>=0
 assert a['command']==(['lake','env','lean','SafeLearning/CompleteBarrierIntroMaterial24.lean'] if pair['file'].endswith('-standalone.json') else ['lake','build','SafeLearning.CompleteBarrierIntroMaterial24'])
 assert H(P(a['log']))==a['log_sha256']==pair['log']['sha256'];actualpairs.append({'record':ref(pair['file']),'actual_exit_code':0,'log':ref(a['log'])})
assert len(actualpairs)==2
archives=[]
for original,alias in ready['original_TMP_byte_copies'].items():
 assert H(P(original))==H(P(alias['file']))==alias['sha256'];archives.append(alias)
reviewrows={};original_reviews=[]
for rref in integrity['whole_source_reviews']:
 assert H(P(rref['file']))==rref['sha256'];r=read(rref['file'])
 original='/tmp/'+Path(rref['file']).name;assert P(original).read_bytes()==P(rref['file']).read_bytes()
 assert r['status']=='independent_whole_literal_source_review_passed' and r['reviewer']=='/root/applied_next'
 original_reviews.append({'reference':rref,'original_review_time':r['reviewed_at_utc'],'entire_original_review':r})
 for u in r['material_units']:
  key=u['source_unit_key'];assert key not in reviewrows and u['whole_unit_approved'] is True and u['missing_clauses']==[]
  assert u['entire_inventory_record']==units[key]
  assert H(P(units[key]['source']))==u['source_sha256']==units[key]['source_sha256']
  assert u['unit_text_sha256']==units[key]['text_sha256']==hashlib.sha256(units[key]['source_text'].encode()).hexdigest()
  assert u['material_status'] in ['proved','not_a_formal_claim']
  assert set(u['lean_declarations'])<=set(names) and (bool(u['lean_declarations'])==(u['material_status']=='proved'))
  reviewrows[key]=(u,rref,r['reviewed_at_utc'])
assert len(reviewrows)==10 and sum(z[0]['material_status']=='proved' for z in reviewrows.values())==1
assert set(integrity['whole_material_units'])==set(reviewrows)
assert len(candidate['exercises'])==len(old['exercises'])==92 and candidate['exercises']==old['exercises']
assert len(candidate['material_claims'])==len(old['material_claims'])==4147
reverse=copy.deepcopy(candidate);seen=set();changed_records=[]
for i,(a,b) in enumerate(zip(old['material_claims'],candidate['material_claims'])):
 keys=a['source_unit_keys'];key=keys[0] if len(keys)==1 else None
 if key not in reviewrows:assert a==b;continue
 assert key not in seen;seen.add(key);u,rref,time=reviewrows[key]
 assert a['status']=='pending' and b['original_source51_entire_pending_material_row']==a
 assert b['source_unit_keys']==a['source_unit_keys'] and b['statement_in_prose']==b['source_text']==units[key]['source_text']
 expected=copy.deepcopy(a);expected.update(kind='independently_reviewed_literal_material_unit',status=u['material_status'],lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_unit_reason'],remaining_gaps=[],independent_review={'source':rref['file'],'sha256':rref['sha256'],'original_review_time':time},original_complete_literal_review_record=copy.deepcopy(u),original_source51_entire_pending_material_row=copy.deepcopy(a))
 assert b==expected,key
 reverse['material_claims'][i]=a;changed_records.append({'source_unit_key':key,'status':b['status'],'exact_original_review_time':time,'original_row':a,'normalized_candidate_row':b})
assert seen==set(reviewrows)
assert src not in old['proof_files'] and candidate['proof_files'][src]==digest
assert len(old['proof_files'])==175 and len(candidate['proof_files'])==176
reverse['proof_files'].pop(src);reverse['generated_at_utc']=old['generated_at_utc']
binding=reverse.pop('future24_material_candidate_binding');assert binding['original_source51_owner']==ref(oldname) and binding['current_inventory']==ref(invname) and binding['canonical_readiness']==ref(readyname)
assert binding['whole_source_reviews']==integrity['whole_source_reviews']
assert reverse==old,'Entire inverse did not restore original Core23 body'
executionname='reports/full-coverage/root-core24-material-candidate-execution-v1.json';a=read(executionname)
assert a['actual_exit_code']==0 and a['actual_command']==['python3','book/coverage/checks/prepare_root_core24_material_candidate_v1.py'] and a['actual_workdir']==str(ROOT)
assert H(P(a['log']))==a['log_sha256']
assert a['helper_sha256_before']==a['helper_sha256_after']=={'book/coverage/checks/prepare_root_core24_material_candidate_v1.py':H(P('book/coverage/checks/prepare_root_core24_material_candidate_v1.py'))}
manifest=read('reports/full-coverage/checkpoint-23-manifest.json');assert len(manifest['proof_files'])==1131
for n,z in manifest['proof_files'].items():assert H(P(n))==z['sha256'],n
held={n:d for n,d in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/modules.json','book/coverage/applied.json','book/coverage/applied-promotions.json','book/coverage/inventory.json']}
for n,d in held.items():assert H(P(n))==d,n
out=Path('/tmp/core24-material-candidate-independent-applied-confirmation-v1.json');assert not out.exists()
out.write_text(json.dumps({'status':'passed_independent_isolated_core24_candidate_mechanics','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(cname),'candidate_integrity':ref(reportname),'builder':ref('book/coverage/checks/prepare_root_core24_material_candidate_v1.py'),'genuine_builder_execution':ref(executionname),'canonical_readiness':ref(readyname),'actual_new_compiler_pairs':actualpairs,'source':ref(src),'public_theorem_names':names,'original_semantic_reviews':original_reviews,'changed_material_rows':changed_records,'counts':{'changed_whole_units':10,'proved_whole_units':1,'nonformal_whole_units':9,'unchanged_exercises':92,'original_material_claims':4147,'unchanged_material_claims':4137,'old_proof_rows':175,'new_proof_rows':1,'new_public_theorems':4,'actual_zero_compiler_records':2,'exact_archived_originals':len(archives),'protected_selected23_sources':1131},'entire_candidate_inverse_exact_original_core23':True,'all_held_current_owner_source_hashes_exact':held,'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),'scope':'Mechanical confirmation of an isolated candidate using the two previously full-read literal semantic reviews. Their complete original bodies and review times remain unchanged. Candidate/source/compiler checks do not claim live mapping, a new aggregate24 audit or deployment. Original candidate execution exit0 is retained even though historical counts remain unchanged as intended.','errors':[],'coverage_complete':False},indent=2,ensure_ascii=False)+'\n')
print(str(out),H(out))
