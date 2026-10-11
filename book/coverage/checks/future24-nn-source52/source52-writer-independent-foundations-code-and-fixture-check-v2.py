from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib,copy,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-nn-source52';V1=ROOT/'book/coverage/checks/root_source_batch52_v1.py';HELPER=ROOT/'book/coverage/checks/root_source_batch52_v2.py';CATALOG=BASE/'approved-source52-catalog-v1.json';OUT=BASE/'source52-writer-independent-foundations-review-v2.json'
cache={}
def H(p):
 p=Path(p);st=p.stat();signature=(st.st_mtime_ns,st.st_size,st.st_ino)
 if p not in cache or cache[p][0]!=signature:cache[p]=(signature,hashlib.sha256(p.read_bytes()).hexdigest())
 return cache[p][1]
read=lambda p:json.loads(Path(p).read_text())
def ref(p):return {'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
assert not OUT.exists()and H(V1)=='587c730171965e9564b92bb612ba1b754e54bff3b762e3804f7e48512961f885'and H(HELPER)=='84fa36f2b88b7ab7ecb06a70dbc200f14d58f4c50adb88193b2c18d79fe62b1f'and H(CATALOG)=='68ad4d6cb53c99e8a5721ae88cf16d1b88a6939773b61c897cf118ab107a6f31'
c=read(CATALOG);assert len(c['pages'])==1;item=c['pages'][0];p=read(ROOT/item['proposal']);peer=read(ROOT/item['independent_review'])
assert H(ROOT/item['proposal'])==item['proposal_sha256']=='ed3048a29f91b4f68201af308429831bc094e560db99f48a8b6ffb19851ff9fe'and H(ROOT/item['independent_review'])==item['independent_review_sha256']=='06b0bf523849ccd111594222f8e816350f54fc35a0c2447287727993882155a4'
assert peer['entire_original_proposal_body_and_time']==p and peer['errors']==[]and peer['proposal_text_approved']is True and peer['whole_exercise_or_material_unit_approved']is False
assert peer['reviewer']!=p['prepared_by']and len(p['replacements'])==2
source=ROOT/p['source'];before=source.read_bytes();after=before;assert H(source)==p['source_sha256_before']
for r in p['replacements']:assert after.count(r['before'].encode())==r['count']==1;after=after.replace(r['before'].encode(),r['after'].encode(),1)
assert hashlib.sha256(after).hexdigest()==p['proposed_source_sha256_after']
rev=after
for r in reversed(p['replacements']):assert rev.count(r['after'].encode())==1;rev=rev.replace(r['after'].encode(),r['before'].encode(),1)
assert rev==before and after.count(b'\n')==before.count(b'\n')
sys.path.insert(0,str(ROOT/'book'));from validate import Document
a,b=Document(before.decode()),Document(after.decode());assert [(n.tag,n.attrs,n.line)for n in a.nodes]==[(n.tag,n.attrs,n.line)for n in b.nodes]
assert p['expected_changed_text_keys']=={'exercises':['nn-in-the-loop.html::exercise-20'],'material_source_units':['nn-in-the-loop.html::node-1260','nn-in-the-loop.html::node-1262']}
assert len(item['proof_source_sha256'])==len(c['original_proof_byte_aliases'])==3
for original,r in c['original_proof_byte_aliases'].items():assert H(Path(original))==H(ROOT/r['file'])==r['sha256']==item['proof_source_sha256'][r['file']]
ali=read(ROOT/c['original_byte_alias_catalog']['file']);assert H(ROOT/c['original_byte_alias_catalog']['file'])==c['original_byte_alias_catalog']['sha256']=='6a08c185cc062e257934cc1f560e2ec862d91c85b8b9b3a8b166f6137b730d5f'
for original,r in ali['original_absolute_path_byte_aliases'].items():assert H(Path(original))==H(ROOT/r['file'])==r['sha256']
t1,t2=ast.parse(V1.read_text()),ast.parse(HELPER.read_text())
for name in ['write','compare']:
 x=next(n for n in t1.body if isinstance(n,ast.FunctionDef)and n.name==name);y=next(n for n in t2.body if isinstance(n,ast.FunctionDef)and n.name==name);assert ast.dump(x)==ast.dump(y)
main1=next(n for n in t1.body if isinstance(n,ast.If));main2=next(n for n in t2.body if isinstance(n,ast.If));assert ast.dump(main1)==ast.dump(main2)
assert isinstance(main2.orelse[0],ast.Assert)and isinstance(main2.orelse[1],ast.Assert)
assert 'live-checkpoint-23-attempt2.json'in ast.unparse(main2.orelse[0])and'pages-checkpoint-23-attempt2.json'in ast.unparse(main2.orelse[1])
def extract(tree):
 body=[]
 for n in tree.body:
  if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id in ['H','load']for t in n.targets):body.append(n)
  if isinstance(n,ast.FunctionDef)and n.name in ['protect','compare']:body.append(n)
 ns={'R':ROOT,'CATALOG':CATALOG,'Path':Path,'json':json,'hashlib':hashlib};exec(compile(ast.Module(body=body,type_ignores=[]),str(HELPER),'exec'),ns);ns['H']=H;return ns
n1,n2=extract(t1),extract(t2)
old=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');new=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json');owners={n:new['working_inputs_sha256'][n]for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
conflicts={}
for r in old['proof_files'].values():
 for n,h in r['evidence_sha256'].items():
  actual=H(ROOT/n)
  if actual!=h:
   assert n in owners and n!='book/coverage/applied-promotions.json'and h==old['working_inputs_sha256'][n]and actual==owners[n]
   archive=ROOT/'reports/full-coverage/owner22-originals-before-owner23-integration-v1'/Path(n).name;assert H(archive)==h;conflicts[n]={'original22_sha256':h,'installed23_sha256':actual,'archive':ref(archive)}
assert len(conflicts)==4
try:n1['protect']()
except AssertionError as e:original_guard_failure=str(e);assert original_guard_failure in conflicts
else:raise AssertionError('Uncorrected original v1 guard incorrectly accepted four stale owners')
# Actual full read-only corrected protection, with independent memoized real SHA256.
actual_protection=n2['protect']();assert actual_protection['22']['selected_sources']==1113 and actual_protection['23']['selected_sources']==1131
# Pure independent dataset fixtures exercise unchanged protect logic without writes.
documents={n:read(ROOT/n)for n in ['reports/full-coverage/source51-apply-execution-v1.json','reports/full-coverage/owner23-integration-apply-execution-v1.json','reports/full-coverage/owner23-reviewed-candidate-integration-v1.json','reports/full-coverage/checkpoint-22-manifest.json','reports/full-coverage/checkpoint-23-manifest.json',str(CATALOG.relative_to(ROOT)),c['original_byte_alias_catalog']['file']]}
fn=next(iter(old['proof_files']));ph=old['proof_files'][fn]['sha256'];documents['reports/full-coverage/checkpoint-22-manifest.json']['proof_files']={fn:{'sha256':ph,'evidence_sha256':{n:r['original22_sha256']for n,r in conflicts.items()}}};documents['reports/full-coverage/checkpoint-22-manifest.json']['frozen_inputs_sha256']={}
documents['reports/full-coverage/checkpoint-23-manifest.json']['proof_files']={fn:{'sha256':ph,'evidence_sha256':{n:owners[n]for n in conflicts}}};documents['reports/full-coverage/checkpoint-23-manifest.json']['frozen_inputs_sha256']={}
def fixture(changes=None,hash_override=None):
 ds=copy.deepcopy(documents)
 if changes:changes(ds)
 n=extract(t2);n['load']=lambda p:copy.deepcopy(ds[p]);n['H']=lambda p:(hash_override or {}).get(str(Path(p)),H(p));return n['protect']()
fixture();fixtures=['accept_exact_four_historical22_archives_and_fresh23_current_raw_owner_evidence_together']
def reject(label,mutator=None,hashes=None):
 try:fixture(mutator,hashes)
 except AssertionError:fixtures.append('reject_'+label)
 else:raise AssertionError(label+' was accepted')
core='book/coverage/core.json';applied='book/coverage/applied.json';ip='reports/full-coverage/owner23-reviewed-candidate-integration-v1.json';m22='reports/full-coverage/checkpoint-22-manifest.json';m23='reports/full-coverage/checkpoint-23-manifest.json'
reject('old22_raw_expected_replaced_with_current23_digest',lambda ds:ds[m22]['proof_files'][fn]['evidence_sha256'].update({core:owners[core]}))
reject('fresh23_raw_expected_replaced_with_old22_digest',lambda ds:ds[m23]['proof_files'][fn]['evidence_sha256'].update({core:old['working_inputs_sha256'][core]}))
reject('Applied_pruned_frozen_digest_instead_of_raw_working0ee',lambda ds:ds[m22]['proof_files'][fn]['evidence_sha256'].update({applied:old['frozen_inputs_sha256'][applied]}))
reject('historical_archive_bytes_changed',hashes={str(ROOT/conflicts[core]['archive']['file']):'0'*64})
reject('unauthorized_owner_path',lambda ds:ds[ip]['exact_replacements'][0].update(destination='book/coverage/unapproved.json'))
reject('original_owner_before_digest_changed',lambda ds:ds[ip]['exact_replacements'][0].update(before_sha256='0'*64))
reject('current_raw_owner_arbitrary_new_digest',hashes={str(ROOT/core):'0'*64})
reject('current_promotions_changed',hashes={str(ROOT/'book/coverage/applied-promotions.json'):'0'*64})
reject('native_actual_integration_digest_changed',hashes={str(ROOT/ip):'0'*64})
reject('actual_apply_not_zero',lambda ds:ds['reports/full-coverage/owner23-integration-apply-execution-v1.json'].update(actual_exit_code=1))
compare=n2['compare'];a={'counts':{'e':1,'u':1},'exercises':[{'key':'e1','source':'a','source_text':'old','text_sha256':'h','source_sha256':'s','line':1}],'material_source_units':[{'key':'u1','source':'b','source_text':'unchanged','text_sha256':'j','source_sha256':'t','line':2}]};b=copy.deepcopy(a);b['exercises'][0].update(source_text='new',text_sha256='newh',source_sha256='newsource');assert compare(a,b,{'a'})=={'exercises':['e1'],'material_source_units':[]}
for label,mutate in [('counts',lambda x:x['counts'].update(e=2)),('key',lambda x:x['exercises'][0].update(key='other')),('line',lambda x:x['exercises'][0].update(line=3)),('unrelated_page_text',lambda x:x['material_source_units'][0].update(source_text='other'))]:
 x=copy.deepcopy(b);mutate(x)
 try:compare(a,x,{'a'})
 except AssertionError:fixtures.append('reject_compare_'+label)
 else:raise AssertionError(label+' was accepted')
failp=BASE/'source52-writer-independent-foundations-code-and-fixture-actual-v1.json';fail=read(failp);assert fail['actual_exit_code']==1 and H(ROOT/fail['actual_command'][1])==fail['actual_checker_sha256_before']==fail['actual_checker_sha256_after']and H(fail['raw_log'])==fail['raw_log_sha256']
report={'status':'passed_independent_source52_writer_v2_code_catalog_original_semantic_binding_and_accept_reject_guard_fixtures','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'helper_sha256':H(HELPER),'catalog':ref(CATALOG),'checker':ref(Path(__file__)),'entire_original_proposal_body_and_time_unchanged':True,'entire_original_semantic_peer_body_and_time_unchanged':True,'original_proposal':{'file':item['proposal'],'sha256':item['proposal_sha256']},'original_semantic_peer':{'file':item['independent_review'],'sha256':item['independent_review_sha256']},'original_unexecuted_helper_v1':ref(V1),'original_v1_guard_conflicts':conflicts,'actual_original_readonly_v1_protect_failure':original_guard_failure,'actual_full_readonly_v2_protection':actual_protection,'independent_accept_reject_fixtures':fixtures,'all_five_current51_owner_sha256':owners,'actual_native23_integration':ref(ROOT/ip),'exact_two_replacements_DOM_reverse_and_only_expected_key_scope':True,'apply_before_write_requires_both_actual23_delivery_attempt2_statuses':True,'original_dry_apply_and_structural_guard_AST_unchanged':True,'preserved_first_independent_checker_failure':{'entire_original_actual_body_and_time':fail,'actual':ref(failp),'reader':{'file':str(Path(fail['actual_command'][1]).relative_to(ROOT)),'sha256':fail['actual_checker_sha256_before']},'raw_log':ref(Path(fail['raw_log'])),'cause':'First reader extracted load as a function definition although original load is a lambda assignment; it correctly enumerated the four historical raw owner conflicts, then failed before evaluating protect. New reader honors the exact lambda assignment schema.'},'errors':[],'writer_main_dry_apply_executed':False,'scope':'Independent code and exact catalog/body binding. Only original read-only hash/load/protect/compare definitions evaluated with real SHA256 plus explicit pure accept/reject fixtures; no writer main/dry/apply, HTML/inventory/current owner mutation or changed-source correspondence inference. Original semantic review timestamp and decisions unchanged. Root actual dry/apply remain future distinct execution.'}
with OUT.open('x')as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':ref(OUT),'helper_sha256':H(HELPER),'fixtures':len(fixtures),'writer_executed':False}))
