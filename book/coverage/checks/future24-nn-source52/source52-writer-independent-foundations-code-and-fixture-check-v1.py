from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib,copy
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-nn-source52';HELPER=ROOT/'book/coverage/checks/root_source_batch52_v1.py';CATALOG=BASE/'approved-source52-catalog-v1.json';OUT=BASE/'source52-writer-independent-foundations-blocking-review-v1.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
def ref(p):return {'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
assert not OUT.exists()and H(HELPER)=='587c730171965e9564b92bb612ba1b754e54bff3b762e3804f7e48512961f885'and H(CATALOG)=='68ad4d6cb53c99e8a5721ae88cf16d1b88a6939773b61c897cf118ab107a6f31'
c=read(CATALOG);assert len(c['pages'])==1;item=c['pages'][0]
proposal=read(ROOT/item['proposal']);peer=read(ROOT/item['independent_review']);assert H(ROOT/item['proposal'])==item['proposal_sha256']=='ed3048a29f91b4f68201af308429831bc094e560db99f48a8b6ffb19851ff9fe'and H(ROOT/item['independent_review'])==item['independent_review_sha256']=='06b0bf523849ccd111594222f8e816350f54fc35a0c2447287727993882155a4'
assert peer['entire_original_proposal_body_and_time']==proposal and peer['errors']==[]and peer['proposal_text_approved']is True
old=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');new=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json');stale={}
for row in old['proof_files'].values():
 for n,h in row['evidence_sha256'].items():
  actual=H(ROOT/n)
  if actual!=h:
   assert n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json']
   assert h==old['working_inputs_sha256'][n]and actual==new['working_inputs_sha256'][n]
   archive=ROOT/'reports/full-coverage/owner22-originals-before-owner23-integration-v1'/Path(n).name
   assert H(archive)==h
   stale[n]={'baseline22_expected_raw_owner_sha256':h,'current23_installed_owner_sha256':actual,'exact_historical_byte_archive':ref(archive),'correct_bytes_exist_but_v1_protect_uses_current_raw_path':True}
assert len(stale)==4
assert all('book/coverage/applied-promotions.json'not in z['evidence_sha256']for m in [old,new]for z in m['proof_files'].values())
module=ast.parse(HELPER.read_text());body=[]
for node in module.body:
 if isinstance(node,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='H'for t in node.targets):body.append(node)
 if isinstance(node,ast.FunctionDef)and node.name in ['load','protect','compare']:body.append(node)
ns={'R':ROOT,'CATALOG':CATALOG,'Path':Path,'json':json,'hashlib':hashlib};exec(compile(ast.Module(body=body,type_ignores=[]),str(HELPER),'exec'),ns)
try:ns['protect']()
except AssertionError as e:
 observed=str(e);assert observed in stale
else:raise AssertionError('Original protect unexpectedly accepted stale raw owner evidence')
fixtures=[]
a={'counts':{'e':1,'u':1},'exercises':[{'key':'e1','source':'a','source_text':'old','text_sha256':'h','source_sha256':'s','line':1}],'material_source_units':[{'key':'u1','source':'b','source_text':'unchanged','text_sha256':'j','source_sha256':'t','line':2}]}
b=copy.deepcopy(a);b['exercises'][0].update(source_text='new',text_sha256='newh',source_sha256='newsource')
assert ns['compare'](a,b,{'a'})=={'exercises':['e1'],'material_source_units':[]};fixtures.append('accept_only_permitted_text_and_source_hash_identity_changes')
for label,mutate in [('counts',lambda x:x['counts'].update(e=2)),('key',lambda x:x['exercises'][0].update(key='other')),('line',lambda x:x['exercises'][0].update(line=3)),('unrelated_page_text',lambda x:x['material_source_units'][0].update(source_text='other'))]:
 x=copy.deepcopy(b);mutate(x)
 try:ns['compare'](a,x,{'a'})
 except AssertionError:fixtures.append('reject_'+label)
 else:raise AssertionError(label+' was accepted')
report={'status':'blocked_independent_source52_writer_v1_code_review_exact_four_historical_raw_owner_evidence_conflict','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'catalog':ref(CATALOG),'checker':ref(Path(__file__)),'original_semantic_proposal_and_review_bytes_unchanged':True,'exact_four_conflicts':stale,'observed_readonly_protect_assertion_failure':observed,'protect_only_execution_scope':'Only extracted original read-only protect/load/hash/compare definitions evaluated. No helper main/dry/apply branch or writer executed.','structural_compare_accept_reject_fixtures':fixtures,'additional_five_owner_guard_gap':{'unprotected_file':'book/coverage/applied-promotions.json','current51_sha256':H(ROOT/'book/coverage/applied-promotions.json'),'reason':'Neither baseline22 nor23 proof-evidence maps contain promotions. Full frozen snapshots are separately checked but do not establish unchanged current live promotions.'},'required_new_version':'Resolve only the exact four baseline22 raw owner references through manifest-working/actual-integration-authorized immutable original22 byte archives; keep all other references exact and fresh raw23 paths exact. Add explicit current five-owner hold. Preserve helper-v1 and this actual review history.','writer_execution_or_HTML_inventory_mutation':False,'coverage_complete':False}
with OUT.open('x')as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':ref(OUT),'observed_protect_failure':observed,'stale_owner_paths':sorted(stale),'writer_executed':False}))
